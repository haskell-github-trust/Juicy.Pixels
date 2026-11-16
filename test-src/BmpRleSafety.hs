-- BmpRleSafety.hs: regression tests for the BMP RLE out-of-bounds write fix
-- (HSEC-2026-00XX / CVE pending).
--
-- Covers:
--  1. Int32 allocation-wrap header (w = 2^27, h = 64 -> product == 2^33)
--     must be rejected by the dimension gate, not crash.
--  2. A negative-offset RLE8 delta escape stream (cursor walked above the
--     buffer) must decode safely with the writes clipped.
--  2b. height = INT32_MIN must be rejected (Int32 abs wraps to itself).
--  2c. The same negative-offset escape through the 4bpp (RLE4) path.
--  3. A benign 4x4 RLE8 image must still decode correctly (no overblocking).
--  4. A benign 8x1 RLE4 image must still decode correctly (4bpp path).
--
-- Palettes are identity grayscale (entry i = RGB i i i) so decoded pixel
-- values are deterministic.
module Main where

import qualified Data.ByteString as B
import qualified Data.Vector.Storable as VS
import           Data.Bits ((.&.), shiftR)
import           Data.Int (Int32)
import           Data.Word
import           Data.List (isPrefixOf)
import           System.Exit (exitFailure, exitSuccess)
import           Codec.Picture

le16 :: Int -> [Word8]
le16 v = [ fromIntegral (v .&. 0xFF), fromIntegral ((v `shiftR` 8) .&. 0xFF) ]

le32 :: Int -> [Word8]
le32 v = [ fromIntegral (v .&. 0xFF), fromIntegral ((v `shiftR` 8) .&. 0xFF)
         , fromIntegral ((v `shiftR` 16) .&. 0xFF)
         , fromIntegral ((v `shiftR` 24) .&. 0xFF) ]

-- Identity grayscale 8bpp palette: entry i stored as B,G,R,X bytes.
grayPalette :: B.ByteString
grayPalette = B.pack $ concat
  [ [ fromIntegral i, fromIntegral i, fromIntegral i, 0 ]
  | i <- [0 .. 255 :: Int] ]

-- BITMAPINFOHEADER wrapper, BGR palette order.
bmp :: Int -> Int -> Int -> Int -> Int -> B.ByteString -> B.ByteString
       -> B.ByteString
bmp w h bpp compression clrUsed palette stream = B.pack $
  concat [ [0x42, 0x4D], le32 totalSize, le16 0, le16 0, le32 pixelOffset
         , le32 40, le32 w, le32 h, le16 1, le16 bpp, le32 compression
         , le32 (B.length stream), le32 2835, le32 2835
         , le32 clrUsed, le32 0 ]
    ++ B.unpack palette ++ B.unpack stream
  where
    totalSize = 14 + 40 + B.length palette + B.length stream
    pixelOffset = 14 + 40 + B.length palette

-- 1. Allocation-wrap header: 2^27 * 64 == 2^33 -> Int32 wraps to 0, plus a
--    delta escape (v=255) walking the cursor ~24 GB below the buffer.
wrapBmp :: B.ByteString
wrapBmp = bmp 0x08000000 64 8 1 0 grayPalette (B.pack [0x00, 0x02, 0x00, 0xFF, 0x10, 0x41, 0x00, 0x01])

-- 2. F110-style attack stream: 16x16, leading vertical delta escape
--    (00 02 00 38, y -= 16*56) pushing the cursor far above the buffer,
--    then 16 marker runs 0xC0..0xCF, then end-of-bitmap.
attackBmp :: B.ByteString
attackBmp = bmp 16 16 8 1 0 grayPalette stream
  where
    stream = B.pack $ concat
      [ [0x00, 0x02, 0x00, 0x38]
      , [0x00, 0x02, 0x00, 0x00]
      , concat [ [0x01, 0xC0 + fromIntegral i] | i <- [0 .. 15 :: Int] ]
      , [0x00, 0x01] ]

-- 2b. height = INT32_MIN: `abs` in Int32 wraps back to minBound, so the gate
--     must widen to Int64 before taking abs to reject it.
minHeightBmp :: B.ByteString
minHeightBmp = bmp 1 (fromIntegral (minBound :: Int32)) 8 1 0 grayPalette
                     (B.pack [0x00, 0x01])

-- 2c. F110-style 4bpp attack: 4x4, delta escape (00 02 00 10) pushes the
--     cursor 4*16 rows up (negative), then a two-nibble run 0x0A, then EOB.
--     Exercises both nibble writeByte calls on the clipped path.
attack4Bmp :: B.ByteString
attack4Bmp = bmp 4 4 4 2 16 palette stream
  where
    palette = B.pack $
      concat [ replicate 4 (fromIntegral (i * 17)) | i <- [0 .. 15 :: Int] ]
    stream = B.pack [0x00, 0x02, 0x00, 0x10, 0x02, 0xAA, 0x00, 0x01]

-- 3. Benign 4x4 RLE8: one 4-pixel run per row (with end-of-line codes),
--    all at index 0x41, then end-of-bitmap.
benign8Bmp :: B.ByteString
benign8Bmp = bmp 4 4 8 1 0 grayPalette stream
  where
    stream = B.pack $
      concat (replicate 3 [0x04, 0x41, 0x00, 0x00])
        ++ [0x04, 0x41, 0x00, 0x01]

-- 4. Benign 8x1 RLE4 (compression=2): 8 pixels at nibble 0x0A, then EOB.
--    Palette has only 16 entries (B,G,R,X each), scaled 17x for visibility.
benign4Bmp :: B.ByteString
benign4Bmp = bmp 8 1 4 2 16 palette stream
  where
    palette = B.pack $
      concat [ replicate 4 (fromIntegral (i * 17)) | i <- [0 .. 15 :: Int] ]
    stream = B.pack [0x08, 0xAA, 0x00, 0x01]

-- Force the full decoded image; returns (width, height, byte sum of RGBA8).
forceDecoded :: B.ByteString -> Either String (Int, Int, Int)
forceDecoded bs = case decodeBitmap bs of
  Left e -> Left e
  Right dyn ->
    let img = convertRGBA8 dyn
    in Right ( imageWidth img, imageHeight img
             , VS.foldl' (\a w -> a + fromIntegral w) (0 :: Int) (imageData img) )

main :: IO ()
main = do
  results <- sequence
    [ check "wrap header rejected" $
        case forceDecoded wrapBmp of
          Left e -> "Invalid bmp dimensions" `isPrefixOf` e
          Right _ -> False
    , check "negative-offset attack stream decodes safely" $
        case forceDecoded attackBmp of
          Right (16, 16, s) -> s == 16 * 16 * 255  -- all writes clipped -> zero-filled
          _ -> False
    , check "INT32_MIN height rejected (Int32 abs wraps)" $
        case forceDecoded minHeightBmp of
          Left e -> "Invalid bmp dimensions" `isPrefixOf` e
          Right _ -> False
    , check "4bpp negative-offset stream decodes safely" $
        case forceDecoded attack4Bmp of
          Right (4, 4, _) -> True
          _ -> False
    , check "benign 4x4 RLE8 decodes to 16 pixels of 0x41" $
        case forceDecoded benign8Bmp of
          Right (4, 4, s) -> s == 16 * (0x41 * 3 + 255)
          _ -> False
    , check "benign 8x1 RLE4 decodes to 8 pixels of 0x0A" $
        case forceDecoded benign4Bmp of
          Right (8, 1, s) -> s == 8 * (0x0A * 17 * 3 + 255)
          _ -> False
    ]
  if and results
    then putStrLn ("bmp-rle-safety: " ++ show (length results) ++ "/" ++ show (length results) ++ " pass") >> exitSuccess
    else exitFailure
  where
    check name ok = do
      putStrLn (name ++ ": " ++ (if ok then "PASS" else "FAIL"))
      return ok
