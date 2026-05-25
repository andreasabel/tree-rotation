module Plot
  ( printScorePlot
  ) where

import Data.List (intercalate, sortOn)
import Text.Read (readMaybe)

-- | Score row extracted from the CSV file.
data ScorePoint = ScorePoint
  { pointLeafCount :: Int
    -- ^ Starting number of leaves.
  , pointScore :: Int
    -- ^ High-score found for that start size.
  }

-- | Read a CSV file of winners and print an SVG plot to standard output.
--
-- Precondition: the input file follows the CSV layout emitted by the solver.
-- Postcondition: prints a complete SVG document.
printScorePlot :: FilePath -> IO ()
printScorePlot csvPath = do
  csvContents <- readFile csvPath
  putStrLn (renderScorePlot (parseScorePoints csvContents))

-- | Parse all valid score rows from the CSV contents.
parseScorePoints :: String -> [ScorePoint]
parseScorePoints csvContents =
  sortOn pointLeafCount (foldr collectScorePoint [] (dropHeader (lines csvContents)))
  where
    collectScorePoint line points =
      case parseScorePoint line of
        Just point -> point : points
        Nothing -> points

-- | Ignore the CSV header when present.
dropHeader :: [String] -> [String]
dropHeader [] = []
dropHeader (firstLine : remainingLines)
  | take 2 firstLine == "n," = remainingLines
  | otherwise = firstLine : remainingLines

-- | Parse one CSV line into the fields needed for plotting.
parseScorePoint :: String -> Maybe ScorePoint
parseScorePoint line = do
  fields <- parseCsvLine line
  case fields of
    leafCountText : scoreText : _ -> do
      leafCount <- readMaybe leafCountText
      score <- readMaybe scoreText
      pure
        ScorePoint
          { pointLeafCount = leafCount
          , pointScore = score
          }
    _ -> Nothing

-- | Parse one CSV line, supporting quoted fields and escaped double quotes.
parseCsvLine :: String -> Maybe [String]
parseCsvLine input = go input False "" []
  where
    go [] False currentField fields =
      Just (reverse (reverse currentField : fields))
    go [] True _ _ = Nothing
    go ('"' : '"' : rest) True currentField fields =
      go rest True ('"' : currentField) fields
    go ('"' : rest) insideQuotes currentField fields =
      go rest (not insideQuotes) currentField fields
    go (',' : rest) False currentField fields =
      go rest False "" (reverse currentField : fields)
    go (character : rest) insideQuotes currentField fields =
      go rest insideQuotes (character : currentField) fields

-- | Render a complete SVG chart of the score points.
renderScorePlot :: [ScorePoint] -> String
renderScorePlot [] =
  unlines
    [ "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"800\" height=\"240\" viewBox=\"0 0 800 240\">"
    , "  <rect width=\"800\" height=\"240\" fill=\"white\"/>"
    , "  <text x=\"400\" y=\"120\" text-anchor=\"middle\" font-family=\"monospace\" font-size=\"18\">No score data available</text>"
    , "</svg>"
    ]
renderScorePlot points =
  unlines
    [ "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"800\" height=\"500\" viewBox=\"0 0 800 500\">"
    , "  <rect width=\"800\" height=\"500\" fill=\"white\"/>"
    , "  <line x1=\"70\" y1=\"430\" x2=\"760\" y2=\"430\" stroke=\"black\" stroke-width=\"2\"/>"
    , "  <line x1=\"70\" y1=\"430\" x2=\"70\" y2=\"40\" stroke=\"black\" stroke-width=\"2\"/>"
    , "  <text x=\"415\" y=\"470\" text-anchor=\"middle\" font-family=\"monospace\" font-size=\"16\">N</text>"
    , "  <text x=\"25\" y=\"235\" text-anchor=\"middle\" font-family=\"monospace\" font-size=\"16\" transform=\"rotate(-90 25 235)\">high-score</text>"
    , "  <polyline fill=\"none\" stroke=\"#005cc5\" stroke-width=\"3\" points=\"" <> polylinePoints <> "\"/>"
    , pointCircles
    , axisLabels
    , "</svg>"
    ]
  where
    xMin = minimum (map pointLeafCount points)
    xMax = maximum (map pointLeafCount points)
    yMax = max 1 (maximum (map pointScore points))

    xCoordinate value
      | xMin == xMax = 415
      | otherwise =
          70 + ((value - xMin) * 690) `div` (xMax - xMin)

    yCoordinate value = 430 - (value * 390) `div` yMax

    pointPairs =
      [ (xCoordinate (pointLeafCount point), yCoordinate (pointScore point), point)
      | point <- points
      ]

    polylinePoints =
      intercalate
        " "
        [ show x <> "," <> show y
        | (x, y, _) <- pointPairs
        ]

    pointCircles =
      unlines
        [ "  <circle cx=\"" <> show x <> "\" cy=\"" <> show y <> "\" r=\"4\" fill=\"#d73a49\"/>"
            <> "<text x=\"" <> show x <> "\" y=\"" <> show (y - 10) <> "\" text-anchor=\"middle\" font-family=\"monospace\" font-size=\"12\">"
            <> show (pointScore point)
            <> "</text>"
        | (x, y, point) <- pointPairs
        ]

    axisLabels =
      unlines
        [ renderXAxisLabel xMin
        , renderXAxisLabel xMax
        , renderYAxisLabel 0
        , renderYAxisLabel yMax
        ]

    renderXAxisLabel value =
      let x = xCoordinate value
       in "  <text x=\"" <> show x <> "\" y=\"450\" text-anchor=\"middle\" font-family=\"monospace\" font-size=\"14\">"
            <> show value
            <> "</text>"

    renderYAxisLabel value =
      let y = yCoordinate value
       in "  <text x=\"55\" y=\"" <> show (y + 5) <> "\" text-anchor=\"end\" font-family=\"monospace\" font-size=\"14\">"
            <> show value
            <> "</text>"
