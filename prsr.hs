import Text.ParserCombinators.Parsec
import Text.Parsec.Char
import System.Environment
import qualified Data.List as DL

-- \def\PAX#1#2{\alwaysNoLine\AxiomC{$#1$}
-- \UnaryInfC{$#2$}\alwaysSingleLine}
--
-- \def\Judge{\downarrow}
--
-- \def\r{\rightarrow}
-- \def\ms{\r^*}
--
-- \def\MS#1#2{\langle #1 \rangle \ms \langle #2\rangle}
--
-- \def\SS#1#2{\langle #1 \rangle \rightarrow \langle #2\rangle}
--
-- \def\sm{\rightarrow^*}
-- \def\s{\rightarrow}
--
-- \def\AX#1{\AxiomC{$#1$}}
-- \def\UN#1{\UnaryInfC{$#1$}}
-- \def\BI#1{\BinaryInfC{$#1$}}
-- \def\TI#1{\TrinaryInfC{$#1$}}
--
-- \def\LL#1{\LeftLabel{\textsc{#1}}}
--
-- \def\brac#1{\langle#1\rangle}
--
-- \def\E{\mathcal{E}}
--
-- \def\T#1{\texttt{#1}}
--
-- \def\a{\sigma}
--
-- \def\skrt#1{\begin{prooftree}#1\end{prooftree}}
--
--
-- \def\ex#1#2{\brac{#1}\Judge #2}
-- \def\exsm#1#2{\brac{#1} \sm \brac{#2}}
-- \def\exs#1#2{\brac{#1} \s \brac{#2}}
--
-- \def\exb#1#2{\a \vdash #1 \s #2}
-- \def\exbs#1#2{\a \vdash #1 \sm #2}
--
-- \def\skip{\T{skip}}
-- \def\true{\T{true}}
-- \def\false{\T{false}}


-- needed defs in latex


-- extensions "case X of"



data Rep = Var String Int
  | Line (Maybe String) Int Int
    deriving (Show)

type Name = (String, String)

data Node = N Rep [Node] deriving Show


actualSpaces = many $ oneOf " \t"


brk :: Parser ()
brk = do
  try $ string "over"
  spaces

varName = many1 (letter <|> digit)

p_def :: Parser Name
p_def = do
  var <- varName
  spaces
  char '='
  spaces
  ret <- manyTill anyChar endOfLine
  spaces
  return (var, ret)


p_bar = do
  p1 <- getPosition
  v <- optionMaybe varName
  many1 (char '-')
  p2 <- getPosition
  actualSpaces
  return (Line v (sourceColumn p1) (sourceColumn p2))


p_var = do
  p <- getPosition
  name <- varName
  actualSpaces
  return (Var name (sourceColumn p))



p_line :: Parser [Rep]
p_line = do
  res <- many (try p_bar <|> p_var)
  endOfLine
  spaces
  return res


p_prog :: Parser ([Name], [[Rep]])
p_prog = do
  spaces
  names <- manyTill p_def brk
  spaces
  linez <- many p_line
  eof
  return (names, linez)

f s = case parse p_prog "" s of
  Right x -> x
  Left  y -> error (show y)


-- (b0 -> a0 -> b0) -> b0 -> [a0] -> b0


fits :: Node -> Node -> Bool
fits (N (Var _ i) _) (N (Line _ b1 b2) _) = b1 <= i && i <= b2
fits (N (Line _ b1 b2) _) (N (Var _ i) _) = b1 <= i && i <= b2
fits _ _ = False

insert :: [Node] -> Node -> [Node]
insert [] elm = [elm]
insert (N x s1 : xs) elm = if fits (N x s1) elm
  then N x (elm : s1) : xs
  else N x s1 : insert xs elm

toNodes :: [Rep] -> [Node]
toNodes = map (\x -> (N x []))

buildTree :: [[Rep]] -> Node
buildTree reps = case res of
    [x] -> x
    _   -> error "multiple roots\n"
  where
    insertAll old new = foldl insert (toNodes new) old
    res = foldl insertAll [] reps

get_Name :: [Name] -> String -> String
get_Name [] elm = error $ "missing variable " ++ elm ++ "\n"
get_Name ((n, val) : ns) elm = if n == elm then val else
  get_Name ns elm

genCode :: [Name] -> Node -> String
genCode names (N (Var x _) [N (Line y _ _) lst]) =
  DL.intercalate "\n" $ reverse output
  where
    output = print_tree : map (genCode names) lst
    print_tree =
      case length lst of
        0 -> "\\AX{ }" ++ possible_str ++ "\\UN{" ++ get_Name' x ++ "}"
        1 -> possible_str ++ "\\UN{" ++ get_Name' x ++ "}"
        2 -> possible_str ++ "\\BI{" ++ get_Name' x ++ "}"
        3 -> possible_str ++ "\\TI{" ++ get_Name' x ++ "}"
        4 -> possible_str ++ "\\QuaternaryInfC{$" ++ get_Name' x ++ "$}"
        5 -> possible_str ++ "\\QuinaryInfC{$" ++ get_Name' x++ "$}"
        _ -> error $ (show (length lst)) ++ " is too many overline args\n"
    possible_str = case y of
      Just n -> "\\LL{" ++ get_Name' n ++ "}"
      Nothing -> ""
    get_Name' = get_Name names
genCode names (N (Var x _) []) = "\\PAX{ }{" ++ get_Name names x ++ "}"
genCode _ _ = error "bad tree\n"




intr :: ([Name], [[Rep]]) -> String
intr (store, linez) = (genCode store) $ buildTree linez

main :: IO()
main = do
  args <- getArgs
  case args of
    [file] -> do
      s <- readFile file
      putStr $ intr $ f s
      putStr "\n"
    _ -> putStrLn "Wrong number of arguments"
  return ()
