{-
 Copyright (C) 2012 Christopher Walker <http://gsd.uwaterloo.ca>

 Permission is hereby granted, free of charge, to any person obtaining a copy of
 this software and associated documentation files (the "Software"), to deal in
 the Software without restriction, including without limitation the rights to
 use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 of the Software, and to permit persons to whom the Software is furnished to do
 so, subject to the following conditions:

 The above copyright notice and this permission notice shall be included in all
 copies or substantial portions of the Software.

 THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 SOFTWARE.
-}

module Language.Clafer.Comments(getOptions, getFragments, getSummary, getComments) where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.List (stripPrefix)
import Language.Clafer.Front.Absclafer

type InputModel = String

getOptions :: InputModel -> String
getOptions model = case lines model of
  []    -> ""
  (s:_) -> fromMaybe "" $ stripPrefix "//# OPTIONS " s

getFragments :: InputModel -> [ Int ]
getFragments [] = []
getFragments xs = getFragments' (lines xs) 1
getFramgents' [] _ = []
getFragments' ("//# FRAGMENT":xs) ln = ln:getFragments' xs (ln + 1)
getFragments' (x:xs) ln = getFragments' xs $ ln + 1

getSummary :: InputModel -> Maybe Int
getSummary [] = Nothing
getSummary xs = getSummary' (lines xs) 1
getSummary' [] _ = Nothing
getSummary' ("//# SUMMARY":xs) ln = Just ln
getSummary' (x:xs) ln = getSummary' xs $ ln + 1

getComments :: InputModel -> Map Span String
getComments input = getComments' input 1 1
getComments' []           row col = Map.empty
getComments' ('/':'/':xs) row col = readLine ('/':'/':xs) (Pos row col)
getComments' ('/':'*':xs) row col = readBlock ('/':'*':xs) (Pos row col)
getComments' ('\n':xs)    row col = getComments' xs (row + 1) 1
getComments' (x:xs)       row col = getComments' xs row $ col + 1
readLine    xs start@(Pos row col) = let comment = takeWhile (/= '\n') xs in 
                                                   Map.insert (Span start (Pos row (col + toInteger (length comment)))) 
                                                              comment $ 
                                                              getComments' (drop (length comment + 1) xs) (row + 1) 1
readBlock   xs start@(Pos row col) = let (end@(Pos row' col'), comment, rest) = readBlock' xs row col id in
                                      Map.insert (Span start end) comment $ getComments' rest row' col'
readBlock' ('*':'/':xs) row col comment = ((Pos row $ col + 2), comment "*/", xs)
readBlock' ('\n':xs)    row col comment = readBlock' xs (row + 1) 1 (comment "\n" ++)
readBlock' (x:xs)       row col comment = readBlock' xs row (col + 1) (comment [x]++)
