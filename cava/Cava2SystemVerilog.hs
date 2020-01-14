{- Copyright 2019 The Project Oak Authors
  
   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at
  
       http://www.apache.org/licenses/LICENSE-2.0
  
   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
-}

module Cava2SystemVerilog
where

import qualified Cava

writeSystemVerilog :: Cava.CavaState -> IO ()
writeSystemVerilog netlist
  = writeFile (Cava.moduleName netlist ++ ".sv")
              (unlines (cava2SystemVerilog netlist))

cava2SystemVerilog :: Cava.CavaState -> [String]
cava2SystemVerilog (Cava.Coq_mkCavaState moduleName netNumber instances
                    inputs outputs)
  = ["module " ++ moduleName ++ "("] ++
    insertCommas (inputPorts inputs ++ outputPorts outputs) ++
    ["  );"] ++
    [""] ++
    ["  logic[0:" ++ show (netNumber-1) ++ "] net;"] ++
    [""] ++
    ["  // Wire up inputs."] ++
    map wireInput inputs ++
    ["  // Wire up outputs."] ++
    map wireOutput outputs ++
    [""] ++
    map generateInstance instances ++
    [""] ++
    ["endmodule"]

inputPorts :: [(String, Integer)] -> [String]
inputPorts = map inputPort

inputPort :: (String, Integer) -> String
inputPort (name, _) = "  input logic " ++ name

outputPorts :: [(String, Integer)] -> [String]
outputPorts = map outputPort

outputPort :: (String, Integer) -> String
outputPort (name, _) = "  output logic " ++ name

insertCommas :: [String] -> [String]
insertCommas [] = []
insertCommas [x] = [x]
insertCommas (x:y:xs) = (x ++ ",") : insertCommas (y:xs)

generateInstance :: Cava.Instance -> String
generateInstance (Cava.Coq_mkInstance name number args)
  = "  " ++ name ++ " inst" ++ show number ++ " " ++  showArgs args ++ ";"

showArgs :: [Integer] -> String
showArgs args = "(" ++ concat (insertCommas (map showArg args)) ++ ")";

showArg :: Integer -> String
showArg n = "net[" ++ show n ++ "]"

wireInput :: (String, Integer) -> String
wireInput (name, n) = "  assign net[" ++ show n ++ "] = " ++ name ++ ";"

wireOutput :: (String, Integer) -> String
wireOutput (name, n) = "  assign " ++ name ++ " = net[" ++ show n ++ "] ;"