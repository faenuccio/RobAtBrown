-- import Mathlib

def fooN : List Nat → List Nat
| [] => [1,2,3]
| _ => [1,2]

def fooSt : List Char → List String
| [] => ["vuoto"]
| _ => ["non", "vuoto"]

-- def StringListToNat :

def main : IO Unit := do
  IO.println "Input a list of strings"
  let inputlist ← IO.getStdin
  let otherlist ← inputlist.getLine
  let charlist := otherlist.trim.toList
  let outputlist := fooSt charlist
  IO.print outputlist
