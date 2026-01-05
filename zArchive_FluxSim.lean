inductive State3x3
  | s00 | s01 | s02
  | s10 | s11 | s12
  | s20 | s21 | s22
open State3x3

-- Toy graph connectivity (neighbors)
def neighbors : State3x3 -> List State3x3
  | s00 => [s01, s10]
  | s01 => [s00, s02, s11]
  | s02 => [s01, s12]
  | s10 => [s00, s11, s20]
  | s11 => [s01, s10, s12, s21]
  | s12 => [s02, s11, s22]
  | s20 => [s10, s21]
  | s21 => [s11, s20, s22]
  | s22 => [s12, s21]

-- Simple dynamics: assign each state to a basin
def basinOf : State3x3 -> Nat
  | s00 | s01 | s10 => 1
  | s02 | s12 | s22 => 2
  | s11 | s21 | s20 => 3

-- Flux direction: nearest neighbor toward same basin (simplified)
def fluxNeighbor (s : State3x3) : State3x3 :=
  (neighbors s).find? (fun n => basinOf n = basinOf s) |>.getD s

-- Walk flux from a state until cycle or fixed point
def findCycle (start : State3x3) : List State3x3 :=
  let rec aux (visited : List State3x3) (curr : State3x3) :=
    if curr ∈ visited then visited.dropWhile (fun x => x ≠ curr) ++ [curr] else
    let next := fluxNeighbor curr
    aux (visited ++ [curr]) next
  aux [] start

-- All cycles for all states
def allCycles : List (List State3x3) :=
  [s00, s01, s02, s10, s11, s12, s20, s21, s22].map findCycle |>.filter (fun l => l.length > 1)

-- ASCII display of flux directions
def arrowOf (s : State3x3) : String :=
  match fluxNeighbor s with
  | s00 => "^"
  | s01 => ">"
  | s02 => "v"
  | s10 => "<"
  | s11 => "SE"
  | s12 => "v"
  | s20 => "NW"
  | s21 => "<"
  | s22 => "^"

-- Mark cycles with "*"
def markCycles (s : State3x3) : String :=
  if allCycles.any (fun cycle => s ∈ cycle) then "*" else arrowOf s

-- Render grid as ASCII
def renderGrid : String :=
  let rows := [[s00, s01, s02], [s10, s11, s12], [s20, s21, s22]]
  String.intercalate "\n" (rows.map (fun row => String.intercalate "  " (row.map markCycles)))

#eval renderGrid

#eval allCycles
