import Erdos1122

open Erdos1122.Statements

/-- info: 'Erdos1122.Statements.main_of_cited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1122.Statements.main_of_cited

example : Mangerel → Ruzsa → ErdosV → Hildebrand → ErdosProblem1122 :=
  main_of_cited

/-- info: 'Erdos1122.hildebrand_implies_erdosX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1122.hildebrand_implies_erdosX
