/-
Copyright 2026 Liam Kruer and Jensen Kohlmeyer.
-/
import PrizeSubmission
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _info) in env.constants.toList do
    if (`Bounty.Erdos944Proof).isPrefixOf name ||
       (`Erdos944Prize).isPrefixOf name || name == `Bounty.target then
      count := count + 1
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "Unexpected transitive axiom {axiomName} in {name}"
  logInfo m!"PASS: {count} proof declarations checked; every transitive axiom is one of propext, Classical.choice, Quot.sound. No sorryAx or additional axioms."

#print axioms Bounty.target
#print axioms Erdos944Prize.finite_all
#print axioms Erdos944Prize.target
#print axioms Erdos944Prize.benchmark_target
#print axioms Erdos944Prize.benchmark_type_check
#print Erdos944Prize.target
