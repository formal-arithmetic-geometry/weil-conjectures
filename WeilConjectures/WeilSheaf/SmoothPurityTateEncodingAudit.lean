module

import WeilConjectures.WeilSheaf.SmoothPurityTateEncoding
import Lean

/-! # Axiom audit for the native Tate encoding

This command only checks declarations; it creates no mathematical proof term.
-/

open Lean in
run_elab do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for root in #[
      `AlgebraicGeometry.ProEtale.purityRationalTateTrivialization,
      `AlgebraicGeometry.ProEtale.purityExtendPullbackIso_factor,
      `AlgebraicGeometry.ProEtale.CondensedRing.purityTateTwistOneTrivialization_weil,
      `AlgebraicGeometry.ProEtaleWeilSheaf.purity_tateTwistSheafCondensedIso] do
    let axioms ← collectAxioms root
    logInfo m!"{root}: {axioms}"
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
