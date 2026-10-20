module

public import Mathlib.AlgebraicGeometry.Sites.Proetale

/-! Declarations of ours that lived in the upstream file `WeilConjectures.AlgebraicGeometry.ProEtale.Proetale.Basic` (moved out by the scheduled sync, tools/upstream_verbatim.py, 2026-10-20: upstream files are verbatim in live). -/

/-!
# The pro-étale site of a scheme

-/

@[expose] public section

universe u

open CategoryTheory MorphismProperty

namespace AlgebraicGeometry.Scheme

namespace ProEt

variable (X : Scheme.{u})

instance Basic_hasIsos : (precoverage X).HasIsos := by
  dsimp [precoverage]
  infer_instance

instance Basic_isStableUnderComposition : (precoverage X).IsStableUnderComposition := by
  dsimp [precoverage]
  infer_instance

instance Basic_isStableUnderBaseChange : (precoverage X).IsStableUnderBaseChange := by
  dsimp [precoverage]
  infer_instance

variable {S : Scheme.{u}}

end ProEt

end AlgebraicGeometry.Scheme
