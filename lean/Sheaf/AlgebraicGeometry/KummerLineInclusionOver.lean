module

public import Sheaf.AlgebraicGeometry.KummerLineGeometry

/-! # The punctured-line inclusion preserves the base structure
Source: blueprint Step 2 (blueprint: lem-pur-kummer-line-inclusion-over).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

/-- The punctured-line inclusion is over k.
Source: blueprint Step 2 (blueprint: lem-pur-kummer-line-inclusion-over).
Proof: the coordinate ring map k[t] -> k[t,t^-1] preserves every coefficient. -/
theorem normalizedKummerInclusion_over (k : Type u) [Field k] :
    KummerLine.inclusion k ≫ KummerLine.structureMap k false =
      KummerLine.structureMap k true := by
  sorry

end AlgebraicGeometry.Etale
