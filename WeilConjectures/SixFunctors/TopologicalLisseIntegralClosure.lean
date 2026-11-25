/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators

/-! Lattice filtration step for topological Noetherian integral generators.

The missing argument constructs a finite stratified integral lattice filtration of a
lisse finite-coefficient module and identifies each quotient with an integral generator.

## References

* Bhatt--Scholze, Lemma 6.8.13, Proposition 6.8.14(2)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace WeilConjectures.SixFunctors

/-- A lisse finite-coefficient extension `v_! t_* L` belongs to the triangulated,
isomorphism-closed closure of the integral locally free generators. -/
theorem topological_lisse_integral_closure
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (T V : Scheme.{u}) (t : T ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion t] [IsOpenImmersion v]
    (L : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (finiteCoefficientObject T ℓ E))
    (hL : IsLocallyFree
      (condensedRingObj (Profinite.continuousMapRingObj E.1) T) L) :
    (sInf {P | integralModelGenerator X ℓ E ≤ P ∧ P.IsTriangulated ∧
      P.IsClosedUnderIsomorphisms})
      ((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.openImmersionLowerShriek (Profinite.continuousMapRingObj E.1) v).obj
          ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E.1) t).obj L))) := by
  sorry

end WeilConjectures.SixFunctors
