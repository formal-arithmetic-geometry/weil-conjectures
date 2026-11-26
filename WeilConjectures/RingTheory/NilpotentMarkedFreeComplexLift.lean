/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRings
public import WeilConjectures.RingTheory.RingPseudoCoherent
import WeilConjectures.RingTheory.MarkedFiniteFreeLiftCompatibility
import WeilConjectures.RingTheory.UnmarkedFiniteFreeLift

/-!
# Lifting a marked finite free complex across a nilpotent quotient

For a nilpotent ideal `I` with `1 + I` consisting of units, a prescribed bounded-above finite
free model of the derived reduction of a pseudo-coherent complex lifts, together with its marking
and its upper bound.

## Implementation details

A bounded-above finite free representative `L₀` is chosen, and the inverse of the marking is
represented by a quasi-isomorphism `δ : F → L₀/IL₀`. The acyclic cone of `δ` lifts to an acyclic
bounded-above projective complex `A`; the cone inclusion lifts strictly to `f : L₀ → A`, whose
cokernel `B` reduces to `F[1]`. Then `P = B[-1]` is finite projective with free reduction, hence
free, and nilpotence keeps the bound. The marking identity comes from the explicit homotopy
`h(x, y, z) = x` on the reduced cone of `f`, which also fixes the sign.

## References

* [Stacks, Tags 0H76, 0BCB]
* [Stacks, Tag 0BCA] (the choice of `δ`)
-/

@[expose] public section

set_option autoImplicit false

universe u v w w'

open CategoryTheory

namespace DerivedCategory

/-- A prescribed bounded-above finite-free model of derived reduction lifts with its marking
and its upper bound. `L` and `ε` express derived scalar extension by its universal property,
as in derived change of rings on the one-object site. The right side of the final equality
first applies the canonical counit comparison from derived to termwise reduction, then
`Q(θ)`. Thus it says exactly `Q(θ) = α ∘ (β ⊗ᴸ R/I)` under that comparison. -/
theorem exists_marked_finiteFree_lift_of_nilpotent
    {R : Type u} [CommRing R] (I : Ideal R)
    (hnil : ∃ N : ℕ, 1 ≤ N ∧ I ^ N = 0)
    (hunits : ∀ x : I, IsUnit (1 + (x : R)))
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    [HasDerivedCategory.{w'} (ModuleCat.{max u v} (R ⧸ I))]
    (L : DerivedCategory (ModuleCat.{max u v} R) ⥤
      DerivedCategory (ModuleCat.{max u v} (R ⧸ I)))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      @Functor.mapHomotopyCategory _ _ _ _ _ _ _
        (ModuleCat.extendScalars (Ideal.Quotient.mk I))
        (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)).left_adjoint_additive
        (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (.up ℤ))]
    (K : DerivedCategory (ModuleCat.{max u v} R)) (hK : IsPseudoCoherent K)
    (F : CochainComplex (ModuleCat.{max u v} (R ⧸ I)) ℤ)
    (b : ℤ) (hFbound : F.IsStrictlyLE b)
    (hFterms : ∀ i : ℤ, Module.Free (R ⧸ I) (F.X i) ∧ Module.Finite (R ⧸ I) (F.X i))
    (α : L.obj K ≅ Q.obj F) :
    ∃ (P : CochainComplex (ModuleCat.{max u v} R) ℤ)
      (β : Q.obj P ≅ K)
      (θ : ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
        (.up ℤ)).obj P ≅ F),
      P.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free R (P.X i) ∧ Module.Finite R (P.X i)) ∧
      L.map β.hom ≫ α.hom =
        L.map ((quotientCompQhIso (ModuleCat.{max u v} R)).inv.app P) ≫
        ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
        Qh.map ((@Functor.mapHomotopyCategoryFactors _ _ _ _ _ _ _
          (ModuleCat.extendScalars (Ideal.Quotient.mk I))
          (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)).left_adjoint_additive
          (.up ℤ)).hom.app P) ≫
        (quotientCompQhIso (ModuleCat.{max u v} (R ⧸ I))).hom.app _ ≫
        Q.map θ.hom := by
  obtain ⟨P, β, θ, hbound, hfree⟩ :=
    exists_unmarked_finiteFree_lift_of_nilpotent I hnil hunits L ε K hK F b hFbound hFterms α
  exact exists_marking_compatible_finiteFree_lift I hnil hunits L ε K hK F b hFbound hFterms α
    ⟨P, β, θ, hbound, hfree⟩

end DerivedCategory
