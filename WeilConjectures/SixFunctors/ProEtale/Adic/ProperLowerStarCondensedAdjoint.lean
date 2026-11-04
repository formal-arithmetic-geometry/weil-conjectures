/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.BoundedConstructibleCondensedComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarLeftAdjoint

/-!
# The proper exceptional inverse image in the model of `ℓ`-adic sheaves

For a proper morphism `g : Z ⟶ Y` of separated schemes of finite type over an algebraic closure
`k` of a finite field, the derived direct image `Rg_*` of `ℓ`-adic sheaves restricted to bounded
constructible complexes has a right adjoint `Rg^!` which corresponds, under the comparison
`D(AdicSheaf ℓ -) ≌ D(Mod_{Λ_-})` of the two models, to the exceptional inverse image of the
condensed model, the right adjoint of
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleLowerStar`
(`AlgebraicGeometry.ProEtale.exists_adjunction_boundedConstructibleAdicRightDerivedLowerStar`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable {ℓ : ℕ} [Fact ℓ.Prime] {k₀ k : Type u} [Field k₀] [Finite k₀] [Field k] [Algebra k₀ k]
  [IsAlgClosure k₀ k] [Fact (ringChar k₀ ≠ ℓ)] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Over (Spec (CommRingCat.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]

variable (k₀ ℓ) in
/-- **The proper exceptional inverse image of `ℓ`-adic sheaves is the condensed one.** The
restriction of `Rg_*` to bounded constructible complexes of `ℓ`-adic sheaves has a right adjoint
`R'` which corresponds, under the comparison of the two models, to the right adjoint of the
condensed `Rg_*` on bounded constructible complexes. -/
theorem exists_adjunction_boundedConstructibleAdicRightDerivedLowerStar
    (hR : ∀ K, DerivedCategory.boundedConstructibleAdic ℓ Z.left K →
      DerivedCategory.boundedConstructibleAdic ℓ Y.left
        ((adicLowerStar ℓ g.left).rightDerivedFunctor.obj K)) :
    ∃ (R' : (DerivedCategory.boundedConstructibleAdic ℓ Y.left).FullSubcategory ⥤
        (DerivedCategory.boundedConstructibleAdic ℓ Z.left).FullSubcategory)
      (_ : (DerivedCategory.boundedConstructibleAdic ℓ Z.left).liftFullSubcategory
        (DerivedCategory.boundedConstructibleAdic ℓ Y.left)
        (adicLowerStar ℓ g.left).rightDerivedFunctor hR ⊣ R'),
      ∀ L, Nonempty ((adicSheafDerivedEquivCondensedMod ℓ Z.left).functor.obj (R'.obj L).obj ≅
        ((CondensedRing.boundedConstructibleLowerStar ℓ g).rightAdjoint.obj
          ⟨(adicSheafDerivedEquivCondensedMod ℓ Y.left).functor.obj L.obj,
            (boundedConstructibleAdic_iff_boundedConstructible ℓ k₀ k Y L.obj).1
              L.property⟩).obj) :=
  sorry

end AlgebraicGeometry.ProEtale
