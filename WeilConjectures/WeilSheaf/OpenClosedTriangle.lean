/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.CohomologySequence

/-!
# The open–closed triangle under direct image with compact support

For a closed immersion `i : Z ↪ X` with open complement `j : U ↪ X` of separated `k₀`-schemes of
finite type, applying `Ra_!` to the open–closed localization triangle `j_!j^*K → K → i_*i^*K →` of
a Weil complex `K` on `X` gives a distinguished triangle

`Ra_{U!} j^*K ⟶ Ra_{X!} K ⟶ Ra_{Z!} i^*K ⟶`

of Weil complexes on `Spec k₀` (blueprint `prop-functor-package`, clause 3). This file states it,
and identifies the pullback of a Weil sheaf placed in degree zero with the pullback of the sheaf.

## Main declarations

- `AlgebraicGeometry.WeilComplex.exists_distTriang_derivedLowerShriek_openClosed`: the triangle.
- `AlgebraicGeometry.WeilSheaf.toComplexCompUpperStarIso`: `φ^* (F[0]) ≅ (φ^* F)[0]`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **The open–closed triangle under `Ra_!`**: for a closed immersion `i : Z ↪ X` with open
complement `j : U ↪ X` of separated `k₀`-schemes of finite type and a Weil complex `K` on `X`,
there is a distinguished triangle of Weil complexes on `Spec k₀`

`Ra_{U!} j^*K ⟶ Ra_{X!} K ⟶ Ra_{Z!} i^*K ⟶ Ra_{U!} j^*K[1]`,

obtained by applying `Ra_{X!}` to the open–closed recollement triangle `j_!j^*K → K → i_*i^*K →`
and using `R(a_X j)_! = Ra_{X!} j_!` and `R(a_X i)_! = Ra_{X!} i_*`, with the Weil structures of
the operations. (blueprint: `prop-functor-package`, clause 3) -/
theorem WeilComplex.exists_distTriang_derivedLowerShriek_openClosed {U X Z : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (U ↘ Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) (K : WeilComplex k₀ l X) :
    ∃ (α : (derivedLowerShriek k₀ l (U ↘ Spec (CommRingCat.of k₀))).obj
          ((WeilComplex.upperStar j).obj K) ⟶
        (derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).obj K)
      (β : (derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).obj K ⟶
        (derivedLowerShriek k₀ l (Z ↘ Spec (CommRingCat.of k₀))).obj
          ((WeilComplex.upperStar i).obj K))
      (γ : (derivedLowerShriek k₀ l (Z ↘ Spec (CommRingCat.of k₀))).obj
          ((WeilComplex.upperStar i).obj K) ⟶
        ((derivedLowerShriek k₀ l (U ↘ Spec (CommRingCat.of k₀))).obj
          ((WeilComplex.upperStar j).obj K))⟦(1 : ℤ)⟧),
      Triangle.mk α β γ ∈ distTriang (WeilComplex k₀ l (Spec (CommRingCat.of k₀))) := by
  sorry

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

/-- The pullback of a Weil sheaf placed in degree zero is the pullback of the sheaf placed in
degree zero: the pullback of pro-étale Weil sheaves is exact. -/
noncomputable def WeilSheaf.toComplexCompUpperStarIso :
    WeilSheaf.toComplex ⋙ WeilComplex.upperStar φ ≅
      WeilSheaf.upperStar (k₀ := k₀) (l := l) φ ⋙ WeilSheaf.toComplex :=
  ((WeilComplex.objectProperty k₀ l X).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((ProEtaleWeilSheaf.upperStar k₀ l φ).mapDerivedCategorySingleFunctor
        0) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _).symm ≪≫
      (Functor.associator _ _ _).symm)

end AlgebraicGeometry
