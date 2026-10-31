/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionOpenImmersion
public import WeilConjectures.SmoothPurity.OrientationUnique

/-!
# The canonical orientation along open immersions

Let `j : X ⟶ Y` be a morphism of separated `k`-schemes of finite type which is an open
immersion, hence smooth of relative dimension `0`. This file identifies the canonical
orientation (`ProEtale.CondensedRing.smoothOrientationOfSmooth`, blueprint
`sk-thm-purity-transport`) in two cases:

* for `j` itself, it is the canonical identification
  `ℚ̄_ℓ,X(0)[0] ≅ ℚ̄_ℓ,X ≅ j^* ℚ̄_ℓ,Y ≅ Rj^! ℚ̄_ℓ,Y`
  (`ProEtale.CondensedRing.openImmersionOrientation`,
  `ProEtale.CondensedRing.smoothOrientationOfSmooth_eq_openImmersionOrientation`);
* for a composite `f ≫ j` with `f` smooth of relative dimension `d`, it is the orientation of `f`
  followed by `Rf^! ℚ̄_ℓ,X ≅ Rf^! Rj^! ℚ̄_ℓ ≅ R(f ≫ j)^! ℚ̄_ℓ`
  (`ProEtale.CondensedRing.compOpenImmersionOrientation`,
  `ProEtale.CondensedRing.smoothOrientationOfSmooth_comp_openImmersion`).

The canonical orientation is the only one satisfying `IsCanonicalSmoothOrientation`
(`ProEtale.CondensedRing.smoothOrientationOfSmooth_eq_of_isCanonicalSmoothOrientation`), so it
suffices to show that the morphisms above are canonical orientations: they are the extensions of
scalars of integral lifts of the finite orientations. For `j`, the integral lift is the integral
canonical identification `𝒪_X(0)[0] ≅ 𝒪_X ≅ j^* 𝒪_Y ≅ Rj^! 𝒪_Y`
(`ProEtale.CondensedRing.integralOpenImmersionOrientation`).

## Unproved steps

The following steps are stated and `sorry`ed:

- `ProEtale.CondensedRing.isIntegralSmoothOrientation_integralOpenImmersionOrientation`: the
  reductions of the integral canonical identification are the finite orientations of the diagonal
  argument. This needs the finite statement for the open immersion (for `j` the diagonal is an
  isomorphism, and the orientation `Etale.dualizingComplexTwistShiftIso` of
  `Rj^! Λ ≅ Λ(0)[0]` is the canonical `Rj^! Λ ≅ j^* Λ ≅ Λ`), and the comparison of the canonical
  reduction isomorphism `etaleReductionUpperShriekIso` (built from the compactification chosen by
  Nagata's theorem) with `etaleReductionUpperShriekIsoOfIsOpenImmersion` (built from the trivial
  compactification).
- `ProEtale.CondensedRing.extendScalarsIntegralOrientation_integralOpenImmersionOrientation`: the
  extension of scalars to `ℚ̄_ℓ` of the integral identification is the `ℚ̄_ℓ` one, i.e. the
  coefficient comparison `integersToPadicAlgClUpperShriekUnitIso` is compatible with
  `Rj^! ≅ j^*` on both sides.
- `ProEtale.CondensedRing.isCanonicalSmoothOrientation_compOpenImmersionOrientation`: the
  finite orientations are compatible with composition with an open immersion, and so are the
  coefficient comparisons.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

section OpenImmersion

variable (j : X ⟶ Y) [IsOpenImmersion j.left]

/-- The **canonical orientation of an open immersion** `j`, `ℚ̄_ℓ,X(0)[0] ⟶ Rj^! ℚ̄_ℓ,Y`: the
identifications `ℚ̄_ℓ,X(0)[0] ≅ ℚ̄_ℓ,X(0) ≅ ℚ̄_ℓ,X` (`tateTwistDerivedZeroIso`) followed by the
inverse of purity for the open immersion `Rj^! ℚ̄_ℓ,Y ≅ j^* ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,X`
(`boundedConstructibleUpperShriekUnitIso_padicAlgCl`). -/
noncomputable def openImmersionOrientation :
    boundedConstructibleTateTwist ℓ X (0 : ℕ) (2 * (0 : ℕ)) ⟶
      (boundedConstructibleUpperShriek ℓ j).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :=
  (ObjectProperty.fullyFaithfulι _).preimage
    (((shiftFunctorZero' _ (2 * ((0 : ℕ) : ℤ)) (by simp)).app _).hom ≫
      (tateTwistDerivedZeroIso ℓ X.left).hom ≫
      (ObjectProperty.ι _).map (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).inv)

lemma ι_map_openImmersionOrientation :
    (ObjectProperty.ι _).map (openImmersionOrientation ℓ j) =
      ((shiftFunctorZero' _ (2 * ((0 : ℕ) : ℤ)) (by simp)).app _).hom ≫
        (tateTwistDerivedZeroIso ℓ X.left).hom ≫
        (ObjectProperty.ι _).map (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).inv :=
  (ObjectProperty.fullyFaithfulι _).map_preimage _

variable (E : PadicAlgCl.FiniteIntermediateField ℓ) [NeZero (ℓ : k)]

/-- The **integral canonical orientation of an open immersion** `j`,
`𝒪_{E,X}(0)[0] ⟶ Rj^! 𝒪_{E,Y}`: the identification `𝒪_{E,X}(0)[0] ≅ 𝒪_{E,X}[0] ≅ 𝒪_{E,X}`
(`𝒪_{E,X}(0)` is the unit `𝒪_{E,X}` by definition) followed by the unit isomorphism
`𝒪_{E,X} ≅ j^* 𝒪_{E,Y}` of the monoidal functor `j^*` and `j^* ≅ Rj^!`
(`boundedConstructibleUpperShriekIsoUpperStar_padicIntegers`). -/
noncomputable def integralOpenImmersionOrientation :
    (shiftFunctor (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) (2 * ((0 : ℕ) : ℤ))).obj
        (integralTateTwistBoundedConstructible ℓ E.1 X.hom 0) ⟶
      (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 j).obj (𝟙_ _) :=
  (ObjectProperty.fullyFaithfulι _).preimage
    (((shiftFunctorZero' _ (2 * ((0 : ℕ) : ℤ)) (by simp)).app _).hom ≫
      (DerivedCategory.singleFunctorObjUnitIso _).hom ≫
      (ObjectProperty.ι _).map
        ((Functor.Monoidal.εIso
          (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ j)).hom ≫
        ((boundedConstructibleUpperShriekIsoUpperStar_padicIntegers ℓ E.1 j).app _).inv))

/-- The reductions of the integral canonical orientation of an open immersion are the canonical
finite orientations of the diagonal argument. -/
theorem isIntegralSmoothOrientation_integralOpenImmersionOrientation :
    IsIntegralSmoothOrientation ℓ E j 0 (integralOpenImmersionOrientation ℓ j E) :=
  sorry

/-- The extension of scalars to `ℚ̄_ℓ` of the integral canonical orientation of an open immersion
is the canonical orientation `openImmersionOrientation`. -/
theorem extendScalarsIntegralOrientation_integralOpenImmersionOrientation :
    extendScalarsIntegralOrientation ℓ E j 0 (integralOpenImmersionOrientation ℓ j E) =
      openImmersionOrientation ℓ j :=
  sorry

/-- The canonical orientation of an open immersion is a canonical orientation in the sense of
`IsCanonicalSmoothOrientation`. -/
theorem isCanonicalSmoothOrientation_openImmersionOrientation :
    IsCanonicalSmoothOrientation ℓ j 0 (openImmersionOrientation ℓ j) :=
  ⟨_, isIntegralSmoothOrientation_integralOpenImmersionOrientation ℓ j _,
    extendScalarsIntegralOrientation_integralOpenImmersionOrientation ℓ j _⟩

/-- Blueprint `sk-thm-purity-transport`, étale case: **the orientation of an open immersion is
the canonical identification** `ℚ̄_ℓ,X(0)[0] ≅ ℚ̄_ℓ,X ≅ Rj^! ℚ̄_ℓ,Y`. -/
theorem smoothOrientationOfSmooth_eq_openImmersionOrientation :
    smoothOrientationOfSmooth ℓ j 0 = openImmersionOrientation ℓ j :=
  smoothOrientationOfSmooth_eq_of_isCanonicalSmoothOrientation ℓ j 0
    (isCanonicalSmoothOrientation_openImmersionOrientation ℓ j)

end OpenImmersion

section Composition

variable {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] (f : X ⟶ Y) (j : Y ⟶ Z) [IsOpenImmersion j.left] (d : ℕ)

/-- The orientation of `f ≫ j`, for an open immersion `j`, induced by a morphism
`φ : ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y`: `φ` followed by `Rf^! ℚ̄_ℓ,Y ≅ Rf^! Rj^! ℚ̄_ℓ,Z` (purity for
the open immersion `j`, `boundedConstructibleUpperShriekUnitIso_padicAlgCl`) and the
composition isomorphism `Rf^! Rj^! ≅ R(f ≫ j)^!`. -/
noncomputable def compOpenImmersionOrientation
    (φ : boundedConstructibleTateTwist ℓ X d (2 * d) ⟶
      (boundedConstructibleUpperShriek ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))) :
    boundedConstructibleTateTwist ℓ X d (2 * d) ⟶
      (boundedConstructibleUpperShriek ℓ (f ≫ j)).obj
        (𝟙_ (Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :=
  φ ≫ (boundedConstructibleUpperShriek ℓ f).map
      (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).inv ≫
    (boundedConstructibleUpperShriekComp_padicAlgCl ℓ f j).inv.app _

variable [NeZero (ℓ : k)] [SmoothOfRelativeDimension d f.left]
  [SmoothOfRelativeDimension d (f ≫ j).left]

/-- Blueprint `sk-prop-sp-composition`, case of an open immersion: the orientation of `f ≫ j`
induced by the canonical orientation of `f` is a canonical orientation. -/
theorem isCanonicalSmoothOrientation_compOpenImmersionOrientation :
    IsCanonicalSmoothOrientation ℓ (f ≫ j) d
      (compOpenImmersionOrientation ℓ f j d (smoothOrientationOfSmooth ℓ f d)) :=
  sorry

/-- Blueprint `sk-prop-sp-composition`, case of an open immersion: **the orientation of `f ≫ j`
is that of `f` followed by `Rf^! ℚ̄_ℓ ≅ Rf^! Rj^! ℚ̄_ℓ ≅ R(f ≫ j)^! ℚ̄_ℓ`**. -/
theorem smoothOrientationOfSmooth_comp_openImmersion :
    smoothOrientationOfSmooth ℓ (f ≫ j) d =
      compOpenImmersionOrientation ℓ f j d (smoothOrientationOfSmooth ℓ f d) :=
  smoothOrientationOfSmooth_eq_of_isCanonicalSmoothOrientation ℓ (f ≫ j) d
    (isCanonicalSmoothOrientation_compOpenImmersionOrientation ℓ f j d)

end Composition

end AlgebraicGeometry.ProEtale.CondensedRing
