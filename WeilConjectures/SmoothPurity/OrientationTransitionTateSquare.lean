/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SmoothPurity.OrientationTransitionSquares
public import WeilConjectures.SmoothPurity.OrientationTransitionTate

/-!
# The reduction of the integral Tate twist under the reduction of coefficients

The shifted square of the Tate twist constituent of the finite orientations
(`ProEtale.CondensedRing.map_etaleReductionIntegralTateTwistIso_comp`), deduced from its unshifted
form, proved in `WeilConjectures.SmoothPurity.OrientationTransitionTate`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [NeZero (ℓ : k)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (E : PadicAlgCl.FiniteIntermediateField ℓ) (f : X ⟶ Y) (d : ℕ)
  [SmoothOfRelativeDimension d f.left]

/-- A formal shift computation: if `F i₂ ≫ R = b ≫ i₁`, then, through the commutation of `F`
with the shift by `a`, the shifts of `i₂ ≫ L₂⁻¹` and of `i₁ ≫ L₁⁻¹` correspond under
`F(L₂⟦a⟧) ≫ T ≫ L₁⁻¹⟦a⟧`, for `T` the commutation of `F` with the shift followed by `R⟦a⟧`. -/
lemma Functor.map_shift_map_comp_mapIso_trans_trans_symm_hom {C D : Type*} [Category C]
    [Category D] [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D) [F.CommShift ℤ] (a : ℤ)
    {A B B' : C} {A'' P P' : D} (i₂ : A ≅ B) (L₂ : B' ≅ B) (R : F.obj B ⟶ P) (b : F.obj A ⟶ A'')
    (i₁ : A'' ≅ P) (L₁ : P' ≅ P) (T : F.obj (B⟦a⟧) ≅ P⟦a⟧)
    (hT : T.hom = (F.commShiftIso a).hom.app B ≫ R⟦a⟧') (h : F.map i₂.hom ≫ R = b ≫ i₁.hom) :
    F.map ((shiftFunctor C a).map (i₂ ≪≫ L₂.symm).hom) ≫
        (F.mapIso ((shiftFunctor C a).mapIso L₂) ≪≫ T ≪≫
          ((shiftFunctor D a).mapIso L₁).symm).hom =
      (F.commShiftIso a).hom.app A ≫ b⟦a⟧' ≫ (shiftFunctor D a).map (i₁ ≪≫ L₁.symm).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv, hT,
    ← Functor.map_comp_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Functor.commShiftIso_hom_naturality_assoc, ← Functor.map_comp, reassoc_of% h]

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [NeZero (ℓ : k)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- The Tate data of `integersModPowSupportedCoefficientChange` are the commutation of `Ψ` with
the shifts followed by the canonical reduction of the Tate twists. -/
lemma integersModPowSupportedCoefficientChange_tateShiftIso_hom (n : ℕ)
    [HasInvertibleExponent (integersModPowCoeff.{u} ℓ E.1 (n + 1 + 1)) X.left]
    [HasInvertibleExponent (integersModPowCoeff.{u} ℓ E.1 (n + 1)) X.left] (m : ℤ) :
    ((integersModPowSupportedCoefficientChange ℓ E n).tateShiftIso X.left m).hom =
      ((integersModPowDerivedExtendScalars ℓ E.1 (n + 1) X.left).commShiftIso (2 * m)).hom.app _ ≫
        (integersModPowCanonicalTateTwistIso ℓ E.1 (n + 1) X m).hom⟦2 * m⟧' :=
  rfl

/-- Blueprint `det-sp-purity-coefficient-change`: change of coefficients in purity

**The reduction of the integral Tate twist is compatible with the reduction of coefficients**:
through `β : Ψ(red_{n+2} -) ≅ red_{n+1} -`, the identifications
`red_m(𝒪_{E,X}(d)) ≅ Λ_X(d)` (`etaleReductionIntegralTateTwistIso`) for `m = n + 2` and
`m = n + 1` correspond under the canonical Tate data `Ψ(Λ_X(d)[2d]) ≅ Λ'_X(d)[2d]`. -/
theorem map_etaleReductionIntegralTateTwistIso_comp (n : ℕ)
    [HasInvertibleExponent (integersModPowCoeff.{u} ℓ E.1 (n + 1 + 1)) X.left]
    [HasInvertibleExponent (integersModPowCoeff.{u} ℓ E.1 (n + 1)) X.left] :
    (integersModPowDerivedExtendScalars ℓ E.1 (n + 1) X.left).map
          ((shiftFunctor _ (2 * d : ℤ)).map
            (etaleReductionIntegralTateTwistIso ℓ E.1 (n + 1 + 1) X d ≪≫ (λ_ _).symm).hom) ≫
        ((integersModPowSupportedCoefficientChange ℓ E n).twistShiftConstantComplexIso
          X.left d).hom =
      ((integersModPowDerivedExtendScalars ℓ E.1 (n + 1) X.left).commShiftIso
          (2 * d : ℤ)).hom.app _ ≫
        (etaleReductionExtendScalarsIsoApp ℓ E.1 (n + 1) X _).hom⟦(2 * d : ℤ)⟧' ≫
          (shiftFunctor _ (2 * d : ℤ)).map
            (etaleReductionIntegralTateTwistIso ℓ E.1 (n + 1) X d ≪≫ (λ_ _).symm).hom := by
  exact Functor.map_shift_map_comp_mapIso_trans_trans_symm_hom
    (integersModPowDerivedExtendScalars ℓ E.1 (n + 1) X.left) (2 * d : ℤ)
    (etaleReductionIntegralTateTwistIso ℓ E.1 (n + 1 + 1) X d) (λ_ _)
    (integersModPowCanonicalTateTwistIso ℓ E.1 (n + 1) X d).hom
    (etaleReductionExtendScalarsIsoApp ℓ E.1 (n + 1) X _).hom
    (etaleReductionIntegralTateTwistIso ℓ E.1 (n + 1) X d) (λ_ _)
    ((integersModPowSupportedCoefficientChange ℓ E n).tateShiftIso X.left d)
    (integersModPowSupportedCoefficientChange_tateShiftIso_hom ℓ E n d)
    (map_etaleReductionIntegralTateTwistIso_hom_comp_reductionTateTwistIso_hom ℓ E.1 (n + 1) X d)

end AlgebraicGeometry.ProEtale.CondensedRing
