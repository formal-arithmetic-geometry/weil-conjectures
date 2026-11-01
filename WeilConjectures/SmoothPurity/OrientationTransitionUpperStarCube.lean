/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReductionTranspose
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReductionUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStarComapCube
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStarDerived
public import WeilConjectures.SmoothPurity.OrientationTransitionUpperStarTransition

/-!
# The reduction square for the pullbacks: the cube

The pro-étale reduction square for the pullbacks
(`ProEtale.CondensedRing.map_etaleReductionProEtaleTranspose_comp_eq`) is the composite of two
commutative faces (blueprint `det-sp-purity-coefficient-change`):

* `ProEtale.leftDerivedUpperStar_map_finiteCoefficientDerivedEquivalenceComapIso_hom_app_comp`:
  the comparison `Φ` of the two finite-coefficient models commutes with the derived pullbacks
  compatibly with the restrictions of scalars on both sides;
* `ProEtale.CondensedRing.leftDerivedUpperStar_map_unit_app_comp_eq`: the condensed transition
  `red_{n+1} ⟶ Res((𝒪_E ⧸ ℓⁿ) ⊗ᴸ red_{n+1}) ≅ Res(red_n)` commutes with the derived pullbacks.

`CategoryTheory.map_comp_hom_app_comp_map_eq_of_cube` assembles the two faces.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

/-- **Assembling a cube of commutation isomorphisms.** Let `Φ` be functors (comparisons) from
`C`-categories to `P`-categories, `F` functors (pullbacks) from `Y`-categories to `Z`-categories,
and `R` functors (restrictions) from unprimed to primed categories, with commutation isomorphisms
`c : R ⋙ Φ' ≅ Φ ⋙ R`, `U : F ⋙ Φ ≅ Φ ⋙ F`, `r : R ⋙ F' ≅ F ⋙ R` and `s : R ⋙ F' ≅ F ⋙ R`. If the
face `H₁` of the cube relating `c`, `r`, `U` and `s` commutes at `A`, and the morphisms
`gY : A' ⟶ R A`, `gZ : B' ⟶ R B`, `h₁ ≫ h₂ : F A ⟶ B` and `h₁' ≫ h₂' : F' A' ⟶ B'` are
intertwined by `s` (`H₂`), then the composites `F'(Φ'(gY) ≫ c) ≫ r ≫ R(U⁻¹ ≫ Φ(h₁ ≫ h₂))` and
`(U'⁻¹ ≫ Φ'(h₁' ≫ h₂')) ≫ Φ'(gZ) ≫ c` agree. -/
lemma map_comp_hom_app_comp_map_eq_of_cube {CY' CY CZ' CZ PY' PY PZ' PZ : Type*}
    [Category CY'] [Category CY] [Category CZ'] [Category CZ] [Category PY'] [Category PY]
    [Category PZ'] [Category PZ]
    {ΦY' : CY' ⥤ PY'} {ΦY : CY ⥤ PY} {ΦZ' : CZ' ⥤ PZ'} {ΦZ : CZ ⥤ PZ}
    {Fc' : CY' ⥤ CZ'} {Fc : CY ⥤ CZ} {Fp' : PY' ⥤ PZ'} {Fp : PY ⥤ PZ}
    {RcY : CY ⥤ CY'} {RcZ : CZ ⥤ CZ'} {RpY : PY ⥤ PY'} {RpZ : PZ ⥤ PZ'}
    {cY : RcY ⋙ ΦY' ≅ ΦY ⋙ RpY} {cZ : RcZ ⋙ ΦZ' ≅ ΦZ ⋙ RpZ}
    {U' : Fc' ⋙ ΦZ' ≅ ΦY' ⋙ Fp'} {U : Fc ⋙ ΦZ ≅ ΦY ⋙ Fp}
    {r : RpY ⋙ Fp' ≅ Fp ⋙ RpZ} {s : RcY ⋙ Fc' ≅ Fc ⋙ RcZ}
    {A' : CY'} {A : CY} {B' : CZ'} {B : CZ} {C₁ : CZ} {C₁' : CZ'}
    {gY : A' ⟶ RcY.obj A} {gZ : B' ⟶ RcZ.obj B}
    {h₁ : Fc.obj A ⟶ C₁} {h₂ : C₁ ⟶ B} {h₁' : Fc'.obj A' ⟶ C₁'} {h₂' : C₁' ⟶ B'}
    (H₁ : Fp'.map (cY.hom.app A) ≫ r.hom.app (ΦY.obj A) ≫ RpZ.map (U.inv.app A) =
      U'.inv.app (RcY.obj A) ≫ ΦZ'.map (s.hom.app A) ≫ cZ.hom.app (Fc.obj A))
    (H₂ : Fc'.map gY ≫ s.hom.app A ≫ RcZ.map (h₁ ≫ h₂) = h₁' ≫ h₂' ≫ gZ) :
    Fp'.map (ΦY'.map gY ≫ cY.hom.app A) ≫ r.hom.app (ΦY.obj A) ≫
        RpZ.map (U.inv.app A ≫ ΦZ.map h₁ ≫ ΦZ.map h₂) =
      (U'.inv.app A' ≫ ΦZ'.map h₁' ≫ ΦZ'.map h₂') ≫ ΦZ'.map gZ ≫ cZ.hom.app B := by
  have hU : Fp'.map (ΦY'.map gY) ≫ U'.inv.app (RcY.obj A) = U'.inv.app A' ≫ ΦZ'.map (Fc'.map gY) :=
    U'.inv.naturality gY
  have hc : cZ.hom.app (Fc.obj A) ≫ RpZ.map (ΦZ.map h₁) ≫ RpZ.map (ΦZ.map h₂) =
      ΦZ'.map (RcZ.map h₁) ≫ ΦZ'.map (RcZ.map h₂) ≫ cZ.hom.app B := by
    simpa using (cZ.hom.naturality (h₁ ≫ h₂)).symm
  simp only [Functor.map_comp, assoc] at H₁ ⊢
  rw [reassoc_of% H₁, reassoc_of% hU, hc]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp]
  rw [H₂]

/-- Moving the components of two natural isomorphisms across an equation. -/
lemma inv_app_comp_eq_of_hom_app_comp {C D E C' : Type*} [Category C] [Category D] [Category E]
    [Category C'] {F G : C ⥤ E} {F' G' : C' ⥤ D} {R : D ⥤ E} {e : F ≅ G} {e' : F' ≅ G'} {X : C}
    {X' : C'} {A B : E} {x : F.obj X ⟶ A} {y : A ⟶ R.obj (F'.obj X')} {p : G.obj X ⟶ B}
    {q : B ⟶ R.obj (G'.obj X')}
    (H : x ≫ y ≫ R.map (e'.hom.app X') = e.hom.app X ≫ p ≫ q) :
    p ≫ q ≫ R.map (e'.inv.app X') = e.inv.app X ≫ x ≫ y := by
  rw [← cancel_epi (e.hom.app X), Iso.hom_inv_id_app_assoc, ← reassoc_of% H, ← R.map_comp,
    Iso.hom_inv_id_app, R.map_id, comp_id]


end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {T T' : Type} [TopologicalSpace T] [CommRing T]
  [IsTopologicalRing T] [DiscreteTopology T] [Finite T] [TopologicalSpace T'] [CommRing T']
  [IsTopologicalRing T'] [DiscreteTopology T'] [Finite T'] (ρ : T →+* T')

/-- **The underived cube**: for `ρ : T →+* T'`, the commutations of the comparison of the two
finite-coefficient models with the pullbacks (`upperStarFiniteCoefficientModEquivalenceIso`) and
with the restrictions of scalars (`finiteCoefficientModEquivalenceComapIso`) are compatible with
the commutations of the restrictions of scalars with the pullbacks, pro-étale
(`upperStarRestrictScalarsIso`) and condensed (`CondensedRing.comapUpperStarIso`). -/
lemma finiteCoefficientModEquivalence_upperStar_comap_cube
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T') Y)) :
    (finiteCoefficientModEquivalence X T).functor.map
        ((CondensedRing.comapUpperStarIso (Profinite.continuousMapRingObjMap.{u} ρ
          continuous_of_discreteTopology) f).symm.hom.app N) ≫
      (finiteCoefficientModEquivalenceComapIso X ρ).hom.app
        ((CondensedRing.upperStar (Profinite.continuousMapRingObj T') f).obj N) ≫
      (Sheaf.restrictScalars (Scheme.ProEt.topology X) ρ.ulift).map
        ((upperStarFiniteCoefficientModEquivalenceIso f T').symm.inv.app N) =
    (upperStarFiniteCoefficientModEquivalenceIso f T).symm.inv.app
        ((Mod.comap (coefficientMap (Profinite.continuousMapRingObjMap.{u} ρ
          continuous_of_discreteTopology) Y)).obj N) ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} T)) f).map
        ((finiteCoefficientModEquivalenceComapIso Y ρ).hom.app N) ≫
      (upperStarRestrictScalarsIso ρ.ulift f).hom.app
        ((finiteCoefficientModEquivalence Y T').functor.obj N) :=
  map_comapUpperStarIso_symm_hom_app_comp_finiteCoefficientModEquivalenceComapIso_hom_app f ρ N

/-- **The comparison of the finite-coefficient models, the derived pullbacks and the
restrictions of scalars form a commutative cube**: for `ρ : T →+* T'`, the commutations of the
comparison `Φ` (`finiteCoefficientDerivedEquivalence`) with the restrictions of scalars
(`finiteCoefficientDerivedEquivalenceComapIso`) and with the derived pullbacks
(`leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso`) are compatible with the
commutations of the restrictions of scalars with the derived pullbacks, pro-étale
(`leftDerivedUpperStarRestrictScalarsIso`) and condensed
(`CondensedRing.derivedComapLeftDerivedUpperStarIso`).

All functors involved are exact, so this is the derived form of the corresponding cube of
underived isomorphisms; the passage to derived categories is
`Functor.mapDerivedCategorySquareIso_cube_of_iso`. -/
lemma leftDerivedUpperStar_map_finiteCoefficientDerivedEquivalenceComapIso_hom_app_comp
    (N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T') Y))) :
    (L(ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} T)) f)).map
        ((finiteCoefficientDerivedEquivalenceComapIso Y ρ).hom.app N) ≫
      (leftDerivedUpperStarRestrictScalarsIso ρ.ulift f).hom.app
        ((finiteCoefficientDerivedEquivalence Y T').functor.obj N) ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) ρ.ulift).map
        ((leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso f T').inv.app N) =
    (leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso f T).inv.app
        ((Mod.comap (coefficientMap (Profinite.continuousMapRingObjMap.{u} ρ
          continuous_of_discreteTopology) Y)).mapDerivedCategory.obj N) ≫
      (finiteCoefficientDerivedEquivalence X T).functor.map
        ((CondensedRing.derivedComapLeftDerivedUpperStarIso (Profinite.continuousMapRingObjMap.{u} ρ
          continuous_of_discreteTopology) f).hom.app N) ≫
      (finiteCoefficientDerivedEquivalenceComapIso X ρ).hom.app
        ((L(CondensedRing.upperStar (Profinite.continuousMapRingObj T') f)).obj N) := by
  have H := Functor.mapDerivedCategorySquareIso_cube_of_iso _ _ _ _ _ _
    (finiteCoefficientModEquivalence_upperStar_comap_cube f ρ)
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory _ f)
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory _ f)
    (leftDerivedUpperStarIsoMapDerivedCategory _ f)
    (leftDerivedUpperStarIsoMapDerivedCategory _ f)
    (finiteCoefficientDerivedEquivalenceComapIso Y ρ) rfl
    (finiteCoefficientDerivedEquivalenceComapIso X ρ) rfl
    (leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso f T').symm (fun M ↦ by
      have h := Functor.mapDerivedCategoryNatIso_symm
        (upperStarFiniteCoefficientModEquivalenceIso f T').symm
      rw [Iso.symm_symm_eq] at h
      simp [leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso, ← h]
      rfl)
    (leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso f T).symm (fun M ↦ by
      have h := Functor.mapDerivedCategoryNatIso_symm
        (upperStarFiniteCoefficientModEquivalenceIso f T).symm
      rw [Iso.symm_symm_eq] at h
      simp [leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso, ← h]
      rfl)
    (CondensedRing.derivedComapLeftDerivedUpperStarIso (Profinite.continuousMapRingObjMap.{u} ρ
          continuous_of_discreteTopology) f) (fun M ↦ rfl)
    (leftDerivedUpperStarRestrictScalarsIso ρ.ulift f) (fun M ↦ rfl) N
  simp only [Iso.symm_inv] at H
  exact inv_app_comp_eq_of_hom_app_comp
    (e := leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso f T)
    (e' := leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso f T')
    (R := Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) ρ.ulift) H

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)
  {Z Y : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : Z ⟶ Y)

set_option synthInstance.maxHeartbeats 400000 in
-- The derived pullback over `𝒪_E ⧸ ℓⁿ⁺¹` needs a slow instance search (monoidal structure on
-- graded objects for the K-flat resolutions).
set_option maxHeartbeats 1000000 in
-- elaborating this statement unifies large composites of derived functors
/-- **The condensed transition commutes with the derived pullbacks**: the condensed transition
`red_{n+1} K ⟶ Res((𝒪_E ⧸ ℓⁿ) ⊗ᴸ red_{n+1} K) ≅ Res(red_n K)` (the unit of the derived extension
of scalars along `𝒪_E ⧸ ℓⁿ⁺¹ ⟶ 𝒪_E ⧸ ℓⁿ`, followed by
`boundedConstructibleIntegersModPowReductionTransitionIso`) is intertwined with its value at
`f^* M` by the commutations of the reductions with the derived pullbacks
(`boundedConstructibleUpperStarIntegersModPowReductionIso`) and of the restriction of scalars with
the derived pullbacks (`derivedComapLeftDerivedUpperStarIso`). -/
lemma leftDerivedUpperStar_map_unit_app_comp_eq
    (M : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    (L((f.left)^*⟦Profinite.integersModPowRingObj ℓ E (n + 1)⟧)).map
        ((Mod.derivedExtendMapDerivedCategoryAdjunction
          (integersModPowTransition Y.left ℓ E n)).unit.app
          ((boundedConstructible _).ι.obj
            ((boundedConstructibleIntegersModPowReduction Y.left ℓ E (n + 1)).obj M)) ≫
        (Mod.comap (integersModPowTransition Y.left ℓ E n)).mapDerivedCategory.map
          ((boundedConstructibleIntegersModPowReductionTransitionIso ℓ E n Y.left).hom.app M)) ≫
      (derivedComapLeftDerivedUpperStarIso (Profinite.integersModPowRingObjTransition ℓ E n)
        f.left).hom.app ((boundedConstructible _).ι.obj
          ((boundedConstructibleIntegersModPowReduction Y.left ℓ E n).obj M)) ≫
      (Mod.comap (integersModPowTransition Z.left ℓ E n)).mapDerivedCategory.map
        ((boundedConstructibleUpperStarCompatibility _ ℓ f).inv.app
          ((boundedConstructibleIntegersModPowReduction Y.left ℓ E n).obj M) ≫
         (boundedConstructible _).ι.map
          ((boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n f).inv.app M)) =
    (boundedConstructibleUpperStarCompatibility _ ℓ f).inv.app
          ((boundedConstructibleIntegersModPowReduction Y.left ℓ E (n + 1)).obj M) ≫
      (boundedConstructible _).ι.map
          ((boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E (n + 1) f).inv.app M) ≫
      (Mod.derivedExtendMapDerivedCategoryAdjunction
          (integersModPowTransition Z.left ℓ E n)).unit.app
          ((boundedConstructible _).ι.obj
            ((boundedConstructibleIntegersModPowReduction Z.left ℓ E (n + 1)).obj
              ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ f).obj M))) ≫
        (Mod.comap (integersModPowTransition Z.left ℓ E n)).mapDerivedCategory.map
          ((boundedConstructibleIntegersModPowReductionTransitionIso ℓ E n Z.left).hom.app
            ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ f).obj M)) := by
  exact map_unit_app_comp_map_comp_eq rfl rfl
    (upperStar_map_unit_comp_derivedComapLeftDerivedUpperStarIso_hom_app
      (Profinite.padicIntegersRingObjToIntegersModPow ℓ E (n + 1)) f.left)
    (upperStar_map_unit_comp_derivedComapLeftDerivedUpperStarIso_hom_app
      (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) f.left)
    (map_mapDerivedCategoryComapCompIso_inv_app_comp_derivedComapLeftDerivedUpperStarIso _ _ _
      f.left (integersModPowReduction_comp_integersModPowTransition Y.left ℓ E n)
      (integersModPowReduction_comp_integersModPowTransition Z.left ℓ E n))
    (boundedConstructibleIntegersModPowReductionTransitionIso_hom_app ℓ E n Y.left M)
    (boundedConstructibleIntegersModPowReductionTransitionIso_hom_app ℓ E n Z.left _)
    rfl rfl rfl rfl rfl rfl
    (boundedConstructibleUpperStarIntegersModPowReductionIso_inv_app_hom ℓ E (n + 1) f M)
    (boundedConstructibleUpperStarIntegersModPowReductionIso_inv_app_hom ℓ E n f M)

end AlgebraicGeometry.ProEtale.CondensedRing
