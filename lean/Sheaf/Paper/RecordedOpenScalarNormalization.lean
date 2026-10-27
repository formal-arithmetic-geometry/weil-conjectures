/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Sheaf.Paper.EtaleProEtaleCoefficientTransport
public import Sheaf.Paper.OpenScalarSiteCoherence
public import Sheaf.Paper.FiniteCompactScalarCoordinates
import all Sheaf.Paper.FiniteOpenScalarRealizationTransport
import all Sheaf.Paper.FiniteOpenScalarSiteTransport
import Sheaf.Paper.OpenScalarCounitSquare

/-! # Realization normalization for the open scalar factor

Source: Stacks Tags 00YV, 03DI and 07A6; the open-factor argument in
`lem-sp-recorded-compact-scalar-fixed-normalization`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CoefficientCompatibility

attribute [local irreducible] sfIntrinsicModuleEquivalence
attribute [local implicit_reducible] proEtaleConstantRingMap scalarExtensionFunctor

private theorem conjugated_scalar_unit
    {C D C' D' : Type*}
    [Category C] [Category D] [Category C'] [Category D']
    (E : C ≌ C') (F : D ≌ D')
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (b : L' ⊣ R') (r : F.functor ⋙ R' ≅ R ⋙ E.functor)
    (M : C) :
    E.functor.map (a.unit.app M) ≫ r.inv.app (L.obj M) =
      b.unit.app (E.functor.obj M) ≫ R'.map
        ((((E.toAdjunction.comp b).ofNatIsoRight
          (isoWhiskerRight F.counitIso.symm (R' ⋙ E.inverse) ≪≫
            isoWhiskerLeft F.inverse (isoWhiskerRight r E.inverse) ≪≫
            isoWhiskerLeft (F.inverse ⋙ R) E.unitIso.symm)).leftAdjointUniq
          (a.comp F.toAdjunction)).hom.app M) := by
  apply comparison_unit E F a b _ r
  intro N
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    isoWhiskerRight_inv, isoWhiskerLeft_inv, whiskerRight_app, whiskerLeft_app,
    Functor.comp_map, Functor.comp_obj, Category.assoc]
  have hη := E.unitIso.hom.naturality (R.map (F.unitIso.hom.app N))
  have hr := r.inv.naturality (F.unitIso.hom.app N)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hη hr
  rw [reassoc_of% hη, ← E.inverse.map_comp_assoc, hr]
  simp only [Functor.map_comp, Category.assoc]
  rw [← E.inverse.map_comp, ← R'.map_comp]
  simp only [F.functor_unitIso_comp, Functor.id_obj]
  erw [R'.map_id, E.inverse.map_id, Category.comp_id]

private theorem scalarPresentation_eq
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) :
    scalarPresentation φ T = FiniteCompactScalar.realizationScalarIso φ T := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let a := proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := T) φ)
  let b := Adjunction.ofIsRightAdjoint
    (@Sheaf.derivedRestrictScalars.{u} T.ProEt inferInstance
      (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology T)
      (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance
      (uliftRingHom φ))
  let r := mapDerivedCategorySquareIso.{u + 2, u + 2, u + 2, u + 2,
      u + 2, u + 1, u + 2, u + 1, u + 1, u + 1, u + 1, u + 1}
        (sfRealizationRestriction T φ)
  have hn := conjugated_scalar_unit
    (sfIntrinsicDerivedEquivalence T A) (sfIntrinsicDerivedEquivalence T B) b a r
  apply Iso.ext
  ext M
  apply (a.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  have hnew :
      (sfIntrinsicDerivedEquivalence T A).functor.map (b.unit.app M) ≫
          r.inv.app ((liftedScalarExtension φ T).obj M) =
        a.unit.app ((sfIntrinsicDerivedEquivalence T A).functor.obj M) ≫
          (scalarRestriction φ T).map ((scalarPresentation φ T).hom.app M) := by
    simpa only [scalarPresentation, r, sfRealizationRestriction, liftedScalarExtension,
      uliftRingHom, pbcFixedScalarExtension, scalarRestriction,
      proEtaleCoefficientRestrictScalars, proEtaleConstantRingMap, a, b] using hn M
  exact hnew.symm.trans (FiniteCompactScalar.realization_scalar_unit T φ M)

private theorem scalar_unit_of_counit
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {S : C ⥤ D} {U : D ⥤ C} {T : E ⥤ F} {V : F ⥤ E}
    (a : S ⊣ U) (b : T ⊣ V) (P : E ⥤ C) (Q : F ⥤ D)
    (c : P ⋙ S ⟶ T ⋙ Q) (v : V ⋙ P ⟶ Q ⋙ U)
    (hc : ∀ N, S.map (v.app N) ≫ a.counit.app (Q.obj N) =
      c.app (V.obj N) ≫ Q.map (b.counit.app N)) (M : E) :
    a.unit.app (P.obj M) ≫ U.map (c.app M) =
      P.map (b.unit.app M) ≫ v.app (T.obj M) := by
  apply (a.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, S.map_comp, Category.assoc]
  rw [a.counit_naturality, ← Category.assoc, a.left_triangle_components (P.obj M)]
  dsimp only [Functor.comp_obj]
  rw [hc]
  have hn := c.naturality (b.unit.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  erw [← Category.assoc, hn, Category.assoc, ← Q.map_comp,
    b.left_triangle_components, Q.map_id, Category.comp_id]
  exact Category.id_comp _

/-- Realization identifies the recorded open scalar comparison with its fixed-module
comparison, before any direct image is applied.

Source: Stacks Project, Tags 00YV, 03DI and 07A6; open-factor part of Step 1 of
`lem-sp-recorded-compact-scalar-fixed-normalization`.
(blueprint: lem-sp-recorded-open-scalar-fixed-normalization).

Proof: express the intrinsic open extension as inverse realization, fixed open
extension, and forward realization. Its realization comparison is openRealizationIso,
which cancels the adjacent realization unit. The scalar restriction comparison is
the termwise section-identity square sfRealizationRestriction. Conjugating the fixed
open/restriction square through realization gives sfOpenRestriction; canceling the
realization unit and counit shows that this restriction cube commutes. Transpose under
the scalar adjunctions. The scalar uniqueness comparison is scalarPresentation,
since its right square is exactly this conjugated section-identity square. The
intrinsic open scalar transpose is reductionOpenScalarIso: reductionOpenModel is the
unit-preserving change from the sheafified open model, and openScalarIso is the
uniqueness map for the composite open/scalar left adjoints. The fixed transpose is
OpenScalarSite.scalarOpen, by the same composite-adjoint uniqueness and its literal
restriction square. Naturality and the triangle identities give the displayed
square on arbitrary unbounded inputs. Empty opens, identity opens and zero rings
satisfy the same unit equations; no support or boundedness assumption is needed. -/
theorem recordedOpenScalar_fixed_normalization
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (K : DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (reductionOpenScalarIso φ j).hom.app
          ((sfIntrinsicDerivedEquivalence X A).functor.obj K) ≫
        (sfIntrinsicExtensionByZero j B).mapDerivedCategory.map
          ((scalarPresentation φ X).hom.app K) ≫
        (FiniteCompactScalar.openRealizationIso B j).hom.app
          ((liftedScalarExtension φ X).obj K) =
      (scalarExtensionFunctor φ Z).map
          ((FiniteCompactScalar.openRealizationIso A j).hom.app K) ≫
        (scalarPresentation φ Z).hom.app
          ((openImmersionLowerShriek
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory.obj K) ≫
        (sfIntrinsicDerivedEquivalence Z B).functor.map
          ((OpenScalarSite.scalarOpen (uliftRingHom φ) j).hom.app K) := by
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : EssentiallySmall.{u + 1} Z.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let ax := proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := X) φ)
  let az := proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := Z) φ)
  let bx := Adjunction.ofIsRightAdjoint
    (@Sheaf.derivedRestrictScalars.{u} X.ProEt inferInstance
      (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X)
      (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance
      (uliftRingHom φ))
  let bz := Adjunction.ofIsRightAdjoint
    (@Sheaf.derivedRestrictScalars.{u} Z.ProEt inferInstance
      (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology Z)
      (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance
      (uliftRingHom φ))
  let I := (sfIntrinsicExtensionByZero j A).mapDerivedCategory
  let J := (sfIntrinsicExtensionByZero j B).mapDerivedCategory
  let F := (openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory
  let G := (openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).mapDerivedCategory
  have hi (M : proEtaleDerivedCategory X A) :
      (az.homEquiv _ _).symm
          (I.map (ax.unit.app M) ≫
            (sfOpenRestrictionDerived j φ).hom.app ((scalarExtensionFunctor φ X).obj M)) =
        (reductionOpenScalarIso φ j).hom.app M := by
    apply (az.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    apply Eq.symm
    apply scalar_unit_of_counit az ax I J (reductionOpenScalarIso φ j).hom
      (sfOpenRestrictionDerived j φ).hom
    intro N
    exact congr_app (openScalarCounitSquare φ j) N
  let a := derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j
  let b := derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j
  let r := mapDerivedCategorySquareIso.{u + 2, u + 2, u + 2, u + 2,
    u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
      (OpenScalarSite.restrictScalarsIso (uliftRingHom φ) j)
  let q := (mapDerivedCategorySquareIso.{u + 2, u + 2, u + 2, u + 2,
    u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
      (sfFixedOpenRestriction j φ)).hom
  have hq := Adjunction.mapDerivedCategoryAdjunction_mate
    (openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j)
    (openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)
    (OpenScalarSite.restrictScalarsIso (uliftRingHom φ) j)
    (sfFixedOpenRestriction j φ) (FiniteCompactScalar.fixed_upper_unit φ j)
  have hf : (bz.homEquiv _ _).symm
        (F.map (bx.unit.app K) ≫ q.app ((liftedScalarExtension φ X).obj K)) =
      (OpenScalarSite.scalarOpen (uliftRingHom φ) j).hom.app K := by
    apply (bz.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    exact (FiniteCompactScalar.scalar_unit_of_open_unit a b bx bz r q hq K).symm
  have h := FiniteCompactScalar.fixedOpenScalar_realization_transport φ j K
  rw [← scalarPresentation_eq φ X, ← scalarPresentation_eq φ Z] at h
  change (az.homEquiv _ _).symm
        (I.map (ax.unit.app _) ≫ (sfOpenRestrictionDerived j φ).hom.app _) ≫
      J.map ((scalarPresentation φ X).hom.app K) =
    (scalarExtensionFunctor φ Z).map
        ((FiniteCompactScalar.openRealizationIso A j).hom.app K) ≫
      (scalarPresentation φ Z).hom.app (F.obj K) ≫
      (sfIntrinsicDerivedEquivalence Z B).functor.map
        ((bz.homEquiv _ _).symm (F.map (bx.unit.app K) ≫ q.app _)) ≫
      (FiniteCompactScalar.openRealizationIso B j).inv.app _ at h
  erw [hi, hf] at h
  have hh := congrArg (fun t ↦ t ≫
    (FiniteCompactScalar.openRealizationIso B j).hom.app
      ((liftedScalarExtension φ X).obj K)) h
  simp only [Category.assoc] at hh
  erw [Iso.inv_hom_id_app, Category.comp_id] at hh
  exact hh


end AlgebraicGeometry.ProEtale.CoefficientCompatibility
