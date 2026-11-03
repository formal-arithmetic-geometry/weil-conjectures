/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientTransport
public import WeilConjectures.AlgebraicGeometry.OpenScalarSite.OpenScalarSiteCoherence
public import WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteCompactScalarCoordinates
import all WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteOpenScalarRealizationTransport
import all WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteOpenScalarSiteTransport
import WeilConjectures.AlgebraicGeometry.Open.OpenScalarCounitSquare

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

end AlgebraicGeometry.ProEtale.CoefficientCompatibility

namespace AlgebraicGeometry.ProEtale.CoefficientCompatibility

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
      uliftRingHom, CoefficientScalarRepresentatives.extension, scalarRestriction,
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

end AlgebraicGeometry.ProEtale.CoefficientCompatibility
