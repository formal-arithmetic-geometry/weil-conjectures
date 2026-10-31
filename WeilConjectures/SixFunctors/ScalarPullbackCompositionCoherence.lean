/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenScalarTensorData
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison
import all WeilConjectures.AlgebraicGeometry.KFlatScalarComparisonNormalization
import all WeilConjectures.SecSmoothPurity.OrdinaryRestrictionPullbackSquare
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedPullbackCoherence
import all WeilConjectures.AlgebraicGeometry.ProEtaleCanonicalDerivedPullbackNormalization

/-! # Geometric composition of the scalar/pullback comparison

Source: Stacks Project, Tag 0D6D; the geometric composition clause of
lem-sfb-kflat-scalar-comparison-normalization.
(blueprint: lem-sf-scalar-pullback-composition-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
attribute [local instance 100000] proEtaleRingModules_hasDerivedCategory
attribute [local instance 200000] SheafOfModules.instAbelian
private noncomputable instance (priority := 200000) fixedStalk (T : Scheme.{u}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1,
    u + 1, u + 2, u + 1} _

namespace AlgebraicGeometry.ProEtale.OpenScalarTensor

private theorem ordinary_compositor (A : Type u) [CommRing A]
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) (r : Z ⟶ Y) :
    ordinaryComp j r A = StrictTower.moduleGComp (ULift.{u + 1, u} A) j r := by
  have hn (T V : Scheme.{u}) (f : T ⟶ V) :
      normalizedAdj f A = proEtaleConstantRingAdjunction A f := by
    exact (normalizedAdj_eq f A _ (moduleAdjunction_normalized f _ _ _)).symm
  have hd : directComp j r A =
      StrictTower.moduleRComp (ULift.{u + 1, u} A) j r := by
    apply (StrictTower.moduleRComp_existsUnique (ULift.{u + 1, u} A) j r).unique
    · unfold directComp
      intro N U x
      exact (constantData j r A).hd N U x
    · exact Classical.choose_spec
        (StrictTower.moduleRComp_existsUnique (ULift.{u + 1, u} A) j r) |>.1
  rw [ordinaryComp_eq, hn, hn, hn, hd]
  rfl

private theorem derived_compositor (A : Type u) [CommRing A]
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) (r : Z ⟶ Y) :
    proEtaleConstantRingPullbackComposition j r A =
      SheafOfModules.ScalarPullback.compositionDerived.{u + 2, u + 2, u + 1}
        (A := proEtaleRingModules Y (proEtaleConstantRing Y A))
        (B := proEtaleRingModules Z (proEtaleConstantRing Z A))
        (C := proEtaleRingModules X (proEtaleConstantRing X A))
        (proEtaleConstantRingPullback A r) (proEtaleConstantRingPullback A j)
        (proEtaleConstantRingPullback A (j ≫ r))
        (StrictTower.moduleGComp (ULift.{u + 1, u} A) j r).symm := by
  apply (Equiv.injective (show _ ≃ _ from ⟨Iso.symm, Iso.symm,
    Iso.symm_symm_eq, Iso.symm_symm_eq⟩))
  dsimp only [Equiv.coe_fn_mk]
  rw [constantComparison_eq, ordinary_compositor]
  have hs : Functor.mapDerivedCategoryNatIso
      (StrictTower.moduleGComp (ULift.{u + 1, u} A) j r).symm =
      (Functor.mapDerivedCategoryNatIso
        (StrictTower.moduleGComp (ULift.{u + 1, u} A) j r)).symm :=
    Iso.ext (Functor.mapDerivedCategoryNatIso_symm _)
  simp only [SheafOfModules.ScalarPullback.compositionDerived, Iso.trans_symm,
    hs, Iso.symm_symm_eq]

private theorem published_composition {A B : Type u} [CommRing A] [CommRing B]
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) (r : Z ⟶ Y) (φ : A →+* B)
    (L : proEtaleDerivedCategory Y A) :
    (scalarExtension φ X).map
        ((proEtaleConstantRingPullbackComposition j r A).hom.app L) ≫
      (tensorPullbackIso φ (j ≫ r)).inv.app L =
    (tensorPullbackIso φ j).inv.app ((constantPullback (A := A) r).obj L) ≫
      (constantPullback (A := B) j).map ((tensorPullbackIso φ r).inv.app L) ≫
      (proEtaleConstantRingPullbackComposition j r B).hom.app ((scalarExtension φ Y).obj L) := by
  let q {T V : Scheme.{u}} (f : T ⟶ V) :=
    @asIso _ _ _ _ (ordinaryRestrictionComparison φ f)
      (proEtaleRingRestrictionPullbackInv_isIso _ _ _ _ _ _ _ _ _ _)
  let c (R : Type u) [CommRing R] :=
    (StrictTower.moduleGComp (ULift.{u + 1, u} R) j r).symm
  have ho (N : proEtaleRingModules Y (proEtaleConstantRing Y B)) :
      (c A).hom.app ((ordinaryScalarRestriction φ Y).obj N) ≫ (q (j ≫ r)).hom.app N =
        (ordinaryConstantPullback A j).map ((q r).hom.app N) ≫
          (q j).hom.app ((ordinaryConstantPullback B r).obj N) ≫
          (ordinaryScalarRestriction φ X).map ((c B).hom.app N) := by
    apply (cancel_epi ((c A).inv.app ((ordinaryScalarRestriction φ Y).obj N))).1
    simp only [Iso.inv_hom_id_app_assoc]
    erw [reassoc_of% (comparison_comp φ j r N)]
    simp only [c, q, asIso_hom, Iso.symm_hom, ← (ordinaryScalarRestriction φ X).map_comp,
      Iso.hom_inv_id_app]
    rw [(ordinaryScalarRestriction φ X).map_id, Category.comp_id]
  have hd := SheafOfModules.ScalarPullback.derived_composition_square.{u + 2, u + 2, u + 1}
    (A₀ := proEtaleRingModules Y (proEtaleConstantRing Y A))
    (A₁ := proEtaleRingModules Z (proEtaleConstantRing Z A))
    (A₂ := proEtaleRingModules X (proEtaleConstantRing X A))
    (B₀ := proEtaleRingModules Y (proEtaleConstantRing Y B))
    (B₁ := proEtaleRingModules Z (proEtaleConstantRing Z B))
    (B₂ := proEtaleRingModules X (proEtaleConstantRing X B))
    (ordinaryScalarRestriction φ Y) (ordinaryScalarRestriction φ Z)
    (ordinaryScalarRestriction φ X)
    (ordinaryConstantPullback A r) (ordinaryConstantPullback B r)
    (ordinaryConstantPullback A j) (ordinaryConstantPullback B j)
    (ordinaryConstantPullback A (j ≫ r)) (ordinaryConstantPullback B (j ≫ r))
    (c A) (c B) (q r) (q j) (q (j ≫ r)) ho
  have hm := SheafOfModules.ScalarPullback.mate_composition_square
    (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := Y) φ))
    (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := Z) φ))
    (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := X) φ))
    (proEtaleConstantRingPullbackComposition j r A)
    (proEtaleConstantRingPullbackComposition j r B)
    (Functor.mapDerivedCategorySquareIso (q r)).hom
    (Functor.mapDerivedCategorySquareIso (q j)).hom
    (Functor.mapDerivedCategorySquareIso (q (j ≫ r))).hom
    (by intro N; simpa only [derived_compositor, c, ordinaryConstantPullback,
      StrictTower.modulePullback, StrictTower.constantRingIso, proEtaleConstantRingPullback,
      proEtaleConstantRingComparison, proEtaleCoefficientInverseImageMap,
      proEtaleConstantRingDerivedPullback, ordinaryScalarRestriction,
      StrictTower.coefficients, proEtaleConstantRing] using hd N) L
  apply (cancel_mono ((proEtaleConstantRingPullbackComposition j r B).inv.app
    ((scalarExtension φ Y).obj L))).1
  simp only [Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id]
  simpa only [tensorPullbackIso, proEtaleReductionPullbackIso,
    proEtaleReductionPullbackInv, proEtaleRingRestrictionDerivedPullback,
    SheafOfModules.ScalarPullback.mate, q, ordinaryRestrictionComparison,
    Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, NatTrans.comp_app, ← Functor.mapDerivedCategoryNatIso_symm,
    Iso.symm_symm_eq, asIso_hom, Category.assoc, TwoSquare.mk, TwoSquare.natTrans,
    ordinaryConstantPullback, StrictTower.modulePullback, StrictTower.constantRingIso,
    proEtaleConstantRingPullback, proEtaleConstantRingComparison,
    proEtaleCoefficientInverseImageMap, StrictTower.coefficients, proEtaleConstantRing,
    ordinaryScalarRestriction, scalarExtension, constantPullback,
    proEtaleRingDerivedPullback, proEtaleConstantRingDerivedPullback] using hm

/-- Inverse lambda respects the canonical compositor for two geometric pullbacks.
Source: Stacks Project, Tag 0D6D; geometric composition in
lem-sfb-kflat-scalar-comparison-normalization
(blueprint: lem-sf-scalar-pullback-composition-coherence).

Proof: the ordinary pullback/restriction squares are identity maps on underlying
sections. Pasting two squares gives the square for the composite, conjugated by
the ordinary pullback compositors: the two maps preserve each section and its
coefficient action. Exact termwise localization preserves this equation and its
compositors. The composition law for adjunction mates therefore identifies the
two scalar/pullback comparisons, with their normalized scalar adjunctions.
The canonical derived pullback compositor has precisely this localization
normalization on flat-term K-flat representatives. Its uniqueness identifies it
with the compositor obtained by pasting. Transport by scalarIso cancels the
intermediate scalar coordinate changes; naturality moves the outer changes
through the compositors. This gives the displayed equation for all L. The
argument needs neither openness nor flatness, and includes identity morphisms
and the empty scheme. -/
theorem scalarPullbackCompositionCoherence (m : Models.{u})
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z Y : Scheme.{u}} (j : X ⟶ Z) (r : Z ⟶ Y)
    (L : proEtaleDerivedCategory Y A) :
    (scalar m φ X).map ((proEtaleConstantRingPullbackComposition j r A).hom.app L) ≫
        (lambda m φ (j ≫ r)).inv.app L =
      (lambda m φ j).inv.app ((constantPullback (A := A) r).obj L) ≫
        (constantPullback (A := B) j).map ((lambda m φ r).inv.app L) ≫
        (proEtaleConstantRingPullbackComposition j r B).hom.app ((scalar m φ Y).obj L) := by
  have h := published_composition j r φ L
  simp only [lambda, Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_inv, Functor.map_comp, Category.assoc]
  have hx := (scalarIso m φ X).hom.naturality
    ((proEtaleConstantRingPullbackComposition j r A).hom.app L)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hx
  erw [reassoc_of% hx, reassoc_of% h]
  have hn := (proEtaleConstantRingPullbackComposition j r B).hom.naturality
    ((scalarIso m φ Y).inv.app L)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  erw [← hn]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc]

end AlgebraicGeometry.ProEtale.OpenScalarTensor
