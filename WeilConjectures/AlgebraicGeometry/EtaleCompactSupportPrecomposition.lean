/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportGraphDerivedIsoSupplement
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenInterchangeSupplement
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumCompositionCounit
public import WeilConjectures.AlgebraicGeometry.Etale.Support.EtaleSupportSumCompositor
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import all WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumCompositionCounit

/-!
# Finite-torsion unbounded compact supports after exact étale sum extension

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/
sec-the-exceptional-inverse-image-of-a-smooth-morphism-and-base-change/
sk-lem-geo-affine-local/lem-amb-etale-adjoint-locality.proof.md, paragraph 2,
third Hom bijection (blueprint: lem-amb-etale-compact-support-precomposition).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The unique left-adjoint comparison for successive étale restrictions, descended termwise.
Source: `lem-amb-etale-adjoint-locality.proof.md`, paragraph 2, further localization;
node proof step 4 (blueprint: lem-amb-etale-compact-support-precomposition).

It is the mate of the inverse of `upperStarComp`, using the given sum/restriction adjunctions.
The exact-functor derived compositor transports this sheaf mate to the ordinary unbounded
categories. Its definition does not assume a later theorem identifying a sheetwise compositor. -/
noncomputable def etaleCompactSupportSumCompIso
    (A : Type (u + 1)) [CommRing A]
    {V U X : Scheme.{u}} (v : V ⟶ U) (u : U ⟶ X) [Etale v] [Etale u] :
    (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory ⋙
        (etaleLowerShriek (ModuleCat.{u + 1} A) u inferInstance).mapDerivedCategory ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) (v ≫ u) inferInstance).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (Adjunction.leftAdjointCompIso
        (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v inferInstance)
        (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) u inferInstance)
        (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (v ≫ u) inferInstance)
        (upperStarComp (ModuleCat.{u + 1} A) v u).symm)

/-- The exact identity sum extension is identified with the identity by uniqueness of
left adjoints to the canonical identity restriction. Source: the identity clause of
`lem-amb-etale-adjoint-locality.proof.md`, paragraph 2
(blueprint: lem-amb-etale-compact-support-precomposition). -/
noncomputable def etaleCompactSupportIdentityComparison
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    (etaleLowerShriek (ModuleCat.{u + 1} A) (𝟙 X) inferInstance).mapDerivedCategory ≅
      𝟭 (DerivedCategoryModule A X) := by
  exact Functor.mapDerivedCategoryNatIso
      (Adjunction.leftAdjointIdIso
        (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X) inferInstance)
        (upperStarId (ModuleCat.{u + 1} A) X)) ≪≫
    Functor.mapDerivedCategoryIdIso _

private theorem graph_comparison_refinement
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} [IsNoetherian U] [IsNoetherian X]
    (u : U ⟶ X) [Etale u] [IsSeparated u] [QuasiCompact u]
    {c d : Compactification u} (r : c.Refinement d) :
    (rightDerivedLowerShriekOfCompactificationIso A d c).hom ≫
        (canonicalEtaleCompactSupportComparison A u c).hom =
      (canonicalEtaleCompactSupportComparison A u d).hom := by
  let : IsLocallyNoetherian d.Z := LocallyOfFiniteType.isLocallyNoetherian d.g
  let : CompactSpace d.Z := QuasiCompact.compactSpace_of_compactSpace d.g
  rw [unboundedEtaleCompactSupport_refinement_normalization A u r
    (canonicalEtaleCompactSupportNormalization A)]
  simpa only [unboundedEtaleRefinementOpenComparison, Iso.symm_hom, Category.assoc,
    canonicalEtaleCompactSupportNormalization, canonicalEtaleCompactSupportCore,
    etaleLowerShriek, openImmersionLowerShriek] using
    (canonicalEtaleCompactSupportNormalization A).refinement u c d r

private theorem graph_comparison_coherence
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} [IsNoetherian U] [IsNoetherian X]
    (u : U ⟶ X) [Etale u] [IsSeparated u] [QuasiCompact u]
    (c d : Compactification u) :
    (rightDerivedLowerShriekOfCompactificationIso A c d).hom ≫
        (canonicalEtaleCompactSupportComparison A u d).hom =
      (canonicalEtaleCompactSupportComparison A u c).hom := by
  rw [← graph_comparison_refinement A u (Compactification.infSnd c d),
    ← Category.assoc]
  have hc := congrArg Iso.hom
    ((unboundedEtaleCompactSupport_comparison_coherence A u).2 c d (c.inf d))
  simp only [Iso.trans_hom] at hc
  rw [hc]
  exact graph_comparison_refinement A u (Compactification.infFst c d)

private lemma support_compositor_global
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X T : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian T]
    (e : U ⟶ X) (v : X ⟶ T)
    [IsSeparated e] [IsSeparated v] [LocallyOfFiniteType e] [LocallyOfFiniteType v]
    [QuasiCompact e] [QuasiCompact v]
    (c : Compactification e) (d : Compactification v) (k : Compactification (e ≫ v))
    [HasCompactification e] [HasCompactification v] [HasCompactification (e ≫ v)]
    (M : DerivedCategoryModule A U) :
    (Functor.isoWhiskerRight
      (rightDerivedLowerShriekOfCompactificationIso A c (k.ofComp d).restrict) _ ≪≫
      rightDerivedLowerShriekOfCompactificationCompIso A d (k.ofComp d) ≪≫
      rightDerivedLowerShriekOfCompactificationIso A (d.comp (k.ofComp d)) k).hom.app M ≫
        (rightDerivedLowerShriekIso A k).hom.app M =
      (rightDerivedLowerShriekIso A d).hom.app
          ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) v).map
          ((rightDerivedLowerShriekIso A c).hom.app M) ≫
        (unboundedEtaleLowerShriekCompIso A e v).hom.app M := by
  let r := (k.ofComp d).restrict
  have ht : (rightDerivedLowerShriekOfCompactificationIso A c r).hom =
      (rightDerivedLowerShriekIso A c).hom ≫ (rightDerivedLowerShriekIso A r).inv := by
    apply (cancel_mono (rightDerivedLowerShriekIso A r).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    simpa only [rightDerivedLowerShriekIso, Iso.trans_hom] using congrArg Iso.hom
      ((unboundedEtaleCompactSupport_comparison_coherence A e).2
        c r (HasCompactification.compactification e))
  have hk := congrArg (fun t ↦ t.hom.app M)
    ((unboundedEtaleCompactSupport_comparison_coherence A (e ≫ v)).2
      (d.comp (k.ofComp d)) k (HasCompactification.compactification (e ≫ v)))
  have hg := NatTrans.congr_app (unboundedEtaleLowerShriekCompIso_tower A e v d
    (k.ofComp d)) M
  simp only [NatTrans.comp_app, NatTrans.hcomp] at hg
  rw [hg, ← Category.assoc, ← (rightDerivedLowerShriekIso A d).hom.naturality]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  have htM := NatTrans.congr_app ht M
  simp only [NatTrans.comp_app] at htM
  rw [← Functor.map_comp_assoc, ← htM]
  have hk' : (rightDerivedLowerShriekOfCompactificationIso A (d.comp (k.ofComp d)) k).hom.app
      M ≫ (rightDerivedLowerShriekIso A k).hom.app M =
      (rightDerivedLowerShriekIso A (d.comp (k.ofComp d))).hom.app M := by
    simpa only [rightDerivedLowerShriekIso, Iso.trans_hom, NatTrans.comp_app] using hk
  simpa only [Iso.trans_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Category.assoc] using congrArg
      (fun t ↦ (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).map
        ((rightDerivedLowerShriekOfCompactificationIso A c r).hom.app M) ≫
          (rightDerivedLowerShriekOfCompactificationCompIso A d (k.ofComp d)).hom.app M ≫ t)
      hk'

private noncomputable def sumToChosen
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (u : U ⟶ X) [Etale u] [IsSeparated u] [QuasiCompact u]
    [HasCompactification u] :
    (etaleLowerShriek (ModuleCat.{u + 1} A) u inferInstance).mapDerivedCategory ≅
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) u :=
  (canonicalEtaleCompactSupportComparison A u
    (HasCompactification.compactification u)).symm

private theorem chosen_comparison_refl
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] :
    rightDerivedLowerShriekIso A (HasCompactification.compactification f) =
      Iso.refl _ := by
  unfold rightDerivedLowerShriekIso
  exact (unboundedEtaleCompactSupport_comparison_coherence A f).1 _

private theorem sum_compositor_eq
    (A : Type (u + 1)) [CommRing A]
    {V U X : Scheme.{u}} (v : V ⟶ U) (u : U ⟶ X) [Etale v] [Etale u] :
    etaleCompactSupportSumCompIso A v u = derivedEtaleSumCompIso A v u := by
  have hs : Adjunction.leftAdjointCompIso
      (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v inferInstance)
      (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) u inferInstance)
      (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (v ≫ u) inferInstance)
      (upperStarComp (ModuleCat.{u + 1} A) v u).symm =
      etaleSumSheafCompIso A v u := by
    apply Iso.ext
    apply (conjugateEquiv
      (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (v ≫ u) inferInstance)
      ((etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v inferInstance).comp
        (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) u inferInstance))).injective
    rw [Adjunction.leftAdjointCompIso_hom]
    simp only [Adjunction.leftAdjointCompNatTrans, Equiv.apply_symm_apply, Iso.symm_inv]
    symm
    apply conjugate_of_counit
    intro Y
    simpa only [Adjunction.comp_counit_app] using sheaf_composition_counit A v u Y
  simp only [etaleCompactSupportSumCompIso, derivedEtaleSumCompIso, hs]

private theorem sumToChosen_composition
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V U X : Scheme.{u}} [IsNoetherian V] [IsNoetherian U] [IsNoetherian X]
    (v : V ⟶ U) (u : U ⟶ X)
    [Etale v] [Etale u] [IsSeparated v] [IsSeparated u]
    [QuasiCompact v] [QuasiCompact u]
    [HasCompactification v] [HasCompactification u] [HasCompactification (v ≫ u)] :
    NatTrans.hcomp (sumToChosen A v).hom (sumToChosen A u).hom ≫
        (unboundedEtaleLowerShriekCompIso A v u).hom =
      (etaleCompactSupportSumCompIso A v u).hom ≫ (sumToChosen A (v ≫ u)).hom := by
  let a := HasCompactification.compactification v
  let b := HasCompactification.compactification u
  let k := HasCompactification.compactification (v ≫ u)
  have h : (Functor.isoWhiskerRight
      (rightDerivedLowerShriekOfCompactificationIso A a (k.ofComp b).restrict) _ ≪≫
      rightDerivedLowerShriekOfCompactificationCompIso A b (k.ofComp b) ≪≫
      rightDerivedLowerShriekOfCompactificationIso A (b.comp (k.ofComp b)) k).hom =
      (unboundedEtaleLowerShriekCompIso A v u).hom := by
    ext K
    have ht := support_compositor_global A v u a b k K
    dsimp only [a, b, k] at ht
    simp only [chosen_comparison_refl, Iso.refl_hom, NatTrans.id_app,
      Category.id_comp, Category.comp_id] at ht
    erw [CategoryTheory.Functor.map_id, Category.id_comp] at ht
    exact ht
  have ht := etaleSupportSumCompositor A v u a b k
  rw [h, ← sum_compositor_eq] at ht
  apply NatTrans.ext
  funext K
  apply (cancel_mono ((canonicalEtaleCompactSupportComparison A (v ≫ u) k).hom.app K)).1
  have hs := congr_app ht K
  simp only [NatTrans.comp_app, NatTrans.hcomp_app] at hs
  simp only [sumToChosen, Iso.symm_hom, NatTrans.comp_app, NatTrans.hcomp_app,
    Category.assoc]
  rw [hs]
  simp only [Category.assoc]
  erw [(canonicalEtaleCompactSupportComparison A u b).hom.naturality_assoc]
  dsimp only [a, b, k]
  simp only [Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

private theorem chosen_copy
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f f' : X ⟶ Y}
    [HasCompactification f] [HasCompactification f']
    [QuasiCompact f] [QuasiCompact f'] (h : f = f')
    (c : Compactification f') :
    (rightDerivedLowerShriekIso A (c.copy h)).hom ≫
        (unboundedEtaleLowerShriekCongr A h).hom =
      (rightDerivedLowerShriekIso A c).hom := by
  cases h
  simp only [unboundedEtaleLowerShriekCongr, Iso.refl_hom, Category.comp_id]
  rfl

private theorem chosen_copy_inv
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f f' : X ⟶ Y}
    [HasCompactification f] [HasCompactification f']
    [QuasiCompact f] [QuasiCompact f'] (h : f = f')
    (c : Compactification f') (K : DerivedCategoryModule A X) :
    (unboundedEtaleLowerShriekCongr A h).hom.app K ≫
        (rightDerivedLowerShriekIso A c).inv.app K =
      (rightDerivedLowerShriekIso A (c.copy h)).inv.app K := by
  apply (cancel_epi ((rightDerivedLowerShriekIso A (c.copy h)).hom.app K)).1
  rw [← Category.assoc, ← NatTrans.comp_app, chosen_copy, Iso.hom_inv_id_app,
    Iso.hom_inv_id_app]

private theorem sumToChosen_identity
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) [IsNoetherian X] :
    (sumToChosen A (𝟙 X)).hom ≫ (unboundedEtaleLowerShriekId A X).hom =
      (etaleCompactSupportIdentityComparison A X).hom := by
  let c := Compactification.ofIsProper (𝟙 X)
  have h := graph_comparison_coherence A (𝟙 X) c
    (HasCompactification.compactification (𝟙 X))
  have hid : canonicalEtaleCompactSupportComparison A (𝟙 X) c =
      identityEtaleCompactSupportComparison A X :=
    (canonicalEtaleCompactSupportNormalization A).identity X
  have hi : (rightDerivedLowerShriekIso A c).inv ≫
      (identityEtaleCompactSupportComparison A X).hom =
      (canonicalEtaleCompactSupportComparison A (𝟙 X)
        (HasCompactification.compactification (𝟙 X))).hom := by
    unfold rightDerivedLowerShriekIso
    rw [← hid, ← h, Iso.inv_hom_id_assoc]
  simp only [sumToChosen, unboundedEtaleLowerShriekId,
    etaleCompactSupportIdentityComparison, Iso.trans_hom, Iso.symm_hom]
  rw [reassoc_of% hi, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Etale
