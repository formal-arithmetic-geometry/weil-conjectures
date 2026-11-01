/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
public import WeilConjectures.AlgebraicGeometry.MixedBaseChangeOperations
public import WeilConjectures.AlgebraicGeometry.Proper.Etale.ProperEtaleOriginScalarData
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportComparisons
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin

/-!
# Ordinary finite-coefficient compactification comparisons

Source: latest blueprint, det-sf-comp-coherence-cocycle, common-refinement comparison;
finite-reduction proof Step 4 (blueprint: det-sf-comp-coherence-cocycle).

The recorded condensed interface is retained. This specialization uses ordinary modules
and characterizes the comparison on every bounded-below etale origin. Its etale factor
is the canonical common-refinement comparison, not a choice of an isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- Change only the constant-ring direct-image presentation, preserving its section unit.
Source: blueprint compactification formula (blueprint: det-sf-comp-coherence-cocycle). -/
def ordinaryCompactificationModel (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    reductionCompactSupport A c.i c.g ≅ sfIntrinsicCompactSupport c A :=
  Functor.isoWhiskerLeft _ (properOriginPushIso A c.g)

/-- The common-refinement comparison transported at an explicitly identified origin.
Both site comparisons are the specified proper/open ones. The etale comparison is
computed through a common proper refinement and hence agrees with the dense-refinement
normalization. Source: latest blueprint, compactification coherence proof and finite
reduction Step 4 (blueprint: det-sf-comp-coherence-cocycle). -/
def ordinaryCompactificationAtOrigin (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f) (K : proEtaleDerivedCategory X A)
    (L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (e : (finiteCoefficientIntrinsicDerivedComparison X A).obj L.obj ≅ K) :
    (reductionCompactSupport A c.i c.g).obj K ≅
      (reductionCompactSupport A d.i d.g).obj K :=
  (reductionCompactSupport A c.i c.g).mapIso e.symm ≪≫
    (ordinaryCompactificationModel A c).app _ ≪≫
    (FiniteCompactScalar.compactSiteIso A c L).symm ≪≫
    (finiteCoefficientIntrinsicDerivedComparison Y A).mapIso
      ((Etale.rightDerivedLowerShriekOfCompactificationIso
        (ULift.{u + 1, u} A) c d).app L.obj) ≪≫
    FiniteCompactScalar.compactSiteIso A d L ≪≫
    ((ordinaryCompactificationModel A d).app _).symm ≪≫
    (reductionCompactSupport A d.i d.g).mapIso e

private theorem extendFiniteComparison
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F : A ⥤ B) [F.Full] (G H : B ⥤ C) (Q : ObjectProperty B)
    (hw : ∀ K : Q.FullSubcategory, ∃ M : A, Nonempty (F.obj M ≅ K.obj))
    (α : F ⋙ G ≅ F ⋙ H) :
    ∃! t : Q.ι ⋙ G ≅ Q.ι ⋙ H,
      ∀ (K : Q.FullSubcategory) (M : A) (e : F.obj M ≅ K.obj),
        t.app K = G.mapIso e.symm ≪≫ α.app M ≪≫ H.mapIso e := by
  classical
  choose M e using hw
  let e' (K : Q.FullSubcategory) : F.obj (M K) ≅ K.obj := (e K).some
  have hn {U V : A} (f : F.obj U ⟶ F.obj V) :
      G.map f ≫ α.hom.app V = α.hom.app U ≫ H.map f := by
    simpa only [Functor.comp_map, Functor.map_preimage] using
      α.hom.naturality (F.preimage f)
  let t : Q.ι ⋙ G ≅ Q.ι ⋙ H := NatIso.ofComponents
    (fun K ↦ G.mapIso (e' K).symm ≪≫ α.app (M K) ≪≫ H.mapIso (e' K)) (by
      intro K L f
      have h := congrArg
        (fun z ↦ G.map (e' K).inv ≫ z ≫ H.map (e' L).hom)
        (hn ((e' K).hom ≫ f.hom ≫ (e' L).inv))
      simpa only [Functor.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc,
        Iso.map_inv_hom_id, Functor.map_id,
        Category.id_comp, Category.comp_id, Functor.comp_map, ObjectProperty.ι_map, Iso.app_hom,
        Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom] using h)
  have ht (K : Q.FullSubcategory) (N : A) (d : F.obj N ≅ K.obj) :
      t.app K = G.mapIso d.symm ≪≫ α.app N ≪≫ H.mapIso d := by
    apply Iso.ext
    have h := congrArg (fun z ↦ G.map d.inv ≫ z ≫ H.map (e' K).hom)
      (hn (d.hom ≫ (e' K).inv))
    simpa only [t, Iso.app_hom, NatIso.ofComponents_hom_app, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom, Functor.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc,
      Iso.map_inv_hom_id, Functor.map_id,
      Category.id_comp, Category.comp_id] using h
  refine ⟨t, ht, ?_⟩
  intro t' ht'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact congrArg Iso.hom ((ht' K (M K) (e' K)).trans (ht K (M K) (e' K)).symm)

private def compactSiteOnPlus (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (DerivedCategory.Plus.ι ⋙
      Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c) ⋙
          finiteCoefficientIntrinsicDerivedComparison Y A ≅
      (DerivedCategory.Plus.ι ⋙ finiteCoefficientIntrinsicDerivedComparison X A) ⋙
        sfIntrinsicCompactSupport c A :=
  Functor.isoWhiskerLeft _ (FiniteCompactScalar.intrinsicSiteFunctorIso A Y) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _) _ ≪≫
    Functor.isoWhiskerRight
      (compactSupportSiteComparison (ULift.{u + 1, u} A) c).symm _ ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (FiniteCompactScalar.compactRealizationIso A c).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _) _ ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft _ (FiniteCompactScalar.intrinsicSiteFunctorIso A X).symm) _

/-- The uniquely normalized natural comparison on ordinary intrinsic Dctf.
Source: latest blueprint, det-sf-comp-coherence-cocycle, proof by common dense refinement
(blueprint: det-sf-comp-coherence-cocycle).

Proof: bounded intrinsic constructibility over a finite ring has a bounded etale origin.
Transport the two canonical proper/open site comparisons and the etale common-refinement
comparison along such an origin. Full faithfulness of site comparison makes this
independent of the origin and gives naturality for every derived morphism. The proper
unit--square--counit normalization and the open adjunction units identify each transported
refinement leg with its ordinary refinement leg. A common dense refinement therefore
computes this same comparison. Further common dense refinements give independence;
the two adjacent refinement factors cancel to give identity and cocycle. Every object
has an origin, so the displayed normalization determines the natural isomorphism uniquely.
-/
theorem ordinaryCompactificationComparison_existsUnique
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} [QuasiCompact f] (c d : Compactification f) :
    ∃! ρ : (spFiniteConstructibleTor X A).ι ⋙ reductionCompactSupport A c.i c.g ≅
        (spFiniteConstructibleTor X A).ι ⋙ reductionCompactSupport A d.i d.g,
      ∀ (K : spFiniteConstructibleTorCategory X A)
        (L : DerivedCategory.Plus
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
        (e : (finiteCoefficientIntrinsicDerivedComparison X A).obj L.obj ≅ K.obj),
        ρ.app K = ordinaryCompactificationAtOrigin A c d K.obj L e := by
  classical
  let I := DerivedCategory.Plus.ι
    (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
  let V := finiteCoefficientIntrinsicDerivedComparison X A
  let F := I ⋙ V
  let C := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X
  let R := finiteCoefficientIntrinsicRealization X A
  have : R.IsEquivalence := (finiteCoefficientIntrinsicRealization_exact X A).1
  have : (I ⋙ C.mapDerivedCategory).Full := ⟨fun {K L} g ↦ by
    obtain ⟨h, hh⟩ := (bijective_comparisonUpperStar_mapDerivedCategory_map
      K.obj L.obj L.property).2 g
    exact ⟨ObjectProperty.homMk h, hh⟩⟩
  have : ((I ⋙ C.mapDerivedCategory) ⋙ R.mapDerivedCategory).Full := inferInstance
  have : F.Full := Functor.Full.of_iso
    ((Functor.associator I C.mapDerivedCategory R.mapDerivedCategory) ≪≫
      Functor.isoWhiskerLeft I (Functor.mapDerivedCategoryCompIso C R).symm)
  have hw (K : spFiniteConstructibleTorCategory X A) :
      ∃ L : DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))),
        Nonempty (F.obj L ≅ K.obj) := by
    obtain ⟨L, ⟨e⟩⟩ := ((finiteRing_constructibleDerived_origin X A).2.2.1 K.obj).mpr
      ⟨K.property.2.1, K.property.1⟩
    obtain ⟨a, b, _, hv⟩ := L.property.2
    exact ⟨⟨L.obj, a, (DerivedCategory.isGE_iff L.obj a).2
      (fun i hi ↦ hv i (Or.inl hi))⟩, ⟨e⟩⟩
  let α : F ⋙ reductionCompactSupport A c.i c.g ≅
      F ⋙ reductionCompactSupport A d.i d.g :=
    Functor.associator I V _ ≪≫
      Functor.isoWhiskerLeft I (Functor.isoWhiskerLeft V
        (ordinaryCompactificationModel A c)) ≪≫
      (Functor.associator I V _).symm ≪≫
      (compactSiteOnPlus A c).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft I
          (Etale.rightDerivedLowerShriekOfCompactificationIso
            (ULift.{u + 1, u} A) c d)) _ ≪≫
      compactSiteOnPlus A d ≪≫
      Functor.associator I V _ ≪≫
      Functor.isoWhiskerLeft I (Functor.isoWhiskerLeft V
        (ordinaryCompactificationModel A d).symm) ≪≫
      (Functor.associator I V _).symm
  obtain ⟨ρ, hρ, huniq⟩ := extendFiniteComparison F
    (reductionCompactSupport A c.i c.g) (reductionCompactSupport A d.i d.g)
    (spFiniteConstructibleTor X A) hw α
  have hn (K : spFiniteConstructibleTorCategory X A)
      (L : DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
      (e : V.obj L.obj ≅ K.obj) :
      (reductionCompactSupport A c.i c.g).mapIso e.symm ≪≫ α.app L ≪≫
        (reductionCompactSupport A d.i d.g).mapIso e =
      ordinaryCompactificationAtOrigin A c d K.obj L e := by
    apply Iso.ext
    simp [α, compactSiteOnPlus, ordinaryCompactificationAtOrigin,
      FiniteCompactScalar.compactSiteIso, I, V]
  refine ⟨ρ, fun K L e ↦ (hρ K L e).trans (hn K L e), ?_⟩
  intro σ hσ
  exact huniq σ (fun K L e ↦ (hσ K L e).trans (hn K L e).symm)

/-- Select the unique comparison fixed on all origins, rather than a bare existence
witness. Source: latest blueprint, compactification coherence
(blueprint: det-sf-comp-coherence-cocycle). -/
def ordinaryCompactificationComparison (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} [QuasiCompact f] (c d : Compactification f) :
    (spFiniteConstructibleTor X A).ι ⋙ reductionCompactSupport A c.i c.g ≅
      (spFiniteConstructibleTor X A).ι ⋙ reductionCompactSupport A d.i d.g :=
  (ordinaryCompactificationComparison_existsUnique A c d).exists.choose

end AlgebraicGeometry.ProEtale
