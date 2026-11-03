/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.FiniteCoefficientAdjointData

import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOrigin
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.EtaleFiniteStageMateInvertible
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.NormalizedChangeSiteReflection
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarFlatModel
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison

/-! # Invertible normalized comparison for one coefficient arrow

Source: current blueprint reduction-exceptional, Locality and Charts, and the
ordinary closed-support argument in the parent node, proof steps 5--6.
(blueprint: lem-pur-finite-stage-normalized-change).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
attribute [local instance 20000] CommRing.toRing Field.toCommRing DFunLike.toCoeFun
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
namespace AlgebraicGeometry.FiniteCoefficientAdjoints

private def changeOrigin (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (K : (ctf A T).FullSubcategory) :
    Scheme.FixedEtaleOriginWitness T A ⟨K.obj, K.property.plus⟩ where
  complex := ⟨(rnu A T).obj K.obj,
    ProEtale.plus_rightDerivedFunctor_comparisonLowerStar_obj K.property.plus⟩
  iso :=
    have := (ProEtale.DerivedCategory.plusEtaleOrigin_iff K.obj).mp
      K.property.plusEtaleOrigin |>.2
    asIso ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).counit.app K.obj)

private theorem origin_ctf
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (K : (ctf A T).FullSubcategory)
    (w : Scheme.FixedEtaleOriginWitness T A ⟨K.obj, K.property.plus⟩) :
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T w.complex.obj := by
  obtain ⟨L, hL, ⟨e⟩⟩ := K.property.1
  obtain ⟨a, b, ht⟩ := (ctf A T).prop_of_iso e.symm K.property |>.2
  have hLt : Etale.DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} A) T L :=
    ⟨a, b, (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b L).mp ht⟩
  have hLplus := hL.1.1
  let := ProEtale.isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} A) T L hLplus
  let := ProEtale.isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} A) T w.complex.obj w.complex.property
  let d : L ≅ w.complex.obj :=
    asIso ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app L) ≪≫
      (rnu A T).mapIso (e ≪≫ w.iso.symm) ≪≫
      (asIso ((ProEtale.derivedComparisonAdjunction
        (ModuleCat.{u + 1} A) T).unit.app w.complex.obj)).symm
  exact (Etale.DerivedCategory.constructibleFiniteTor
    (ModuleCat.{u + 1} A) T).prop_of_iso d ⟨hL, hLt⟩

private theorem change_etale_scalar_preserves
    {A B : Type (u + 1)} [CommRing A] [Finite A] [CommRing B] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) [IsNoetherian T]
    (K : Etale.DerivedCategoryModule A T)
    (hK : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T K) :
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} B) T
      ((Etale.scalarExtension φ T).obj K) := by
  obtain ⟨hbc, a, b, ht⟩ := hK
  have hc : ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ q).obj K) :=
    fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr (hbc.2 q)
  have ht' := Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
    (ht.mono (min_le_left a b) le_rfl)
  obtain ⟨_, _, _, hcB, htB⟩ := Etale.exists_etaleScalarFlatModel T A B φ
    (min a b) b (min_le_right _ _) ⟨K, hbc.1⟩ hc ht'
  have htB' := Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 htB
  have hz := _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn htB'
  exact ⟨⟨⟨⟨min a b, hz.1⟩, ⟨b, hz.2⟩⟩, fun q ↦
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hcB q)⟩,
    min a b, b, htB'⟩

private theorem change_tensor_preserves
    {A B : Type (u + 1)} [CommRing A] [Finite A] [CommRing B] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) [IsNoetherian T]
    (K : D A T) (hK : ctf A T K) : ctf B T ((tensor φ T).obj K) := by
  let w := changeOrigin A T ⟨K, hK⟩
  have h := ProEtale.DerivedCategory.constructibleFiniteTor_mapDerivedCategory B
    (change_etale_scalar_preserves φ T w.complex.obj (origin_ctf A T ⟨K, hK⟩ w))
  let e := ((tensor φ T).mapIso w.iso).symm ≪≫
    (ProEtale.pbcComparisonReduction T φ).app w.complex.obj
  exact (ctf B T).prop_of_iso e.symm h

private theorem change_tensor_bound
    {A B : Type (u + 1)} [CommRing A] [Finite A] [CommRing B] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) [IsNoetherian T]
    (K : (ctf A T).FullSubcategory)
    (w : Scheme.FixedEtaleOriginWitness T A ⟨K.obj, K.property.plus⟩) :
    DerivedCategory.TStructure.t.plus ((Etale.scalarExtension φ T).obj w.complex.obj) :=
  (change_etale_scalar_preserves φ T w.complex.obj (origin_ctf A T K w)).1.1.1

private def changeOriginFunctor (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) : (ctf A T).FullSubcategory ⥤
      (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T).FullSubcategory where
  obj K := ⟨(changeOrigin A T K).complex.obj, origin_ctf A T K (changeOrigin A T K)⟩
  map a := ObjectProperty.homMk ((rnu A T).map a.hom)

private def changeOriginRealization (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) :
    changeOriginFunctor A T ⋙
        (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T).ι ⋙
        nu A T ≅ (ctf A T).ι :=
  NatIso.ofComponents (fun K ↦ (changeOrigin A T K).iso) (fun a ↦ by
    exact (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).counit.naturality
      a.hom)

private def changeEtaleToPlus (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T).FullSubcategory ⥤
      DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) where
  obj K := ⟨K.obj, K.property.1.1.1⟩
  map a := ObjectProperty.homMk a.hom

private def changeEtaleScalarToPlus
    {A B : Type (u + 1)} [CommRing A] [Finite A] [CommRing B] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) [IsNoetherian T] :
    (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T).FullSubcategory ⥤
      DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) where
  obj K := ⟨(Etale.scalarExtension φ T).obj K.obj,
    (change_etale_scalar_preserves φ T K.obj K.property).1.1.1⟩
  map a := ObjectProperty.homMk ((Etale.scalarExtension φ T).map a.hom)

private def changeEtaleProjection
    {A B : Type (u + 1)} [CommRing A] [Finite A] [CommRing B] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} (c : Compactification f) :
    (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X).ι ⋙
        nu A X ⋙ lower A c ⋙ tensor φ Y ≅
      (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X).ι ⋙
        nu A X ⋙ tensor φ X ⋙ lower B c :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (changeEtaleToPlus A X)
        (ProEtale.compactSupportSiteComparison A c)) (tensor φ Y) ≪≫
    Functor.isoWhiskerLeft
      ((Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X).ι ⋙
        Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
      (ProEtale.pbcComparisonReduction Y φ) ≪≫
    Functor.isoWhiskerLeft
      (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X).ι
      (Functor.isoWhiskerRight
        (Etale.ExceptionalCoefficients.compactSupportIso φ c) (nu B Y)) ≪≫
    Functor.isoWhiskerLeft (changeEtaleScalarToPlus φ X)
      (ProEtale.compactSupportSiteComparison B c).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X).ι
        (ProEtale.pbcComparisonReduction X φ).symm) (lower B c)

private def changeProjection
    {A B : Type (u + 1)} [CommRing A] [Finite A] [CommRing B] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} (c : Compactification f) :
    (ctf A X).ι ⋙ lower A c ⋙ tensor φ Y ≅
      (ctf A X).ι ⋙ tensor φ X ⋙ lower B c :=
  Functor.isoWhiskerRight (changeOriginRealization A X).symm
      (lower A c ⋙ tensor φ Y) ≪≫
    Functor.isoWhiskerLeft (changeOriginFunctor A X) (changeEtaleProjection φ c) ≪≫
    Functor.isoWhiskerRight (changeOriginRealization A X) (tensor φ X ⋙ lower B c)

private theorem changeProjection_normalization
    {A B : Type (u + 1)} [CommRing A] [Finite A] [CommRing B] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} (c : Compactification f) (K : (ctf A X).FullSubcategory)
    (w : Scheme.FixedEtaleOriginWitness X A ⟨K.obj, K.property.plus⟩) :
    (changeProjection φ c).hom.app K =
      projectionAtWitness φ c K w (change_tensor_bound φ X K w) := by
  with_unfolding_all
    let e := (changeOrigin A X K).iso
    obtain ⟨a, ha⟩ := (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map
      w.complex.obj (changeOrigin A X K).complex.obj
      (changeOrigin A X K).complex.property).surjective (w.iso.hom ≫ e.inv)
    let t := changeEtaleProjection φ c
    have hn := t.hom.naturality
      (X := ⟨w.complex.obj, origin_ctf A X K w⟩)
      (Y := (changeOriginFunctor A X).obj K) (ObjectProperty.homMk a)
    change (tensor φ Y).map ((lower A c).map ((nu A X).map a)) ≫
        t.hom.app ((changeOriginFunctor A X).obj K) =
      t.hom.app ⟨w.complex.obj, origin_ctf A X K w⟩ ≫
        (lower B c).map ((tensor φ X).map ((nu A X).map a)) at hn
    change (nu A X).map a = w.iso.hom ≫ e.inv at ha
    erw [ha] at hn
    have hw : projectionAtWitness φ c K w (change_tensor_bound φ X K w) =
        (tensor φ Y).map ((lower A c).map w.iso.inv) ≫
          t.hom.app ⟨w.complex.obj, origin_ctf A X K w⟩ ≫
          (lower B c).map ((tensor φ X).map w.iso.hom) := by
      simp only [projectionAtWitness, t, changeEtaleProjection,
        Etale.ExceptionalCoefficients.compactSupportIso_hom_app,
        Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
        Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Category.assoc]
      rfl
    rw [hw]
    apply (cancel_epi ((tensor φ Y).map ((lower A c).map w.iso.hom))).1
    have hcan : (changeProjection φ c).hom.app K =
        (tensor φ Y).map ((lower A c).map e.inv) ≫
          t.hom.app ((changeOriginFunctor A X).obj K) ≫
          (lower B c).map ((tensor φ X).map e.hom) := by
      simp only [changeProjection, changeOriginRealization, e, t, Iso.trans_hom,
        Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
        Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
        NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app, Functor.comp_map]
    rw [hcan]
    calc
      _ = ((tensor φ Y).map ((lower A c).map (w.iso.hom ≫ e.inv)) ≫
          t.hom.app ((changeOriginFunctor A X).obj K)) ≫
          (lower B c).map ((tensor φ X).map e.hom) := by
        simp only [Functor.map_comp, Category.assoc]
      _ = (t.hom.app ⟨w.complex.obj, origin_ctf A X K w⟩ ≫
          (lower B c).map ((tensor φ X).map (w.iso.hom ≫ e.inv))) ≫
          (lower B c).map ((tensor φ X).map e.hom) := by erw [hn]
      _ = t.hom.app ⟨w.complex.obj, origin_ctf A X K w⟩ ≫
          (lower B c).map ((tensor φ X).map w.iso.hom) := by
        erw [Category.assoc, ← (lower B c).map_comp, ← (tensor φ X).map_comp]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      _ = _ := by
        simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.hom_inv_id]
        erw [(lower A c).map_id, (tensor φ Y).map_id, Category.id_comp]

private theorem change_counit_injective
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} {c : Compactification f} (d : AdjointDatum A c)
    (K : (ctf A X).FullSubcategory) (L : (ctf A Y).FullSubcategory)
    (a b : K.obj ⟶ (upper A c).obj L.obj)
    (h : (lower A c).map a ≫ d.counit L = (lower A c).map b ≫ d.counit L) :
    a = b := by
  with_unfolding_all
    have h' : (d.adjunction.homEquiv K L).symm (ObjectProperty.homMk a) =
        (d.adjunction.homEquiv K L).symm (ObjectProperty.homMk b) := by
      apply ObjectProperty.hom_ext
      exact h
    exact congrArg InducedCategory.Hom.hom ((d.adjunction.homEquiv K L).symm.injective h')

private theorem change_unique
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} {c : Compactification f} {φ : A →+* B}
    {dA : AdjointDatum A c} {dB : AdjointDatum B c}
    (a b : Change φ c dA dB) : a = b := by
  with_unfolding_all
    have hp : a.projection = b.projection := by
      apply Iso.ext
      ext K
      exact (a.projection_normalization K (changeOrigin A X K)).trans
        (b.projection_normalization K (changeOrigin A X K)).symm
    have hm : a.mate = b.mate := by
      apply Iso.ext
      ext K
      apply change_counit_injective dB
        ⟨_, a.tensor_preserves_X _ (dA.upper_preserves K.obj K.property)⟩
        ⟨_, a.tensor_preserves_Y K.obj K.property⟩
      rw [a.counit_equation, b.counit_equation, hp]
    cases a
    cases b
    cases hp
    cases hm
    rfl

private def restrictedProjection :
    restrict (lower A c) dA.lower_preserves ⋙ restrict (tensor φ Y) hY ≅
      restrict (tensor φ X) hX ⋙ restrict (lower B c) dB.lower_preserves :=
  NatIso.ofComponents (fun K ↦ (ctf B Y).isoMk (q.app K)) (fun a ↦ by
    apply ObjectProperty.hom_ext
    exact q.hom.naturality a)

private def normalizedChangeMate :
    restrict (upper A c) dA.upper_preserves ⋙ restrict (tensor φ X) hX ⟶
      restrict (tensor φ Y) hY ⋙ restrict (upper B c) dB.upper_preserves :=
  (mateEquiv dA.adjunction dB.adjunction
    (.mk _ _ _ _ (restrictedProjection φ dA dB hX hY q).inv)).natTrans

private theorem normalizedChangeMate_counit (K : (ctf A Y).FullSubcategory) :
    (lower B c).map ((normalizedChangeMate φ dA dB hX hY q).app K).hom ≫
        dB.counit ⟨(tensor φ Y).obj K.obj, hY K.obj K.property⟩ =
      q.inv.app ⟨(upper A c).obj K.obj, dA.upper_preserves K.obj K.property⟩ ≫
        (tensor φ Y).map (dA.counit K) := by
  exact congrArg InducedCategory.Hom.hom
    (mateEquiv_counit dA.adjunction dB.adjunction
      (.mk _ _ _ _ (restrictedProjection φ dA dB hX hY q).inv) K)

private theorem normalizedChangeMate_unit (K : (ctf A X).FullSubcategory) :
    (tensor φ X).map (dA.unit K) ≫
        ((normalizedChangeMate φ dA dB hX hY q).app
          ⟨(lower A c).obj K.obj, dA.lower_preserves K.obj K.property⟩).hom ≫
        (upper B c).map (q.hom.app K) =
      dB.unit ⟨(tensor φ X).obj K.obj, hX K.obj K.property⟩ := by
  have h := congrArg InducedCategory.Hom.hom
    (unit_mateEquiv dA.adjunction dB.adjunction
      (.mk _ _ _ _ (restrictedProjection φ dA dB hX hY q).inv) K)
  change (tensor φ X).map (dA.unit K) ≫
      ((normalizedChangeMate φ dA dB hX hY q).app
        ⟨(lower A c).obj K.obj, dA.lower_preserves K.obj K.property⟩).hom =
    dB.unit ⟨(tensor φ X).obj K.obj, hX K.obj K.property⟩ ≫
      (upper B c).map (q.inv.app K) at h
  rw [← Category.assoc, h, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [(upper B c).map_id, Category.comp_id]

/-- One coefficient arrow has a unique projection and invertible counit-normalized mate
between the specified finite-stage adjunctions.

Source: current blueprint reduction-exceptional, Locality and Charts; parent
lem-pur-finite-coefficient-adjoint-comparisons, proof steps 5--6.
(blueprint: lem-pur-finite-stage-normalized-change).

Proof: identify the stage rings with positive DVR quotients using stage_ramification.
A bounded flat constructible model stays flat and constructible after coefficient
extension, giving both tensor preservation clauses. The finite-Tor site equivalence
and exact faithful comparison show that every retained bounded etale witness has
finite-Tor amplitude; scalar extension therefore remains bounded below. Open tensor
balancing and the proper direct-image coefficient comparison give an invertible q
on the etale site. Transport it using the specified site/coefficient square; its
value at any retained witness is projectionAtWitness, by naturality and full
faithfulness of comparison. Define b as the transpose of q inverse followed by the
scalar-extended A-counit. On an affine-space projection its invertibility follows
from etaleAffineProjectionCoefficientMate. For a closed immersion, tensor the
injective support sequence with a flat K-flat model of the target coefficient
ring, after restriction of scalars. The K-flat support-comparison theorem supplies
a morphism of distinguished support triangles with middle identity and invertible
open term. Two-out-of-three makes its supported term invertible. The supported
triangle mate-identification theorem identifies that term with the specified b,
using the counit equation and the vanishing of Hom from a supported object to an
open direct image in every shift. Affine factorization, adjoint locality and mate
pasting identify restrictions of b with these two invertible cases; conservative
geometric stalks prove global invertibility. Site comparison transports back to
pro-etale functors with their normalized counits. The counit equation holds by
construction. Transpose the proposed unit equation: naturality of q and the two
triangle identities reduce it to the identity. For uniqueness the tensor bounds
are proofs, q is fixed at every witness (each object has one), and b is fixed by
its transpose. These arguments apply to equal levels, identities, quotient maps,
finite-free extensions, and their mixed composites without assuming flatness. -/
theorem finite_stage_normalized_change
    (k : Type u) [Field k] (p l : ℕ) [CharP k p]
    (hk : Finite k ∨ IsAlgClosed k) (hp : 0 < p)
    [Fact l.Prime] (hlp : l ≠ p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    {s t : Stage l E} (a : Arrow s t) (c : Compactification f) :
    letI := finiteTypeNoetherian k X
    letI := finiteTypeNoetherian k Y
    letI := (finiteTypeMorphismProperties k f).1
    letI := (finiteTypeMorphismProperties k f).2.1
    letI := (finiteTypeMorphismProperties k f).2.2
    ∀ (dA : AdjointDatum s.ring c) (dB : AdjointDatum t.ring c),
      ∃! q : Change a.ringMap c dA dB, True := by
  let := finiteTypeNoetherian k X
  let := finiteTypeNoetherian k Y
  let := (finiteTypeMorphismProperties k f).1
  let := (finiteTypeMorphismProperties k f).2.1
  let := (finiteTypeMorphismProperties k f).2.2
  intro dA dB
  let hX := change_tensor_preserves a.ringMap X
  let hY := change_tensor_preserves a.ringMap Y
  let q := changeProjection a.ringMap c
  let m := normalizedChangeMate a.ringMap dA dB hX hY q
  have hm (K : (ctf s.ring Y).FullSubcategory) : IsIso ((m.app K).hom) := by
    apply normalized_change_site_reflection a.ringMap c dA dB hX hY
      (change_tensor_bound a.ringMap X) q
      (changeProjection_normalization a.ringMap c) K _
      (normalizedChangeMate_counit a.ringMap dA dB hX hY q K)
    exact etale_finite_stage_mate_invertible k p l hk hp hlp E f a c
      ((rnu s.ring Y).obj K.obj) (origin_ctf s.ring Y K (changeOrigin s.ring Y K))
  let b : (ctf s.ring Y).ι ⋙ upper s.ring c ⋙ tensor a.ringMap X ≅
      (ctf s.ring Y).ι ⋙ tensor a.ringMap Y ⋙ upper t.ring c :=
    NatIso.ofComponents (fun K ↦ @asIso _ _ _ _ ((m.app K).hom) (hm K)) (fun h ↦ by
      exact congrArg InducedCategory.Hom.hom (m.naturality h))
  let r : Change a.ringMap c dA dB := {
    tensor_preserves_X := hX
    tensor_preserves_Y := hY
    projection := q
    mate := b
    etale_tensor_bound := change_tensor_bound a.ringMap X
    projection_normalization := changeProjection_normalization a.ringMap c
    counit_equation := normalizedChangeMate_counit a.ringMap dA dB hX hY q
    unit_equation := normalizedChangeMate_unit a.ringMap dA dB hX hY q
  }
  exact ⟨r, trivial, fun y _ ↦ change_unique y r⟩

section FormalChange

variable {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
  {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  {f : X ⟶ Y} {c : Compactification f} (φ : A →+* B)
  (dA : AdjointDatum A c) (dB : AdjointDatum B c)
  (hX : ∀ K, ctf A X K → ctf B X ((tensor φ X).obj K))
  (hY : ∀ K, ctf A Y K → ctf B Y ((tensor φ Y).obj K))
  (q : (ctf A X).ι ⋙ lower A c ⋙ tensor φ Y ≅
    (ctf A X).ι ⋙ tensor φ X ⋙ lower B c)

end FormalChange

-- Preserve the existing unique-existence binder, which is absent from its True predicate.
set_option linter.unusedVariables false in
end AlgebraicGeometry.FiniteCoefficientAdjoints
