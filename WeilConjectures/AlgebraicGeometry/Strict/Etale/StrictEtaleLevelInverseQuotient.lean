/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleLevelInverseTransport
import all WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleInverseTensorCoherence
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageExact

/-! # Quotients of finite inverse-image coefficient transport

Source: Zheng, Construction 5.15, Lemma 5.16 and Proposition 2.29(2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

attribute [local irreducible] siteCoefficientTensorAdj coefficientQuotientSheaf
  coefficientQuotientMap CategoryTheory.constantSheaf
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

private abbrev sets (T : Scheme.{u}) (R : Sheaf T.smallEtaleTopology CommRingCat.{u + 1}) :=
  SheafOfModules.toSheaf.{u + 1}
    ((sheafCompose T.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⋙
    sheafCompose T.smallEtaleTopology (forget AddCommGrpCat.{u + 1})

private def insert {T : Scheme.{u}}
    {R S : Sheaf T.smallEtaleTopology CommRingCat.{u + 1}} (a : R ⟶ S)
    (M : SheafOfModules.{u + 1}
      ((sheafCompose T.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :=
  (sheafCompose T.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).map
    (siteTensorUnitUnderlying.{u + 1, u, u + 1} a M)

private theorem insert_naturality {T : Scheme.{u}}
    {R S : Sheaf T.smallEtaleTopology CommRingCat.{u + 1}} (a : R ⟶ S)
    {M N : SheafOfModules.{u + 1}
      ((sheafCompose T.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)}
    (f : M ⟶ N) :
    (sets T R).map f ≫ insert a N =
      insert a M ≫ (sets T S).map ((siteCoefficientTensor a).map f) := by
  let F := sheafCompose T.smallEtaleTopology (forget AddCommGrpCat.{u + 1})
  change F.map ((toSheaf.{u + 1} _).map f) ≫
      F.map (siteTensorUnitUnderlying.{u + 1, u, u + 1} a N) =
    F.map (siteTensorUnitUnderlying.{u + 1, u, u + 1} a M) ≫ F.map ((toSheaf.{u + 1} _).map
      ((siteCoefficientTensor a).map f))
  rw [← F.map_comp, ← F.map_comp]
  apply congrArg F.map
  have hu := congrArg (toSheaf.{u + 1}
    ((sheafCompose T.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)).map
    ((siteCoefficientTensorAdj.{u + 1, u, u + 1} a).unit.naturality f)
  simp only [Functor.map_comp, Functor.comp_map, Functor.id_map] at hu
  have hq := (siteScalarUnderlyingIso.{u + 1, u, u + 1} a).hom.naturality
    ((siteCoefficientTensor a).map f)
  dsimp only [Functor.comp_map] at hq
  dsimp only [siteTensorUnitUnderlying]
  simp only [Category.assoc]
  rw [reassoc_of% hu, hq]

private def scalarUnderlying {T : Scheme.{u}}
    {R S : Sheaf T.smallEtaleTopology CommRingCat.{u + 1}} (a : R ⟶ S) :=
  Functor.isoWhiskerRight (siteScalarUnderlyingIso.{u + 1, u, u + 1} a)
    (sheafCompose T.smallEtaleTopology (forget AddCommGrpCat.{u + 1}))

private theorem insert_transpose_iso {T : Scheme.{u}}
    {R S : Sheaf T.smallEtaleTopology CommRingCat.{u + 1}} (a : R ⟶ S)
    (M : SheafOfModules.{u + 1}
      ((sheafCompose T.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (N : SheafOfModules.{u + 1}
      ((sheafCompose T.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (f : (siteCoefficientTensor.{u + 1, u, u + 1} a).obj M ⟶ N) :
    (sets T R).map ((siteCoefficientTensorAdj.{u + 1, u, u + 1} a).homEquiv M N f) ≫
        (scalarUnderlying a).hom.app N = insert a M ≫ (sets T S).map f := by
  simpa only [insert, scalarUnderlying, sets, Functor.comp_map,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    siteTensorUnitUnderlying, Functor.map_comp, Category.assoc] using
    transpose_underlying (siteCoefficientTensorAdj.{u + 1, u, u + 1} a) (sets T R) (sets T S)
      (scalarUnderlying a) M N f

section Quotient
variable {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O O' ell mu phi index}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {SA : StrictEtaleCompactSupport O ell c} {SB : StrictEtaleCompactSupport O' mu c}
    {TX : StrictEtaleCoefficientTransport a X SA.PX SB.PX}
    {TZ : StrictEtaleCoefficientTransport a c.Z SA.PZ SB.PZ}
    (qX : StrictEtaleTransportQuotient TX) (qZ : StrictEtaleTransportQuotient TZ)
    (finite : ∀ n, StrictEtaleLevelInverseTransport TX TZ SA.openImage SB.openImage
      SA.openDerived.level SB.openDerived.level n)

private theorem finite_insertion (n : ℕ) (M : strictEtaleLevel c.Z O ell (index n)) :
    (Scheme.etaleSetPullback c.i).map (insert (a.sheaf c.Z n) M) ≫
        (SB.openImage.lift n).moduleUnderlying.inv.app _ ≫
        (coefficientUnderlying (J := X.smallEtaleTopology) O' mu n).map
          ((finite n).ordinary.hom.app M) =
      (SA.openImage.lift (index n)).moduleUnderlying.inv.app M ≫
        insert (a.sheaf X n) ((SA.openImage.lift (index n)).modules.obj M) := by
  apply (cancel_epi ((SA.openImage.lift (index n)).moduleUnderlying.hom.app M)).1
  apply (cancel_mono
    ((coefficientUnderlying (J := X.smallEtaleTopology) O' mu n).map
      ((finite n).ordinary.inv.app M) ≫
        (SB.openImage.lift n).moduleUnderlying.hom.app _)).1
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [(coefficientUnderlying (J := X.smallEtaleTopology) O' mu n).map_id]
  simp only [Category.id_comp, Iso.hom_inv_id_app_assoc,
    Iso.inv_hom_id_app]
  exact (finite n).unit M |>.symm

set_option maxHeartbeats 1000000 in
-- Three nested transposes expose concrete underlying sheaf functors.
private theorem mixed_insertion_ext {m n : ℕ} (h : n ≤ m)
    (M : strictEtaleLevel c.Z O ell (index m)) (N : strictEtaleLevel X O' mu n)
    (v w : (SB.openImage.lift n).modules.obj
      ((siteCoefficientTensor (a.sheaf c.Z n)).obj
        ((coefficientTensor (J := c.Z.smallEtaleTopology) (O := O) (ell := ell)
          (index.monotone h)).obj M)) ⟶ N)
    (he : (Scheme.etaleSetPullback c.i).map
        (insert (coefficientQuotientMap (J := c.Z.smallEtaleTopology) O ell
          (index.monotone h)) M) ≫
      (Scheme.etaleSetPullback c.i).map
        (insert (a.sheaf c.Z n) _) ≫
      (SB.openImage.lift n).moduleUnderlying.inv.app _ ≫
      (coefficientUnderlying (J := X.smallEtaleTopology) O' mu n).map v =
      (Scheme.etaleSetPullback c.i).map
        (insert (coefficientQuotientMap (J := c.Z.smallEtaleTopology) O ell
          (index.monotone h)) M) ≫
      (Scheme.etaleSetPullback c.i).map
        (insert (a.sheaf c.Z n) _) ≫
      (SB.openImage.lift n).moduleUnderlying.inv.app _ ≫
      (coefficientUnderlying (J := X.smallEtaleTopology) O' mu n).map w) : v = w := by
  apply ((SB.openImage.levelAdj n).homEquiv _ N).injective
  apply ((siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf c.Z n)).homEquiv _ _).injective
  apply ((coefficientTensorAdj.{u + 1, u, u + 1} (J := c.Z.smallEtaleTopology) (O := O) (ell := ell)
    (index.monotone h)).homEquiv M _).injective
  apply (coefficientUnderlying (J := c.Z.smallEtaleTopology) O ell (index m)).map_injective
  let R := (SB.openImage.right n).obj N
  let RT := (SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose c.Z.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (a.sheaf c.Z n))).obj R
  apply (cancel_mono
    ((scalarUnderlying (coefficientQuotientMap (J := c.Z.smallEtaleTopology)
      O ell (index.monotone h))).hom.app RT ≫
      (scalarUnderlying (a.sheaf c.Z n)).hom.app R ≫
      (SB.openImage.rightUnderlying n).hom.app N)).1
  have hv₁ := insert_transpose_iso
    (coefficientQuotientMap (J := c.Z.smallEtaleTopology) O ell (index.monotone h)) M RT
    ((siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf c.Z n)).homEquiv _ _
      ((SB.openImage.levelAdj n).homEquiv _ _ v))
  have hw₁ := insert_transpose_iso
    (coefficientQuotientMap (J := c.Z.smallEtaleTopology) O ell (index.monotone h)) M RT
    ((siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf c.Z n)).homEquiv _ _
      ((SB.openImage.levelAdj n).homEquiv _ _ w))
  have hv₂ := insert_transpose_iso (a.sheaf c.Z n) _ R
    ((SB.openImage.levelAdj n).homEquiv _ _ v)
  have hw₂ := insert_transpose_iso (a.sheaf c.Z n) _ R
    ((SB.openImage.levelAdj n).homEquiv _ _ w)
  erw [reassoc_of% hv₁, reassoc_of% hw₁, reassoc_of% hv₂, reassoc_of% hw₂]
  have hv := SB.openImage.levelTranspose n _ N v
  have hw := SB.openImage.levelTranspose n _ N w
  dsimp only [coefficientUnderlying, Functor.comp_map] at hv hw
  erw [hv, hw]
  erw [← (strictEtaleSetAdjunction c.i).homEquiv_naturality_left,
    ← (strictEtaleSetAdjunction c.i).homEquiv_naturality_left,
    ← (strictEtaleSetAdjunction c.i).homEquiv_naturality_left,
    ← (strictEtaleSetAdjunction c.i).homEquiv_naturality_left]
  exact congrArg ((strictEtaleSetAdjunction c.i).homEquiv _ _) he

private theorem quotient_insertion {m n : ℕ} (h : n ≤ m)
    (M : strictEtaleLevel c.Z O ell (index m)) :
    insert (coefficientQuotientMap (J := c.Z.smallEtaleTopology) O ell
        (index.monotone h)) M ≫
      insert (a.sheaf c.Z n) _ ≫
      (coefficientUnderlying (J := c.Z.smallEtaleTopology) O' mu n).map
        ((qZ.val.1 h).hom.app M) =
    insert (a.sheaf c.Z m) M ≫
      insert (coefficientQuotientMap (J := c.Z.smallEtaleTopology) O' mu h) _ := by
  have hq := congrArg
    ((sheafCompose c.Z.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).map)
    (qZ.property.1 h M)
  simpa only [insert, coefficientUnderlying, Functor.comp_map, Functor.map_comp,
    Category.assoc] using hq

private theorem quotient_insert_eq {T : Scheme.{u}} {O : Type (u + 1)}
    [CommRing O] {ell : O} {m n : ℕ} (h : n ≤ m)
    (M : strictEtaleLevel T O ell m) :
    insert (coefficientQuotientMap (J := T.smallEtaleTopology) O ell h) M =
      insertion T.smallEtaleTopology h M := by
  simp only [insert, insertion, underlying, tensorAdj, coefficientTensorAdj,
    coefficientRestrictionUnderlying, siteTensorUnitUnderlying, coefficientUnderlying,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.comp_map,
    Functor.map_comp]

private theorem geometric_insertion {T S : Scheme.{u}} {O : Type (u + 1)} [CommRing O]
    {ell : O} {g : T ⟶ S}
    (PW : StrictEtaleEvaluation S O ell) (PV : StrictEtaleEvaluation T O ell)
    (A : StrictEtaleOrdinaryImage O ell g)
    (E : CoefficientSystemDerivedImage.{u + 1, u, u + 1, u, u + 1, u + 2}
      O ell _ _ _ A PW PV)
    {m n : ℕ} (h : n ≤ m) (M : strictEtaleLevel S O ell m) :
    (Scheme.etaleSetPullback g).map
        (insert (coefficientQuotientMap (J := S.smallEtaleTopology) O ell h) M) ≫
      (A.lift n).moduleUnderlying.inv.app _ ≫
      (coefficientUnderlying (J := T.smallEtaleTopology) O ell n).map
        ((E.tensor h).hom.app M) =
    (A.lift m).moduleUnderlying.inv.app M ≫
      insert (coefficientQuotientMap (J := T.smallEtaleTopology) O ell h)
        ((A.lift m).modules.obj M) := by
  rw [quotient_insert_eq, quotient_insert_eq]
  simpa only [tensor, underlying] using tensor_insertion PW PV A E h M

set_option maxHeartbeats 1200000 in
-- The insertion square contains several concrete scalar and geometric functors.
private theorem ordinary_quotient {m n : ℕ} (h : n ≤ m)
    (M : strictEtaleLevel c.Z O ell (index m)) :
    (SB.openImage.lift n).modules.map ((qZ.val.1 h).hom.app M) ≫
        (SB.openDerived.tensor h).hom.app
          ((siteCoefficientTensor (a.sheaf c.Z m)).obj M) ≫
        (coefficientTensor (J := X.smallEtaleTopology) (O := O') (ell := mu) h).map
          ((finite m).ordinary.hom.app M) =
      (finite n).ordinary.hom.app
          ((coefficientTensor (J := c.Z.smallEtaleTopology) (O := O) (ell := ell)
            (index.monotone h)).obj M) ≫
        (siteCoefficientTensor (a.sheaf X n)).map
          ((SA.openDerived.tensor (index.monotone h)).hom.app M) ≫
        (qX.val.1 h).hom.app ((SA.openImage.lift (index m)).modules.obj M) := by
  apply mixed_insertion_ext (a := a) (SB := SB) h M
  have hn := (SB.openImage.lift n).moduleUnderlying.inv.naturality
    ((qZ.val.1 h).hom.app M)
  have hi := insert_naturality
    (coefficientQuotientMap (J := X.smallEtaleTopology) O' mu h)
    ((finite m).ordinary.hom.app M)
  have hj := insert_naturality (a.sheaf X n)
    ((SA.openDerived.tensor (index.monotone h)).hom.app M)
  have hgB := geometric_insertion SB.PZ SB.PX SB.openImage SB.openDerived h
    ((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf c.Z m)).obj M)
  have hgA := geometric_insertion SA.PZ SA.PX SA.openImage SA.openDerived
    (index.monotone h) M
  have hfN := finite_insertion finite n
    ((coefficientTensor.{u + 1, u, u + 1} (J := c.Z.smallEtaleTopology)
      (O := O) (ell := ell) (index.monotone h)).obj M)
  have hfM := finite_insertion finite m M
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.map_comp]
  conv_lhs =>
    erw [← reassoc_of% hn, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
      Category.assoc (insert _ M), quotient_insertion qZ h M]
    erw [Functor.map_comp, Category.assoc,
      reassoc_of% hgB,
      ← hi, reassoc_of% hfM]
  conv_rhs =>
    arg 2
    erw [reassoc_of% hfN]
    arg 2
    erw [← reassoc_of% hj]
  conv_rhs => erw [reassoc_of% hgA]
  have hq := congrArg
    ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).map)
    (qX.property.1 h ((SA.openImage.lift (index m)).modules.obj M))
  simpa only [insert, sets, coefficientUnderlying, Functor.comp_map, Functor.comp_obj,
    coefficientTensor, Functor.map_comp, Category.assoc] using
    congrArg (fun z ↦ (SA.openImage.lift (index m)).moduleUnderlying.inv.app M ≫ z)
      hq.symm

section ScalarPreservation
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (T : GrothendieckTopology C)
    [T.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [T.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [HasSheafify T AddCommGrpCat.{u + 1}] [HasWeakSheafify T CommRingCat.{u + 1}]
    [HasWeakSheafify T (Type (u + 1))]
    [T.HasSheafCompose (CategoryTheory.forget CommRingCat.{u + 1})]
    [T.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1})]

private def identityLift
    (R : Sheaf T CommRingCat.{u + 1}) :
    AlgebraicInverseImage (𝟭 (Sheaf T (Type (u + 1)))) R R where
  ringUnderlying := Iso.refl _
  ringAdd := fun _ _ _ _ h ↦ h
  ringMul := fun _ _ _ _ h ↦ h
  ringZero := fun _ _ h ↦ h
  ringOne := fun _ _ h ↦ h
  modules := 𝟭 _
  moduleUnderlying := Iso.refl _
  moduleAdd := fun _ _ _ _ _ h ↦ h
  moduleZero := fun _ _ _ h ↦ h
  moduleSMul := fun _ _ _ _ _ h ↦ h

omit [HasWeakSheafify T (Type (u + 1))]
    [T.HasSheafCompose (CategoryTheory.forget CommRingCat.{u + 1})]
    [T.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1})] in
private theorem scalar_good_map
    {R S : Sheaf T CommRingCat.{u + 1}} (b : R ⟶ S)
    (P : CochainComplex (SheafOfModules.{u + 1}
      ((sheafCompose T (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ℤ)
    (hk : P.IsKFlatIndependentCoefficients)
    (hf : ∀ i : ℤ, IsFlatOnSite (J := T) (R := R) (P.X i)) :
    CochainComplex.IsKFlatIndependentCoefficients
      (((siteCoefficientTensor.{u + 1, u, u + 1} b).mapHomologicalComplex (.up ℤ)).obj P) ∧
    ∀ i : ℤ, IsFlatOnSite (J := T) (R := S)
      ((((siteCoefficientTensor.{u + 1, u, u + 1} b).mapHomologicalComplex
        (.up ℤ)).obj P).X i) := by
  exact isKFlat_ringedToposPullback (𝟭 _) (𝟭 _) Adjunction.id (identityLift T R) b
    (siteCoefficientTensor.{u + 1, u, u + 1} b) (fun _ ↦ rfl)
    (by intro M N f; simp only [eqToHom_refl, Category.id_comp, Category.comp_id]; rfl)
    P hk hf

end ScalarPreservation

set_option maxHeartbeats 1200000 in
-- Specializing preservation checks the concrete coefficient quotient categories.
private theorem transport_good (T : Scheme.{u}) (n : ℕ)
    (P : CochainComplex (strictEtaleLevel T O ell (index n)) ℤ)
    (hk : P.IsKFlatIndependentCoefficients)
    (hf : ∀ i : ℤ, IsFlatOnSite (J := T.smallEtaleTopology)
      (R := coefficientQuotientSheaf (J := T.smallEtaleTopology) O ell (index n)) (P.X i)) :
    CochainComplex.IsKFlatIndependentCoefficients
      (((siteCoefficientTensor (a.sheaf T n)).mapHomologicalComplex (.up ℤ)).obj P) ∧
    ∀ i : ℤ, IsFlatOnSite (J := T.smallEtaleTopology)
      (R := coefficientQuotientSheaf (J := T.smallEtaleTopology) O' mu n)
      ((((siteCoefficientTensor (a.sheaf T n)).mapHomologicalComplex (.up ℤ)).obj P).X i) := by
  exact scalar_good_map T.smallEtaleTopology (a.sheaf T n) P hk hf

set_option maxHeartbeats 1600000 in
-- The representative substitutions compare several concrete derived functors.
private theorem quotient_on_flat {m n : ℕ} (h : n ≤ m)
    (P : CochainComplex (strictEtaleLevel c.Z O ell (index m)) ℤ)
    (hk : P.IsKFlatIndependentCoefficients)
    (hf : ∀ i : ℤ, IsFlatOnSite (J := c.Z.smallEtaleTopology)
      (R := coefficientQuotientSheaf (J := c.Z.smallEtaleTopology) O ell (index m)) (P.X i)) :
    (SB.openDerived.level n).inverse.map ((qZ.derived h).hom.app (DerivedCategory.Q.obj P)) ≫
        (SB.openDerived.derivedTensor h).hom.app
          ((TZ.level m).derived.obj (DerivedCategory.Q.obj P)) ≫
        (SB.PX.scalar h).derived.map ((finite m).derived.hom.app (DerivedCategory.Q.obj P)) =
      (finite n).derived.hom.app
          ((SA.PZ.scalar (index.monotone h)).derived.obj (DerivedCategory.Q.obj P)) ≫
        (TX.level n).derived.map
          ((SA.openDerived.derivedTensor (index.monotone h)).hom.app (DerivedCategory.Q.obj P)) ≫
        (qX.derived h).hom.app
          ((SA.openDerived.level (index m)).inverse.obj (DerivedCategory.Q.obj P)) := by
  let IA := (SA.openImage.lift (index m)).modules.mapHomologicalComplex (.up ℤ)
  let TZm := (siteCoefficientTensor (a.sheaf c.Z m)).mapHomologicalComplex (.up ℤ)
  let TXm := (siteCoefficientTensor (a.sheaf X m)).mapHomologicalComplex (.up ℤ)
  let : PreservesFiniteLimits (Scheme.etaleSetPullback c.i) :=
    (etaleSetInverseImage_exact c.i).2.2.1
  have hIA := inverse_good (PV := SA.PX) (A := SA.openImage) (index m) P hk hf
  have hTZ := transport_good (a := a) c.Z m P hk hf
  have hTX := transport_good (a := a) X m (IA.obj P) hIA.1 hIA.2
  have hAZ := scalar_good c.Z.smallEtaleTopology (index.monotone h) P hk hf
  let := (TX.level m).computes (IA.obj P) hIA.1
  let := (SB.PX.scalar h).computes (TXm.obj (IA.obj P)) hTX.1
  apply (cancel_mono
    ((SB.PX.scalar h).derived.map
      ((TX.level m).derived.map ((SA.openDerived.level (index m)).inverseFactors.hom.app P) ≫
        (TX.level m).counit.app (IA.obj P)) ≫
      (SB.PX.scalar h).counit.app (TXm.obj (IA.obj P)))).1
  simp only [Functor.map_comp, Category.assoc]
  have hm := congrArg (fun z ↦ (SB.PX.scalar h).derived.map z)
    ((finite m).representative P hk hf)
  simp only [Functor.map_comp] at hm
  conv_lhs => erw [reassoc_of% hm]
  have hc := (SB.PX.scalar h).counit.naturality
    ((NatIso.mapHomologicalComplex (finite m).ordinary (.up ℤ)).hom.app P)
  dsimp only [Functor.comp_map] at hc
  conv_lhs =>
    arg 2; arg 2; arg 2; arg 2
    erw [hc]
  have hn := (SB.openDerived.derivedTensor h).hom.naturality ((TZ.level m).counit.app P)
  dsimp only [Functor.comp_map] at hn
  conv_lhs =>
    arg 2
    erw [← reassoc_of% hn, reassoc_of% SB.openDerived.derivedTensor_rep h
      (TZm.obj P) hTZ.1 hTZ.2]
  have hz := congrArg (fun z ↦ (SB.openDerived.level n).inverse.map z)
    (qZ.property.2 h P)
  simp only [Functor.map_comp] at hz
  conv_lhs => erw [reassoc_of% hz]
  have hzN := (SB.openDerived.level n).inverseFactors.hom.naturality
    ((NatIso.mapHomologicalComplex (qZ.val.1 h) (.up ℤ)).hom.app P)
  dsimp only [Functor.comp_map] at hzN
  conv_lhs =>
    arg 2; arg 2
    erw [reassoc_of% hzN]
  have hxN := (qX.derived h).hom.naturality
    ((SA.openDerived.level (index m)).inverseFactors.hom.app P)
  dsimp only [Functor.comp_map] at hxN
  conv_rhs =>
    arg 2; arg 2
    erw [← reassoc_of% hxN, qX.property.2 h (IA.obj P)]
  have ha := congrArg (fun z ↦ (TX.level n).derived.map z)
    (SA.openDerived.derivedTensor_rep (index.monotone h) P hk hf)
  simp only [Functor.map_comp] at ha
  conv_rhs =>
    arg 2
    erw [reassoc_of% ha]
  have hxC := (TX.level n).counit.naturality
    ((NatIso.mapHomologicalComplex (SA.openDerived.tensor (index.monotone h))
      (.up ℤ)).hom.app P)
  dsimp only [Functor.comp_map] at hxC
  conv_rhs =>
    arg 2; arg 2; arg 2
    erw [reassoc_of% hxC]
  have hnA := (finite n).derived.hom.naturality
    ((SA.PZ.scalar (index.monotone h)).counit.app P)
  dsimp only [Functor.comp_map] at hnA
  conv_rhs =>
    erw [← reassoc_of% hnA]
    arg 2
    erw [reassoc_of% (finite n).representative _ hAZ.1 hAZ.2]
  simp only [← DerivedCategory.Q.map_comp]
  congr 3
  apply congrArg DerivedCategory.Q.map
  ext i : 1
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatIso.mapHomologicalComplex_hom_app_f]
  exact ordinary_quotient qX qZ finite h (P.X i)

end Quotient

private theorem inverse_three_eq {C : Type*} [Category C]
    {A B D E F G : C} (f₁ : A ≅ B) (f₂ : B ≅ D) (f₃ : D ≅ E)
    (g₁ : A ≅ F) (g₂ : F ≅ G) (g₃ : G ≅ E)
    (h : f₁.hom ≫ f₂.hom ≫ f₃.hom = g₁.hom ≫ g₂.hom ≫ g₃.hom) :
    f₃.inv ≫ f₂.inv ≫ f₁.inv = g₃.inv ≫ g₂.inv ≫ g₁.inv := by
  have he : f₁ ≪≫ f₂ ≪≫ f₃ = g₁ ≪≫ g₂ ≪≫ g₃ :=
    Iso.ext h
  simpa only [Iso.trans_inv, Category.assoc] using congrArg Iso.inv he

private theorem inverse_cube
    {A B C D E F G H I : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category E] [Category F] [Category G] [Category H]
    (r : A ⥤ B) (s : C ⥤ D) (t : E ⥤ F) (u : G ⥤ H)
    (a : A ⥤ C) (b : B ⥤ D) (c : E ⥤ G) (d : F ⥤ H)
    (i : A ⥤ E) (j : B ⥤ F) (k : C ⥤ G) (l : D ⥤ H)
    (qZ : r ⋙ b ≅ a ⋙ s) (gB : s ⋙ l ≅ k ⋙ u)
    (fm : a ⋙ k ≅ i ⋙ c) (fn : b ⋙ l ≅ j ⋙ d)
    (gA : r ⋙ j ≅ i ⋙ t) (qX : t ⋙ d ≅ c ⋙ u)
    (Q : I → A) (good : I → Prop)
    (extQ : ∀ {F0 F1 : A ⥤ H} (α β : F0 ⟶ F1),
      (∀ P, good P → α.app (Q P) = β.app (Q P)) → α = β)
    (h : ∀ P, good P →
      l.map (qZ.hom.app (Q P)) ≫ gB.hom.app (a.obj (Q P)) ≫
          u.map (fm.hom.app (Q P)) =
        fn.hom.app (r.obj (Q P)) ≫ d.map (gA.hom.app (Q P)) ≫
          qX.hom.app (i.obj (Q P))) (M : A) :
    u.map (fm.inv.app M) ≫ gB.inv.app (a.obj M) ≫ l.map (qZ.inv.app M) =
      qX.inv.app (i.obj M) ≫ d.map (gA.inv.app M) ≫ fn.inv.app (r.obj M) := by
  let α : (r ⋙ b) ⋙ l ⟶ (i ⋙ c) ⋙ u :=
    Functor.whiskerRight qZ.hom l ≫ Functor.whiskerLeft a gB.hom ≫
      Functor.whiskerRight fm.hom u
  let β : (r ⋙ b) ⋙ l ⟶ (i ⋙ c) ⋙ u :=
    Functor.whiskerLeft r fn.hom ≫ Functor.whiskerRight gA.hom d ≫
      Functor.whiskerLeft i qX.hom
  have he := NatTrans.congr_app (extQ α β h) M
  have hi := inverse_three_eq (l.mapIso (qZ.app M)) (gB.app (a.obj M))
    (u.mapIso (fm.app M)) (fn.app (r.obj M)) (d.mapIso (gA.app M))
    (qX.app (i.obj M))
    (by simpa only [α, β, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.mapIso_hom, Iso.app_hom] using he)
  simpa only [Functor.mapIso_inv, Iso.app_inv] using hi

set_option maxHeartbeats 4000000 in
-- Compare plain natural transformations before reversing the three object isomorphisms.
/-- Quotient compatibility for normalized finite inverse-image transport.
The comparison is on the geometric inverse-image side, before any open-adjunction
mate is taken. It quantifies arbitrary normalized quotient interchange records.
Source: Zheng, Construction 5.15 and Proposition 2.29(2); Stacks Tag 0D6D.
(blueprint: lem-pur-strict-etale-level-inverse-quotient).

Proof: precompose the ordinary versions of both paths with the two scalar-unit
insertions. The unit equations of the finite transport squares, the quotient
interchanges, and the geometric quotient tensor comparisons reduce both words to
inverse image of insertion for the same composite coefficient map. The composites
of coefficient maps agree on every quotient generator by a.generators; the nested
tensor/restriction Hom bijections detect equality of the ordinary module maps.
Explicitly, the two balanced maps send b_n tensor (b_m tensor x) to
b_n times the image of b_m tensor the geometric inverse image of x. On the two
inserted units this is 1 tensor the inverse image of x in both cases. Naturality
and the scalar actions extend this equality to the full nested tensor modules.
Pass to flat-term independently K-flat cochain representatives. Scalar extension
and geometric inverse image preserve that class, so all intermediate universal
scalar computation counits are invertible. Substitute the prescribed representative
equations of finite, qX, qZ, and the two derivedTensor maps. Cancel those counits
and the exact geometric factorization isomorphisms: the resulting equality is
localization of the ordinary equality just proved. Every derived object has such
a resolution, so naturality transfers the equality to every object. This argument
never assumes that a quotient scalar functor is exact on arbitrary complexes. -/
theorem strictEtaleLevelInverse_quotient
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (SA : StrictEtaleCompactSupport O ell c) (SB : StrictEtaleCompactSupport O' mu c)
    (TX : StrictEtaleCoefficientTransport a X SA.PX SB.PX)
    (TZ : StrictEtaleCoefficientTransport a c.Z SA.PZ SB.PZ)
    (qX : StrictEtaleTransportQuotient TX) (qZ : StrictEtaleTransportQuotient TZ)
    (finite : ∀ n, StrictEtaleLevelInverseTransport TX TZ SA.openImage SB.openImage
      SA.openDerived.level SB.openDerived.level n) :
    ∀ {m n : ℕ} (h : n ≤ m) M,
      (SB.PX.scalar h).derived.map ((finite m).derived.inv.app M) ≫
          (SB.openDerived.derivedTensor h).inv.app ((TZ.level m).derived.obj M) ≫
          (SB.openDerived.level n).inverse.map ((qZ.derived h).inv.app M) =
        (qX.derived h).inv.app ((SA.openDerived.level (index m)).inverse.obj M) ≫
          (TX.level n).derived.map
            ((SA.openDerived.derivedTensor (index.monotone h)).inv.app M) ≫
          (finite n).derived.inv.app ((SA.PZ.scalar (index.monotone h)).derived.obj M) := by
  intro m n h M
  exact inverse_cube
    (SA.PZ.scalar (index.monotone h)).derived (SB.PZ.scalar h).derived
    (SA.PX.scalar (index.monotone h)).derived (SB.PX.scalar h).derived
    (TZ.level m).derived (TZ.level n).derived (TX.level m).derived (TX.level n).derived
    (SA.openDerived.level (index m)).inverse (SA.openDerived.level (index n)).inverse
    (SB.openDerived.level m).inverse (SB.openDerived.level n).inverse
    (qZ.derived h) (SB.openDerived.derivedTensor h) (finite m).derived (finite n).derived
    (SA.openDerived.derivedTensor (index.monotone h)) (qX.derived h)
    DerivedCategory.Q.obj
    (fun (P : CochainComplex (strictEtaleLevel c.Z O ell (index m)) ℤ) ↦
      P.IsKFlatIndependentCoefficients ∧ ∀ i : ℤ,
        IsFlatOnSite (J := c.Z.smallEtaleTopology)
          (R := coefficientQuotientSheaf (J := c.Z.smallEtaleTopology) O ell (index m))
          (P.X i))
    (fun α β hαβ ↦ hom_ext_flat c.Z.smallEtaleTopology (index m) α β
      (fun P hk hf ↦ hαβ P ⟨hk, hf⟩))
    (fun P hP ↦ quotient_on_flat qX qZ finite h P hP.1 hP.2) M

end AlgebraicGeometry
