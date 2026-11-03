/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Native.NativeOpenTensorDescentData
public import WeilConjectures.WeilSheaf.NativeOpenTensorNativePairRestrictionStage3
public import WeilConjectures.WeilSheaf.NativeOpenTensorNativeSheafStage3
public import WeilConjectures.SixFunctors.NativeNormalizedRestrictionProof.NativeOpenTensorNativeTotalStage3

/-! The native normalized comparison used by open tensor restriction descent.
(blueprint: lem-sf-native-open-tensor-restriction-descent) -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option synthInstance.maxSize 4096

attribute [local irreducible]
  CategoryTheory.OpenTensorRestrictionNormalization

universe u a b

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtaleWeilSheaf

attribute [local instance] OpenTensorDescentInput.r_add OpenTensorDescentInput.r_lim
  OpenTensorDescentInput.r_colim OpenTensorDescentInput.r_zero

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
variable {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ Z) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]

private def RestrictionPreservation
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
    (c : OpenTensorDescentInput A B) : Prop :=
  ∀ T, c.flatB T → c.flatA ((c.R.mapHomologicalComplex (.up ℤ)).obj T)

private theorem restrictionPreservation_of_eq
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
    (c : OpenTensorDescentInput A B)
    (flatA : CochainComplex A ℤ → Prop) (flatB : CochainComplex B ℤ → Prop)
    (Rc : CochainComplex B ℤ ⥤ CochainComplex A ℤ)
    (ha : c.flatA = flatA) (hb : c.flatB = flatB)
    (hr : c.R.mapHomologicalComplex (.up ℤ) = Rc)
    (hR : ∀ T, flatB T → flatA (Rc.obj T)) : RestrictionPreservation c := by
  unfold RestrictionPreservation
  rw [ha, hb, hr]
  exact hR

private def castPairIso
    {A B : Type a} [Category.{b} A] [Category.{b} B]
    {F G F' G' : B × B ⥤ A} (hF : F = F') (hG : G = G') (e : F ≅ G) : F' ≅ G' :=
  hF ▸ hG ▸ e

private theorem castPairIso_family
    {A B : Type a} [Category.{b} A] [Category.{b} B]
    {F G F' G' : B × B ⥤ A} (hF : F = F') (hG : G = G') (e : F ≅ G) :
    HEq (fun M N ↦ (castPairIso hF hG e).app (M, N))
      (fun M N ↦ e.app (M, N)) := by
  cases hF
  cases hG
  rfl

private abbrev CanonicalTotalData
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
    (c : OpenTensorDescentInput A B) (m : OpenTensorDescentModels c)
    (sr : c.SB ⋙ c.R ≅ c.R.prod c.R ⋙ c.SA) : Type _ :=
  @TotalData _ _ _ _ _ _ _ _ c m c.r_zero sr

private def ModelNaturality
    {C : Type a} [Category.{b} C] [Abelian C] [HasDerivedCategory.{b} C]
    (Tco : CochainComplex C ℤ ⥤ CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (D : DerivedCategory C × DerivedCategory C ⥤ DerivedCategory C)
    (flat : CochainComplex C ℤ → Prop)
    (e : ∀ P T, flat P → flat T →
      (D.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj ((Tco.obj P).obj T))) : Prop :=
  ∀ P P' T T' (hP : flat P) (hP' : flat P') (hT : flat T) (hT' : flat T')
    (f : P ⟶ P') (g : T ⟶ T'),
    D.map (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) ≫
        (e P' T' hP' hT').hom =
      (e P T hP hT).hom ≫ DerivedCategory.Q.map
        (((Tco.map f).app T) ≫ (Tco.obj P').map g)

private def PairFaithfulness
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
    (c : OpenTensorDescentInput A B) : Type _ :=
  ((Functor.whiskeringLeft
    (ObjectProperty.FullSubcategory c.flatB × ObjectProperty.FullSubcategory c.flatB)
    (DerivedCategory B × DerivedCategory B) (DerivedCategory A)).obj
      (((ObjectProperty.ι c.flatB) ⋙ DerivedCategory.Q).prod
        ((ObjectProperty.ι c.flatB) ⋙ DerivedCategory.Q))).FullyFaithful

private theorem descendComparison
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
    (c : OpenTensorDescentInput A B) (m : OpenTensorDescentModels c)
    (hR : RestrictionPreservation c)
    (hnA : ModelNaturality c.TA c.DA c.flatA m.modelA)
    (hnB : ModelNaturality c.TB c.DB c.flatB m.modelB)
    (sr : c.SB ⋙ c.R ≅ c.R.prod c.R ⋙ c.SA) (td : CanonicalTotalData c m sr)
    (hs : HEq m.sheafRestriction (fun M N ↦ sr.app (M, N)))
    (ff : PairFaithfulness c) :
    Nonempty (OpenTensorRestrictionDescentData c m) := by
  unfold RestrictionPreservation at hR
  unfold ModelNaturality at hnA hnB
  unfold PairFaithfulness at ff
  let total := totalData_total c m sr td
  let iB := ObjectProperty.ι c.flatB
  let qB := iB ⋙ DerivedCategory.Q
  let Rc := c.R.mapHomologicalComplex (.up ℤ)
  let rf := c.R.mapDerivedCategoryFactors
  let mB : qB.prod qB ⋙ c.DB ≅
      iB.prod iB ⋙ Functor.uncurry.obj c.TB ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun PT ↦ m.modelB _ _ PT.1.property PT.2.property)
      (fun {PT PT'} fg ↦ hnB _ _ _ _ PT.1.property PT'.1.property
        PT.2.property PT'.2.property fg.1.hom fg.2.hom)
  let mA : ((iB ⋙ Rc) ⋙ DerivedCategory.Q).prod
      ((iB ⋙ Rc) ⋙ DerivedCategory.Q) ⋙ c.DA ≅
      (iB ⋙ Rc).prod (iB ⋙ Rc) ⋙ Functor.uncurry.obj c.TA ⋙ DerivedCategory.Q :=
    NatIso.ofComponents
      (fun PT ↦ m.modelA _ _ (hR _ PT.1.property) (hR _ PT.2.property))
      (fun {PT PT'} fg ↦ hnA _ _ _ _ (hR _ PT.1.property) (hR _ PT'.1.property)
        (hR _ PT.2.property) (hR _ PT'.2.property) (Rc.map fg.1.hom) (Rc.map fg.2.hom))
  let gg : qB.prod qB ⋙ (c.DB ⋙ c.R.mapDerivedCategory) ≅
      qB.prod qB ⋙ (c.R.mapDerivedCategory.prod c.R.mapDerivedCategory ⋙ c.DA) :=
    Functor.isoWhiskerRight mB c.R.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (iB.prod iB ⋙ Functor.uncurry.obj c.TB) rf ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft (iB.prod iB) total)
        DerivedCategory.Q ≪≫ mA.symm ≪≫
      Functor.isoWhiskerRight
        (NatIso.prod (Functor.isoWhiskerLeft iB rf).symm
          (Functor.isoWhiskerLeft iB rf).symm) c.DA
  let rho := ff.preimageIso gg
  refine ⟨{
    hR := hR
    total := fun P T ↦ total.app (P, T)
    rho := rho
    summands := ?_
    model := ?_ }⟩
  · intro P T p q n h
    rw [eq_of_heq hs]
    exact totalData_summands c m sr td P T p q n h
  unfold OpenTensorRestrictionNormalization
  intro P T hP hT
  have h := NatTrans.congr_app (ff.map_preimage gg.hom) (⟨P, hP⟩, ⟨T, hT⟩)
  change rho.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) =
    gg.hom.app (⟨P, hP⟩, ⟨T, hT⟩) at h
  rw [h]
  dsimp only [gg, mB, mA, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerLeft_inv, Iso.symm_hom,
    NatIso.prod_hom, NatTrans.prod,
    NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app]
  dsimp only [iB, qB, Rc, rf, Functor.comp_obj, Functor.prod_obj,
    Functor.uncurry_obj_obj, ObjectProperty.ι_obj]
  simp only [Category.assoc, ← Functor.map_comp_assoc, prod_comp,
    Iso.inv_hom_id_app, ← prod_id, Iso.app_hom]
  erw [c.DA.map_id]
  simp only [Category.id_comp, Iso.inv_hom_id, Category.comp_id]

/-- Existence results supplied by the native sheaf, total, and pair stages. -/
structure NativeRestrictionStageInputs
    (s : NativeOpenTensorData k₀ l j)
    (m : OpenTensorDescentModels (nativeOpenTensorDescentInput k₀ l j)) : Prop where
  restriction_kflat : ∀ T, NativeIsKFlat k₀ l Z T →
    NativeIsKFlat k₀ l U
      (((upperStar k₀ l j).mapHomologicalComplex (.up ℤ)).obj T)
  sheaf : Nonempty (SheafData k₀ l j s m)
  total : ∀ (sr : (nativeOpenTensorDescentInput k₀ l j).SB ⋙
      (nativeOpenTensorDescentInput k₀ l j).R ≅
      (nativeOpenTensorDescentInput k₀ l j).R.prod
        (nativeOpenTensorDescentInput k₀ l j).R ⋙
      (nativeOpenTensorDescentInput k₀ l j).SA),
    Nonempty (NativeNormalizedRestrictionProof.TotalData
      (nativeOpenTensorDescentInput k₀ l j) m sr)
  pair : Nonempty (NativePairRestrictionData k₀ l j)

private theorem nativeModelNaturality
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (e : ∀ P T, NativeIsKFlat k₀ l X P → NativeIsKFlat k₀ l X T →
      ((nativeDerivedTensor k₀ l X).obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj (((nativeTensorTotal k₀ l X).obj P).obj T)))
    (he : HEq e (nativeOpenTensorModel k₀ l X)) :
    ∀ P P' T T' (hP : NativeIsKFlat k₀ l X P) (hP' : NativeIsKFlat k₀ l X P')
      (hT : NativeIsKFlat k₀ l X T) (hT' : NativeIsKFlat k₀ l X T')
      (f : P ⟶ P') (g : T ⟶ T'),
      (nativeDerivedTensor k₀ l X).map
          (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) ≫
          (e P' T' hP' hT').hom =
        (e P T hP hT).hom ≫ DerivedCategory.Q.map
          ((((nativeTensorTotal k₀ l X).map f).app T) ≫
            ((nativeTensorTotal k₀ l X).obj P').map g) := by
  rw [eq_of_heq he]
  unfold nativeOpenTensorModel
  exact (native_normalized_tensor_models k₀ l X).choose_spec.1

private theorem nativeRestrictionPacket
    (s : NativeOpenTensorData k₀ l j)
    (m : OpenTensorDescentModels (nativeOpenTensorDescentInput k₀ l j))
    (hm : NativeOpenTensorModelsCompatibility k₀ l j s m)
    (d : OpenTensorRestrictionDescentData (nativeOpenTensorDescentInput k₀ l j) m) :
    Nonempty (NativeOpenTensorRestrictionDescentData k₀ l j s m) :=
  ⟨{ component := d, compatible := hm, rho := d.rho, rho_compatible := HEq.rfl }⟩

private theorem nativeFlatA_eq :
    (nativeOpenTensorDescentInput k₀ l j).flatA = NativeIsKFlat k₀ l U := rfl

private theorem nativeFlatB_eq :
    (nativeOpenTensorDescentInput k₀ l j).flatB = NativeIsKFlat k₀ l Z := rfl

private theorem nativeComplexRestriction_eq :
    ((nativeOpenTensorDescentInput k₀ l j).R.mapHomologicalComplex (.up ℤ)) =
      (upperStar k₀ l j).mapHomologicalComplex (.up ℤ) := rfl

private theorem nativeRestrictionLeft_eq :
    nativeOpenSheafTensor k₀ l Z ⋙ upperStar k₀ l j =
      (nativeOpenTensorDescentInput k₀ l j).SB ⋙
        (nativeOpenTensorDescentInput k₀ l j).R := rfl

private theorem nativeRestrictionRight_eq :
    (upperStar k₀ l j).prod (upperStar k₀ l j) ⋙ nativeOpenSheafTensor k₀ l U =
      (nativeOpenTensorDescentInput k₀ l j).R.prod
        (nativeOpenTensorDescentInput k₀ l j).R ⋙
        (nativeOpenTensorDescentInput k₀ l j).SA := rfl

private abbrev nativeGenericRestrictionData
    (m : OpenTensorDescentModels (nativeOpenTensorDescentInput k₀ l j)) : Type _ :=
  @OpenTensorRestrictionDescentData _ _ _ _ _ _ _ _
    (nativeOpenTensorDescentInput k₀ l j) m

-- All arguments now have the generic input types before the descent construction is applied.

private theorem nativePacketNonempty
    (s : NativeOpenTensorData k₀ l j)
    (m : OpenTensorDescentModels (nativeOpenTensorDescentInput k₀ l j))
    (hm : NativeOpenTensorModelsCompatibility k₀ l j s m)
    (hd : Nonempty (nativeGenericRestrictionData k₀ l j m)) :
    Nonempty (NativeOpenTensorRestrictionDescentData k₀ l j s m) := by
  obtain ⟨d⟩ := hd
  exact nativeRestrictionPacket k₀ l j s m hm d

/-- The native normalized comparison assembles the restriction component from the
native sheaf and total stages and the fully faithful pair restriction.

Source: Stacks 07A4 (lemma-pullback-tensor-product), 06YN, 06YS and 012Z.
(blueprint: new-sf-native-open-tensor-normalized-comparison-stage3)

Proof: take hR from `restriction_kflat`, choose the sheaf map `sr` of the sheaf stage
and the total comparison for `sr` of the total stage; the sheaf-stage HEq turns its
summand equation into the one for `m.sheafRestriction`. On native K-flat pairs P,T
compose the ambient model (by hm the native model of native_normalized_tensor_models),
the exact derived factorization of restriction, Q of the total comparison, the inverse
open model and the inverse factorizations of the restricted inputs (K-flat by hR).
Naturality of the models, of the total comparison and of the factorizations makes
this a natural isomorphism on K-flat pairs; full faithfulness of the pair stage
descends it to rho on all derived inputs, and cancelling the model and factorization
isomorphisms is the square of OpenTensorRestrictionNormalization. The same rho with
the native functor types gives the native field and its HEq. -/
theorem normalizedComparisonStage3
    (s : NativeOpenTensorData k₀ l j)
    (m : OpenTensorDescentModels (nativeOpenTensorDescentInput k₀ l j))
    (hm : NativeOpenTensorModelsCompatibility k₀ l j s m)
    (stages : NativeRestrictionStageInputs k₀ l j s m) :
    Nonempty (NativeOpenTensorRestrictionDescentData k₀ l j s m) := by
  sorry

end AlgebraicGeometry.ProEtaleWeilSheaf
