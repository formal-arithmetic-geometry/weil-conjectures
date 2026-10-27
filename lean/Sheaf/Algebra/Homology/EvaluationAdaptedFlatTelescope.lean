/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.RingTheory.Flat.Basic
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic

/-! # Simultaneous flat telescope resolutions for evaluation

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Lemma 4.1(1);
Stacks Project, Tags 077J, 06YS, 0949, 06YQ, 07A3 and 010N
(blueprint: lem-zl-evaluation-adapted-flat-telescope).

The existential diagrams below only encode the specified tower, its canonical colimit
factorization and the canonical comparison after evaluation. No functorial selection of
towers or preservation of arbitrary K-flat complexes is claimed.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CochainComplex

open MonoidalCategory
open scoped ZeroObject

attribute [local instance] Abelian.hasFiniteBiproducts

/-- The sum of the transition maps into a fixed term, extended by zero on later terms.
Source: Stacks Project, Tag 093W, the transition-map sum in its proof
(blueprint: lem-pc-telescope-shift-mono). -/
private noncomputable def telescopeProjection
    {A : Type*} [Category A] [Preadditive A] [HasCountableCoproducts A]
    (E : ℕ ⥤ A) (j : ℕ) : (∐ fun n : ℕ ↦ E.obj n) ⟶ E.obj j :=
  Sigma.desc fun k ↦ if h : k ≤ j then E.map (homOfLE h) else 0

/-- The transition-map sum cancels consecutive transitions, leaving a single diagonal entry.
Source: Stacks Project, Tag 093W, the finite short exact sequence in its proof
(blueprint: lem-pc-telescope-shift-mono). -/
private lemma telescopeProjection_formula
    {A : Type*} [Category A] [Preadditive A] [HasCountableCoproducts A]
    (E : ℕ ⥤ A) (j k : ℕ) :
    (Sigma.ι (fun n : ℕ ↦ E.obj n) k -
      E.map (homOfLE (Nat.le_succ k)) ≫
        Sigma.ι (fun n : ℕ ↦ E.obj n) (k + 1)) ≫ telescopeProjection E j =
      if h : k = j then eqToHom (congrArg E.obj h) else 0 := by
  classical
  simp only [telescopeProjection, Preadditive.sub_comp, Category.assoc, Sigma.ι_desc]
  by_cases h : k = j
  · subst j
    simp
  · by_cases hkj : k ≤ j
    · have hsj : k + 1 ≤ j := by omega
      simp only [dif_pos hkj, dif_pos hsj, dif_neg h]
      rw [← E.map_comp]
      simp
    · have hsj : ¬ k + 1 ≤ j := by omega
      simp [hkj, hsj, h]

/-- Restrict one minus shift to each finite subcoproduct, give an explicit retraction,
then take the exact filtered colimit of these monomorphisms into the constant target.
Source: Stacks Project, Tag 093W, proof by finite sums and exact colimits
(blueprint: lem-pc-telescope-shift-mono). -/
private lemma sequentialCoproduct_mono
    {A : Type*} [Category A] [Preadditive A] [HasCountableCoproducts A]
    [HasColimitsOfShape (Finset (Discrete ℕ)) A]
    [HasExactColimitsOfShape (Finset (Discrete ℕ)) A]
    (E : ℕ ⥤ A) :
    Mono (Sigma.desc (fun n : ℕ ↦
      Sigma.ι (fun n : ℕ ↦ E.obj n) n -
        E.map (homOfLE (Nat.le_succ n)) ≫
          Sigma.ι (fun n : ℕ ↦ E.obj n) (n + 1))) := by
  classical
  have : IsConnected (Finset (Discrete ℕ)) := IsFiltered.isConnected _
  let u := Sigma.desc (fun n : ℕ ↦
    Sigma.ι (fun n : ℕ ↦ E.obj n) n -
      E.map (homOfLE (Nat.le_succ n)) ≫
        Sigma.ι (fun n : ℕ ↦ E.obj n) (n + 1))
  let F := CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor E.obj)
  let c := CoproductsFromFiniteFiltered.finiteSubcoproductsCocone (fun n ↦ E.obj n)
  let φ : F ⟶ (Functor.const (Finset (Discrete ℕ))).obj (∐ fun n ↦ E.obj n) :=
    c.ι ≫ (Functor.const _).map u
  have hφ (S : Finset (Discrete ℕ)) : Mono (φ.app S) := by
    let r : (∐ fun n ↦ E.obj n) ⟶ F.obj S :=
      ∑ j : S, telescopeProjection E j.1.as ≫ Sigma.ι (fun k : S ↦ E.obj k.1.as) j
    have hr : φ.app S ≫ r = 𝟙 _ := by
      apply Sigma.hom_ext
      intro k
      dsimp [φ, c, F, CoproductsFromFiniteFiltered.finiteSubcoproductsCocone,
        CoproductsFromFiniteFiltered.liftToFinsetObj, r]
      simp only [u, Sigma.ι_desc, Preadditive.comp_sum,
        ← Category.assoc, telescopeProjection_formula]
      rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hjk
        have hne : k.1.as ≠ j.1.as := by
          intro h
          apply hjk
          apply Subtype.ext
          exact Discrete.ext h.symm
        simp [hne]
      · simp
    exact (IsSplitMono.mk' ⟨r, hr⟩).mono
  have : Mono φ := NatTrans.mono_of_mono_app φ
  exact colim.map_mono' φ
    (CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone (fun n ↦ E.obj n))
    (isColimitConstCocone (Finset (Discrete ℕ)) _) u (by intro j; simp [φ, c])

set_option backward.isDefEq.respectTransparency false in
private noncomputable def telescope_cokernel
    {A : Type*} [Category* A] [Abelian A] [HasCountableCoproducts A]
    [HasColimitsOfShape ℕ A] (E : ℕ ⥤ A)
    (u : (∐ E.obj) ⟶ (∐ E.obj))
    (hu : ∀ n, Sigma.ι E.obj n ≫ u =
      Sigma.ι E.obj n - E.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι E.obj (n + 1))
    (a : (∐ E.obj) ⟶ colimit E)
    (ha : ∀ n, Sigma.ι E.obj n ≫ a = colimit.ι E n)
    (h : u ≫ a = 0) :
    IsColimit (CokernelCofork.ofπ (a) h) := by
  let cocone (s : CokernelCofork (u)) : Cocone E :=
    { pt := s.pt
      ι :=
        { app := fun n ↦ Sigma.ι (fun n : ℕ ↦ E.obj n) n ≫ s.π
          naturality := by
            intro n m f
            have hs (k : ℕ) :
                E.map (homOfLE (Nat.le_succ k)) ≫
                    Sigma.ι (fun n : ℕ ↦ E.obj n) (k + 1) ≫ s.π =
                  Sigma.ι (fun n : ℕ ↦ E.obj n) k ≫ s.π := by
              have hz := congrArg
                (fun z ↦ Sigma.ι (fun n : ℕ ↦ E.obj n) k ≫ z) s.condition
              simp only [comp_zero] at hz
              rw [← Category.assoc, hu] at hz
              simp only [Preadditive.sub_comp, Category.assoc] at hz
              exact (sub_eq_zero.mp hz).symm
            have hall (m : ℕ) (hnm : n ≤ m) :
                E.map (homOfLE hnm) ≫
                    Sigma.ι (fun n : ℕ ↦ E.obj n) m ≫ s.π =
                  Sigma.ι (fun n : ℕ ↦ E.obj n) n ≫ s.π := by
              induction m, hnm using Nat.le_induction with
              | base => simp
              | succ k hnk ih =>
                rw [show homOfLE (Nat.le_trans hnk (Nat.le_succ k)) =
                  homOfLE hnk ≫ homOfLE (Nat.le_succ k) from Subsingleton.elim _ _]
                rw [E.map_comp, Category.assoc, hs k]
                exact ih
            have hf : f = homOfLE (leOfHom f) := Subsingleton.elim _ _
            rw [hf]
            simpa using hall m (leOfHom f) } }
  refine Cofork.IsColimit.mk _ (fun s ↦ colimit.desc E (cocone s)) ?_ ?_
  · intro s
    apply Sigma.hom_ext
    intro n
    simp [← Category.assoc, ha, cocone]
  · intro s m hm
    apply colimit.hom_ext (F := E)
    intro n
    have hn := congrArg (fun z ↦ Sigma.ι (fun n : ℕ ↦ E.obj n) n ≫ z) hm
    simpa [← Category.assoc, ha, cocone] using hn

-- Store the constructed telescope behind a structure interface, so that using its
-- canonical maps never unfolds coproduct and colimit choices of the resolution diagram.
private structure TelescopeData {A : Type*} [Category A] [Abelian A]
    [HasCountableCoproducts A] [HasColimitsOfShape ℕ A]
    (D : ℕ ⥤ CochainComplex A ℤ) where
  B : CochainComplex A ℤ
  j : ∀ n, D.obj n ⟶ B
  u : B ⟶ B
  sum : IsColimit (Cofan.mk B j)
  shift : ∀ n, j n ≫ u = j n - D.map (homOfLE (Nat.le_succ n)) ≫ j (n + 1)
  r : mappingCone u ⟶ colimit D
  inr_r : ∀ n, j n ≫ mappingCone.inr u ≫ r = colimit.ι D n
  inl_r : (mappingCone.inl u).comp (HomComplex.Cochain.ofHom r) (add_zero _) = 0
  quasi_r : QuasiIso r

@[irreducible]
private noncomputable def telescopeData {A : Type*} [Category A] [Abelian A]
    [HasCountableCoproducts A] [HasColimitsOfShape ℕ A]
    [HasColimitsOfShape (Finset (Discrete ℕ)) A]
    [HasExactColimitsOfShape (Finset (Discrete ℕ)) A]
    (D : ℕ ⥤ CochainComplex A ℤ) : TelescopeData D := by
  let B := ∐ D.obj
  let j : ∀ n : ℕ, D.obj n ⟶ B := Sigma.ι D.obj
  let u : B ⟶ B := Sigma.desc
    (fun n ↦ j n - D.map (homOfLE (Nat.le_succ n)) ≫ j (n + 1))
  have hu (n : ℕ) : j n ≫ u =
      j n - D.map (homOfLE (Nat.le_succ n)) ≫ j (n + 1) := Sigma.ι_desc _ _
  let a : B ⟶ colimit D := Sigma.desc (colimit.ι D)
  have ha (n : ℕ) : j n ≫ a = colimit.ι D n := Sigma.ι_desc _ _
  have hz : u ≫ a = 0 := by
    apply Sigma.hom_ext
    intro n
    rw [← Category.assoc, hu, Preadditive.sub_comp, Category.assoc, ha, ha]
    simpa only [comp_zero] using
      sub_eq_zero.mpr (colimit.w D (homOfLE (Nat.le_succ n))).symm
  have : HasCountableCoproducts (CochainComplex A ℤ) :=
    ⟨fun I _ ↦ inferInstance⟩
  have : Mono u := sequentialCoproduct_mono D
  let S := ShortComplex.mk u a hz
  have hc := telescope_cokernel D u hu a ha hz
  have hS : S.ShortExact :=
    { exact := S.exact_of_g_is_cokernel hc
      mono_f := inferInstance
      epi_g := epi_of_isColimit_cofork hc }
  let r := mappingCone.descShortComplex S
  have hr : mappingCone.inr u ≫ r = a := mappingCone.inr_descShortComplex S
  refine ⟨B, j, u, coproductIsCoproduct D.obj, hu, r, ?_,
    mappingCone.inl_desc S.f 0 S.g (by simp), mappingCone.quasiIso_descShortComplex hS⟩
  intro n
  rw [hr, ha]

private theorem acyclic_coproduct {A : Type*} [Category* A] [Abelian A]
    {I : Type*} [HasColimitsOfShape (Discrete I) A]
    [HasExactColimitsOfShape (Discrete I) A]
    (K : I → CochainComplex A ℤ) (hK : ∀ i, (K i).Acyclic) : (∐ K).Acyclic := by
  intro n
  let D := Discrete.functor K
  let S := (ShortComplex.functorEquivalence (Discrete I) A).inverse.obj
    (D ⋙ HomologicalComplex.shortComplexFunctor A (.up ℤ) n)
  have hEval : JointlyReflectIsomorphisms
      (fun j : Discrete I ↦ (evaluation (Discrete I) A).obj j) :=
    ⟨fun f h ↦ by
      have (j : Discrete I) : IsIso (f.app j) := h j
      exact NatIso.isIso_of_isIso_app f⟩
  have hS : S.Exact := (hEval.exact_iff S).2 (fun j ↦ hK j.as n)
  have hc (i : ℤ) := isColimitOfPreserves (HomologicalComplex.eval A (.up ℤ) i)
    (colimit.isColimit D)
  exact colim.exact_mapShortComplex hS
    (hc ((ComplexShape.up ℤ).prev n)) (hc n) (hc ((ComplexShape.up ℤ).next n))
    ((∐ K).d _ n) ((∐ K).d n _)
    (fun j ↦ (colimit.ι D j).comm _ _) (fun j ↦ (colimit.ι D j).comm _ _)

private theorem acyclic_cone {A : Type*} [Category* A] [Abelian A]
    {K L : CochainComplex A ℤ} (f : K ⟶ L) (hK : K.Acyclic) (hL : L.Acyclic) :
    (mappingCone f).Acyclic := by
  let P := HomotopyCategory.subcategoryAcyclic A
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hK hL ⊢
  exact P.ext_of_isTriangulatedClosed₃ _
    (HomotopyCategory.mappingCone_triangleh_distinguished f) hK hL

private theorem tensor_cone_acyclic {A : Type*} [Category* A] [Abelian A]
    [MonoidalCategory A] [MonoidalPreadditive A] [HasCountableCoproducts A]
    {K L : CochainComplex A ℤ} (f : K ⟶ L) (F : CochainComplex A ℤ)
    (hK : (mapBifunctor F K (curriedTensor A)).Acyclic)
    (hL : (mapBifunctor F L (curriedTensor A)).Acyclic) :
    (mapBifunctor F (mappingCone f) (curriedTensor A)).Acyclic := by
  let e := mapBifunctorMappingCone₂Iso F f (curriedTensor A)
  have h := acyclic_cone
    (HomologicalComplex.mapBifunctorMap (𝟙 F) f (curriedTensor A) (.up ℤ)) hK hL
  exact fun i ↦ (h i).of_iso e.symm

section
variable {A B : Type*} [Category A] [Category B] [Abelian A]
  [Preadditive B] [HasZeroObject B] [HasFiniteCoproducts B]
  {ι : B ⥤ A} [ι.Full] [ι.Faithful] [ι.Additive]
  (Λ : Abelian.LeftResolution ι) [Λ.F.PreservesZeroMorphisms]
set_option backward.isDefEq.respectTransparency false in
private theorem totalπ_epi (K : Minus A) (i : ℤ) : Epi ((Λ.totalπ K).f i) := by
  let a := ι.map ((Λ.bicomplexFunctor.obj K.obj).ιTotal (.up ℤ) i 0 i (by simp))
  have h : a ≫ (Λ.totalπ K).f i =
      (ι.map (Λ.cochainComplexXZeroIso (K.obj.X i)).hom ≫ Λ.π.app (K.obj.X i) ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (K.obj.X i)).inv) ≫
        (HomologicalComplex₂.singleRowXXIso (.up ℤ) K.obj i 0).hom ≫
        (HomologicalComplex₂.singleRowObjTotalXIso K.obj i 0 i (by simp)).inv ≫
        (HomologicalComplex₂.singleRow₀ObjTotal K.obj).hom.f i := by
    dsimp [a, Abelian.LeftResolution.totalπ]
    simp only [HomologicalComplex₂.mapTotalIso, HomologicalComplex.Hom.isoOfComponents_inv_f]
    rw [HomologicalComplex₂.map_ι_mapTotalXIso_inv_assoc]
    rw [Abelian.LeftResolution.totalπ', HomologicalComplex₂.ιTotal_map_assoc]
    change (Λ.cochainComplexπ (K.obj.X i)).f 0 ≫ _ = _
    rw [Abelian.LeftResolution.cochainComplexπ_f_0,
      HomologicalComplex₂.singleRow_ιTotal_assoc]
  have : Epi (a ≫ (Λ.totalπ K).f i) := by
    rw [h]
    infer_instance
  exact epi_of_epi a ((Λ.totalπ K).f i)

end


private theorem tensor_cofan_acyclic {A : Type*} [Category* A] [Abelian A]
    [MonoidalCategory A] [MonoidalPreadditive A] [HasCountableCoproducts A]
    [HasExactColimitsOfShape (Discrete ℕ) A]
    [∀ X : A, PreservesColimitsOfShape (Discrete ℕ) (tensorLeft X)]
    (K : ℕ → CochainComplex A ℤ) (B : CochainComplex A ℤ)
    (j : ∀ n, K n ⟶ B) (hj : IsColimit (Cofan.mk B j))
    (F : CochainComplex A ℤ)
    (hK : ∀ n, (mapBifunctor F (K n) (curriedTensor A)).Acyclic) :
    (mapBifunctor F B (curriedTensor A)).Acyclic := by
  let T := ((curriedTensor A).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)).obj F
  have hc := (Cofan.isColimitMapCoconeEquiv T K (Cofan.mk B j))
    (isColimitOfPreserves T hj)
  let e := (coproductIsCoproduct (fun n ↦ T.obj (K n))).coconePointUniqueUpToIso hc
  have h := acyclic_coproduct (fun n ↦ T.obj (K n)) hK
  exact fun i ↦ (h i).of_iso e

private theorem bounded_module_kflat {S : Type w} [CommRing S]
    (K : CochainComplex (ModuleCat.{w} S) ℤ)
    (hb : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (K.X i))
    (hf : ∀ i : ℤ, Module.Flat S (K.X i)) :
    ∀ F : CochainComplex (ModuleCat.{w} S) ℤ, F.Acyclic →
      (mapBifunctor F K (curriedTensor _)).Acyclic := by
  have : AB5OfSize.{w, w} (ModuleCat.{w} S) := inferInstance
  have : AB5OfSize.{0, 0} (ModuleCat.{w} S) := AB5OfSize_shrink _
  have (M : ModuleCat.{w} S) : PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  obtain ⟨b, hb⟩ := hb
  have : K.IsStrictlyLE b := (K.isStrictlyLE_iff b).2 hb
  have hflat (i : ℤ) : ObjectProperty.flat (K.X i) := by
    have := hf i
    exact ⟨⟨show PreservesFiniteLimits (tensorLeft (K.X i)) from inferInstance,
      show PreservesFiniteColimits (tensorLeft (K.X i)) from inferInstance⟩,
      ⟨show PreservesFiniteLimits (tensorRight (K.X i)) from inferInstance,
      show PreservesFiniteColimits (tensorRight (K.X i)) from inferInstance⟩⟩
  have hk := kFlat_of_isStrictlyLE_of_flat K b hflat
  intro F hF
  let T := tensorRight K
  have hz : QuasiIso (0 : (0 : CochainComplex (ModuleCat.{w} S) ℤ) ⟶ F) := by
    rw [quasiIso_iff]
    intro i
    exact (quasiIsoAt_iff_exactAt _ i
      ((HomologicalComplex.acyclic_of_isZero _ (isZero_zero _)) i)).2 (hF i)
  have hmap : QuasiIso (T.map (0 : (0 : CochainComplex (ModuleCat.{w} S) ℤ) ⟶ F)) :=
    hk.2 _ hz
  have htzero : (T.obj (0 : CochainComplex (ModuleCat.{w} S) ℤ)).Acyclic :=
    HomologicalComplex.acyclic_of_isZero _ (T.map_isZero (isZero_zero _))
  exact fun i ↦ (exactAt_iff_of_quasiIsoAt
    (T.map (0 : (0 : CochainComplex (ModuleCat.{w} S) ℤ) ⟶ F)) i).1 (htzero i)

private structure FlatMinusData (A : Type*) [Category* A] [Abelian A]
    (P : ObjectProperty A) where
  L : Minus A ⥤ CochainComplex A ℤ
  ε : L ⟶ Minus.ι A
  bounded : ∀ K, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((L.obj K).X i)
  flat : ∀ K i, P ((L.obj K).X i)
  quasi : ∀ K, QuasiIso (ε.app K)
  epi : ∀ K i, Epi ((ε.app K).f i)

@[irreducible]
private noncomputable def categoricalFlatMinusData
    (A : Type*) [Category* A] [Abelian A]
    [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A]
    [BraidedCategory A] [HasCountableCoproducts A] [Abelian.HasFunctorialFlatResolution A] :
    FlatMinusData A ObjectProperty.flat := by
  classical
  have (M : A) : PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  have : (ObjectProperty.flat (A := A)).ContainsZero :=
    ⟨⟨0, isZero_zero A, ObjectProperty.flat_of_isZero (isZero_zero A)⟩⟩
  have : (ObjectProperty.flat (A := A)).IsStableUnderRetracts :=
    ⟨fun e h ↦ ObjectProperty.flat_of_retract e h⟩
  let Λ := (Classical.arbitrary (Abelian.LeftResolution
    (ObjectProperty.flat.ι : _ ⥤ A))).reduced
  let ιf := (ObjectProperty.flat.ι : _ ⥤ A)
  let L := Λ.minusResolutionFunctor ⋙ ιf.mapCochainComplexMinus ⋙ Minus.ι A
  let ε : L ⟶ Minus.ι A := Functor.whiskerRight Λ.minusResolutionNatTrans (Minus.ι A)
  refine ⟨L, ε, ?_, ?_, ?_, ?_⟩
  · intro K
    obtain ⟨b, hb⟩ := (Λ.minusResolutionFunctor.obj K).property
    have : (Λ.minusResolutionFunctor.obj K).obj.IsStrictlyLE b := hb
    exact ⟨b, fun i hi ↦ ιf.map_isZero
      (isZero_of_isStrictlyLE (Λ.minusResolutionFunctor.obj K).obj b i hi)⟩
  · exact fun K i ↦ ((Λ.minusResolutionFunctor.obj K).obj.X i).property
  · intro K
    dsimp [ε]
    infer_instance
  · exact fun K i ↦ totalπ_epi Λ K i

@[irreducible]
private noncomputable def flatMinusData
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w}) :
    FlatMinusData (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
      (SheafOfModules.IsFlatOnSite (J := J) (R := R)) := by
  classical
  let A := SheafOfModules.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.tensorPreadditive R
  let := (SheafOfModules.nonempty_monoidalClosed_independentCoefficients (R := R)).some
  have := SheafOfModules.hasFunctorialFlatResolution_kfi R
  let data := categoricalFlatMinusData A
  refine ⟨data.L, data.ε, data.bounded, ?_, data.quasi, data.epi⟩
  intro K i
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R _).symm (data.flat K i).2

private theorem flat_cone_terms {A : Type*} [Category* A] [Abelian A]
    [MonoidalCategory A] [HasCountableCoproducts A]
    [(ObjectProperty.flat (A := A)).IsClosedUnderColimitsOfShape (Discrete ℕ)]
    [(ObjectProperty.flat (A := A)).IsClosedUnderLimitsOfShape (Discrete WalkingPair)]
    (D : ℕ → CochainComplex A ℤ) (B : CochainComplex A ℤ)
    (j : ∀ n, D n ⟶ B) (u : B ⟶ B) (hj : IsColimit (Cofan.mk B j))
    (hf : ∀ n i, ObjectProperty.flat ((D n).X i)) :
    ∀ i, ObjectProperty.flat ((mappingCone u).X i) := by
  have hsum (i : ℤ) : ObjectProperty.flat (B.X i) :=
    ObjectProperty.prop_of_isColimit _
      (isColimitOfPreserves (HomologicalComplex.eval A (.up ℤ) i) hj)
      (fun n ↦ hf n.as i)
  intro i
  have h : ObjectProperty.flat (B.X (i + 1) ⊞ B.X i) :=
    ObjectProperty.prop_of_iso _ (biprod.isoProd _ _).symm
      (ObjectProperty.prop_of_isLimit _ (limit.isLimit (pair (B.X (i + 1)) (B.X i)))
        (by rintro ⟨_ | _⟩ <;> apply hsum))
  exact ObjectProperty.prop_of_iso _
    (HomologicalComplex.homotopyCofiber.XIsoBiprod u i (i + 1) rfl).symm h

private theorem adapted_telescope
    {A A₁ : Type*} [Category* A] [Category* A₁] [Abelian A] [Abelian A₁]
    [HasCountableCoproducts A] [HasColimitsOfShape ℕ A]
    [HasExactColimitsOfShape ℕ A]
    [HasColimitsOfShape (Finset (Discrete ℕ)) A]
    [HasExactColimitsOfShape (Finset (Discrete ℕ)) A]
    (P : ObjectProperty A) (Q : ObjectProperty A₁)
    (KP : ObjectProperty (CochainComplex A ℤ))
    (KQ : ObjectProperty (CochainComplex A₁ ℤ))
    (E : A ⥤ A₁) [E.Additive] [PreservesFiniteLimits E]
    [PreservesFiniteColimits E] [PreservesColimitsOfShape (Discrete ℕ) E]
    (data : FlatMinusData A P)
    (hflat : ∀ M, P M → Q (E.obj M))
    (hclosure : ∀ (D : ℕ → CochainComplex A ℤ) (B : CochainComplex A ℤ)
      (j : ∀ n, D n ⟶ B) (u : B ⟶ B), IsColimit (Cofan.mk B j) →
      (∀ n, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((D n).X i)) →
      (∀ n i, P ((D n).X i)) →
      (∀ i, P ((mappingCone u).X i)) ∧ KP (mappingCone u))
    (hclosure₁ : ∀ (D : ℕ → CochainComplex A₁ ℤ) (B : CochainComplex A₁ ℤ)
      (j : ∀ n, D n ⟶ B) (u : B ⟶ B), IsColimit (Cofan.mk B j) →
      (∀ n, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((D n).X i)) →
      (∀ n i, Q ((D n).X i)) → KQ (mappingCone u))
    (K : CochainComplex A ℤ) :
    ∃ (D : ℕ ⥤ CochainComplex (A) ℤ)
      (q : ∀ n : ℕ, D.obj n ⟶ K.truncLE (n : ℤ)),
      (∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((D.obj n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), P ((D.obj n).X i)) ∧
      (∀ n : ℕ, QuasiIso (q n)) ∧
      (∀ (n : ℕ) (i : ℤ), Epi ((q n).f i)) ∧
      (∀ n : ℕ, D.map (homOfLE (Nat.le_succ n)) ≫ q (n + 1) ≫
        K.ιTruncLE ((n + 1 : ℕ) : ℤ) = q n ≫ K.ιTruncLE (n : ℤ)) ∧
      ∃ (B : CochainComplex (A) ℤ)
        (j : ∀ n : ℕ, D.obj n ⟶ B) (u : B ⟶ B),
        Nonempty (IsColimit (Cofan.mk B j)) ∧
        (∀ n : ℕ, j n ≫ u = j n - D.map (homOfLE (Nat.le_succ n)) ≫ j (n + 1)) ∧
        ∃ (p : mappingCone u ⟶ K) (r : mappingCone u ⟶ colimit D)
          (b : colimit D ⟶ K),
          (∀ n : ℕ, j n ≫ mappingCone.inr u ≫ p = q n ≫ K.ιTruncLE (n : ℤ)) ∧
          (mappingCone.inl u).comp (HomComplex.Cochain.ofHom p) (add_zero _) = 0 ∧
          QuasiIso p ∧
          (∀ n : ℕ, j n ≫ mappingCone.inr u ≫ r = colimit.ι D n) ∧
          (mappingCone.inl u).comp (HomComplex.Cochain.ofHom r) (add_zero _) = 0 ∧
          QuasiIso r ∧
          (∀ n : ℕ, colimit.ι D n ≫ b = q n ≫ K.ιTruncLE (n : ℤ)) ∧
          QuasiIso b ∧ r ≫ b = p ∧
          (∃ (T : ℕ ⥤ CochainComplex (A) ℤ)
            (e : ∀ n : ℕ, T.obj n ≅ K.truncLE (n : ℤ))
            (ι : T ⟶ (Functor.const ℕ).obj K) (α : D ⟶ T),
            (∀ n : ℕ, ι.app n = (e n).hom ≫ K.ιTruncLE (n : ℤ)) ∧
            (∀ n : ℕ, α.app n ≫ (e n).hom = q n) ∧
            Nonempty (IsColimit (Cocone.mk K ι)) ∧
            (∀ i : ℤ, Nonempty (IsColimit
              ((HomologicalComplex.eval _ (.up ℤ) i).mapCocone (Cocone.mk K ι)))) ∧
            ∃ g : colimit T ≅ K,
              (∀ n : ℕ, colimit.ι T n ≫ g.hom = ι.app n) ∧
              colim.map α ≫ g.hom = b ∧ QuasiIso (colim.map α)) ∧
          (∀ i : ℤ, P
            ((mappingCone u).X i)) ∧
          KP (mappingCone u) ∧
          ∃ (BA : CochainComplex (A₁) ℤ)
            (jA : ∀ n : ℕ,
              (E.mapHomologicalComplex (.up ℤ)).obj
                (D.obj n) ⟶ BA)
            (tA : ∀ n : ℕ,
              (E.mapHomologicalComplex (.up ℤ)).obj
                (D.obj n) ⟶
              (E.mapHomologicalComplex (.up ℤ)).obj
                (D.obj (n + 1))) (uA : BA ⟶ BA)
            (c : (E.mapHomologicalComplex (.up ℤ)).obj
              B ≅ BA)
            (eP : (E.mapHomologicalComplex (.up ℤ)).obj
              (mappingCone u) ≅ mappingCone uA),
            (∀ n : ℕ, tA n =
              (E.mapHomologicalComplex (.up ℤ)).map
                (D.map (homOfLE (Nat.le_succ n)))) ∧
            Nonempty (IsColimit (Cofan.mk BA jA)) ∧
            (∀ n : ℕ, jA n ≫ uA = jA n - tA n ≫ jA (n + 1)) ∧
            (∀ n : ℕ,
              (E.mapHomologicalComplex (.up ℤ)).map
                (j n) ≫ c.hom = jA n) ∧
            (∀ i : ℤ, E.map
                ((mappingCone.inr u).f i) ≫ eP.hom.f i =
              c.hom.f i ≫ (mappingCone.inr uA).f i) ∧
            (∀ (i k : ℤ) (h : i + (-1) = k),
              E.map
                ((mappingCone.inl u).v i k h) ≫ eP.hom.f k =
              c.hom.f i ≫ (mappingCone.inl uA).v i k h) ∧
            (∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero
              ((E.mapHomologicalComplex (.up ℤ)).obj
                (D.obj n) |>.X i)) ∧
            (∀ (n : ℕ) (i : ℤ), Q
              ((E.mapHomologicalComplex (.up ℤ)).obj
                (D.obj n) |>.X i)) ∧
            (KQ (mappingCone uA)) ∧
            QuasiIso
              ((E.mapHomologicalComplex (.up ℤ)).map p) := by
  classical
  let L := data.L
  let ε := data.ε
  let N : ℕ ⥤ ℤ := (show Monotone (fun n : ℕ ↦ (n : ℤ)) from
    fun a b h ↦ by dsimp; exact_mod_cast h).functor
  let T := N ⋙ K.filtrationLE
  let Tm := N ⋙ K.filtrationLEMinus
  let D := Tm ⋙ L
  let q : ∀ n : ℕ, D.obj n ⟶ K.truncLE (n : ℤ) := fun n ↦ ε.app (Tm.obj n)
  have hbounded (n : ℕ) := data.bounded (Tm.obj n)
  have hterms (n : ℕ) (i : ℤ) := data.flat (Tm.obj n) i
  have hq (n : ℕ) : QuasiIso (q n) := data.quasi (Tm.obj n)
  have hepi (n : ℕ) (i : ℤ) : Epi ((q n).f i) := data.epi (Tm.obj n) i
  have hcompat (n : ℕ) : D.map (homOfLE (Nat.le_succ n)) ≫ q (n + 1) ≫
      K.ιTruncLE ((n + 1 : ℕ) : ℤ) = q n ≫ K.ιTruncLE (n : ℤ) := by
    have h := ε.naturality (Tm.map (homOfLE (Nat.le_succ n)))
    change D.map (homOfLE (Nat.le_succ n)) ≫ q (n + 1) =
      q n ≫ T.map (homOfLE (Nat.le_succ n)) at h
    rw [← Category.assoc, h, Category.assoc]
    simp [T, N, filtrationLE]
  refine ⟨D, q, hbounded, hterms, hq, hepi, hcompat, ?_⟩
  let tel := telescopeData D
  let B := tel.B
  let j := tel.j
  let u := tel.u
  have hu := tel.shift
  let r := tel.r
  have hr (n : ℕ) : j n ≫ mappingCone.inr u ≫ r = colimit.ι D n := tel.inr_r n
  have hrz := tel.inl_r
  have hrq := tel.quasi_r
  let ι : T ⟶ (Functor.const ℕ).obj K :=
    { app := fun n ↦ K.ιTruncLE (n : ℤ)
      naturality := fun n m f ↦ by simp [T, N, filtrationLE] }
  have hιeval (i : ℤ) : IsColimit
      ((HomologicalComplex.eval A (.up ℤ) i).mapCocone (Cocone.mk K ι)) := by
    apply isColimitOfIsEventuallyConstant _ (i.toNat + 1)
    intro n f
    apply isIso_ιTruncLE_f
    have hn := leOfHom f
    omega
  have hι : IsColimit (Cocone.mk K ι) := HomologicalComplex.isColimitOfEval _ _ hιeval
  let g : colimit T ≅ K := (colimit.isColimit T).coconePointUniqueUpToIso hι
  have hg (n : ℕ) : colimit.ι T n ≫ g.hom = ι.app n :=
    IsColimit.comp_coconePointUniqueUpToIso_hom _ _ n
  let α : D ⟶ T := Functor.whiskerLeft Tm ε
  have hα : QuasiIso (colim.map α) :=
    (HomologicalComplex.quasiIso A (.up ℤ)).colimMap α hq
  let b : colimit D ⟶ K := colim.map α ≫ g.hom
  have hb (n : ℕ) : colimit.ι D n ≫ b = q n ≫ K.ιTruncLE (n : ℤ) := by
    simp only [b, colimit.ι_map_assoc, hg]
    rfl
  have hbq : QuasiIso b := by
    have : QuasiIso (colim.map α) := hα
    exact quasiIso_comp (colim.map α) g.hom
  let p := r ≫ b
  have hp (n : ℕ) : j n ≫ mappingCone.inr u ≫ p = q n ≫ K.ιTruncLE (n : ℤ) := by
    dsimp [p]
    simpa only [Category.assoc] using
      (congrArg (fun f ↦ f ≫ b) (hr n)).trans (hb n)
  have hpz : (mappingCone.inl u).comp (HomComplex.Cochain.ofHom p) (add_zero _) = 0 := by
    rw [HomComplex.Cochain.ofHom_comp]
    rw [← HomComplex.Cochain.comp_assoc_of_second_is_zero_cochain, hrz,
      HomComplex.Cochain.zero_comp]
  have hpq : QuasiIso p := by
    have := hrq
    have := hbq
    dsimp [p]
    infer_instance
  refine ⟨B, j, u, ⟨tel.sum⟩, hu, p, r, b, hp, hpz, hpq,
    ?_, hrz, hrq, hb, hbq, rfl, ?_, ?_, ?_, ?_⟩
  · intro n
    exact hr n
  · refine ⟨T, fun _ ↦ Iso.refl _, ι, α, ?_, ?_, ⟨hι⟩,
      fun i ↦ ⟨hιeval i⟩, g, hg, rfl, hα⟩
    · intro n
      simp only [Iso.refl_hom, Category.id_comp]
      rfl
    · intro n
      simp only [Iso.refl_hom, Category.comp_id]
      rfl
  · exact (hclosure D.obj B j u tel.sum hbounded hterms).1
  · exact (hclosure D.obj B j u tel.sum hbounded hterms).2
  · let EC := E.mapHomologicalComplex (.up ℤ)
    let BA := EC.obj B
    let jA : ∀ n, EC.obj (D.obj n) ⟶ BA := fun n ↦ EC.map (j n)
    let tA := fun n ↦ EC.map (D.map (homOfLE (Nat.le_succ n)))
    let uA := EC.map u
    let eP := mappingCone.mapHomologicalComplexIso u E
    have hjA : IsColimit (Cofan.mk BA jA) :=
      (Cofan.isColimitMapCoconeEquiv EC D.obj (Cofan.mk B j))
        (isColimitOfPreserves EC tel.sum)
    have hAbounded (n : ℕ) : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((EC.obj (D.obj n)).X i) := by
      obtain ⟨b, hb⟩ := hbounded n
      exact ⟨b, fun i hi ↦ E.map_isZero (hb i hi)⟩
    have hAflat (n : ℕ) (i : ℤ) :
        Q ((EC.obj (D.obj n)).X i) :=
      hflat _ (hterms n i)
    refine ⟨BA, jA, tA, uA, Iso.refl _, eP, fun _ ↦ rfl, ⟨hjA⟩, ?_,
      (fun _ ↦ by simp only [Iso.refl_hom, Category.comp_id]; rfl),
      ?_, ?_, hAbounded, hAflat, ?_, ?_⟩
    · intro n
      change EC.map (j n) ≫ EC.map u = _
      rw [← EC.map_comp, hu, EC.map_sub, EC.map_comp]
    · intro i
      simpa using congrArg (fun f ↦ f.f i) (mappingCone.map_inr u E)
    · intro i k h
      change E.map ((mappingCone.inl u).v i k h) ≫
        (mappingCone.mapHomologicalComplexXIso u E k).hom =
          𝟙 _ ≫ (mappingCone.inl uA).v i k h
      rw [mappingCone.mapHomologicalComplexXIso_eq u E k i (by omega)]
      simp only [mappingCone.mapHomologicalComplexXIso'_hom, Preadditive.comp_add,
        ← Category.assoc, ← E.map_comp, mappingCone.inl_v_fst_v,
        mappingCone.inl_v_snd_v, E.map_id, E.map_zero, Category.id_comp,
        Limits.zero_comp, add_zero]
      rfl
    · exact hclosure₁ (fun n ↦ EC.obj (D.obj n)) BA jA uA hjA hAbounded hAflat
    · have := hpq
      exact HomologicalComplex.quasiIso_map_of_preservesHomology p E



/-- An exact, cocontinuous evaluation that takes flat sheaves to flat modules admits
simultaneous K-flat telescope resolutions.

Source: Hemo--Richarz--Scholbach, Lemma 4.1(1), expanded using Stacks Tags 077J and
06YS (blueprint: lem-zl-evaluation-adapted-flat-telescope).

Proof:
1. Use `lem-pc-flat-truncation-tower` to resolve every good truncation, beginning at
   zero, by a bounded-above termwise-flat complex, with strictly compatible maps to K.
2. The coproduct map a has a(1-s)=0 by compatibility. In the cone differential
   d(b,c)=(db+(1-s)c,-dc), the formula p(b,c)=a(b) is therefore a chain map.
3. `lem-pc-complex-hocolim-colimit` gives the canonical quasi-isomorphism r to the
   colimit, with zero shifted component; the universal property gives b with rb=p.
4. Monicity of the good truncation inclusions makes q a map of sequences.
   `lem-pc-kflat-hocolim-truncations` makes its filtered colimit a quasi-isomorphism.
   In degree i the truncations are K in all stages n>i, with identity transitions.
   Their canonical cocone with vertex K is thus colimiting in each degree. This
   identifies b with the induced map, and proves quasi-isomorphy of b and p.
5. `lem-pc-kflat-closure` makes each resolution, its sum and its cone K-flat.
   The cone terms are sums of flat terms, hence flat as well.
6. Cocontinuity identifies the evaluated coproduct with the coproduct of evaluations.
   Additivity identifies its shift and the entire cone differential, giving the
   comparison with the evaluated telescope on both summands. Each evaluated stage is
   bounded above and termwise flat. Apply the same K-flat closure argument to ordinary
   modules, equivalently sheaves on the one-object trivial site.
7. By `lem-sp-exact-functor-preserves-homology`, exact evaluation commutes naturally
   with homology, so evaluation of the quasi-isomorphism p is a quasi-isomorphism.
   This last step uses exactness, not preservation of arbitrary K-flat complexes. -/
theorem exists_evaluation_adapted_flat_telescope
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w}) (W : C)
    [PreservesFiniteColimits
      (SheafOfModules.evaluation.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R) (op W))]
    [PreservesColimitsOfSize.{w, w}
      (SheafOfModules.evaluation.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R) (op W))]
    (hflat : ∀ F : SheafOfModules.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R),
      SheafOfModules.IsFlatOnSite (C := C) (J := J) (R := R) F →
        Module.Flat (R.obj.obj (op W)) (F.val.obj (op W)))
    (K : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ) :
    ∃ (D : ℕ ⥤ CochainComplex (SheafOfModules.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ)
      (q : ∀ n : ℕ, D.obj n ⟶ K.truncLE (n : ℤ)),
      (∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((D.obj n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlatOnSite (C := C) (J := J) (R := R) ((D.obj n).X i)) ∧
      (∀ n : ℕ, QuasiIso (q n)) ∧
      (∀ (n : ℕ) (i : ℤ), Epi ((q n).f i)) ∧
      (∀ n : ℕ, D.map (homOfLE (Nat.le_succ n)) ≫ q (n + 1) ≫
        K.ιTruncLE ((n + 1 : ℕ) : ℤ) = q n ≫ K.ιTruncLE (n : ℤ)) ∧
      ∃ (B : CochainComplex (SheafOfModules.{w}
          ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ)
        (j : ∀ n : ℕ, D.obj n ⟶ B) (u : B ⟶ B),
        Nonempty (IsColimit (Cofan.mk B j)) ∧
        (∀ n : ℕ, j n ≫ u = j n - D.map (homOfLE (Nat.le_succ n)) ≫ j (n + 1)) ∧
        ∃ (p : mappingCone u ⟶ K) (r : mappingCone u ⟶ colimit D)
          (b : colimit D ⟶ K),
          (∀ n : ℕ, j n ≫ mappingCone.inr u ≫ p = q n ≫ K.ιTruncLE (n : ℤ)) ∧
          (mappingCone.inl u).comp (HomComplex.Cochain.ofHom p) (add_zero _) = 0 ∧
          QuasiIso p ∧
          (∀ n : ℕ, j n ≫ mappingCone.inr u ≫ r = colimit.ι D n) ∧
          (mappingCone.inl u).comp (HomComplex.Cochain.ofHom r) (add_zero _) = 0 ∧
          QuasiIso r ∧
          (∀ n : ℕ, colimit.ι D n ≫ b = q n ≫ K.ιTruncLE (n : ℤ)) ∧
          QuasiIso b ∧ r ≫ b = p ∧
          (∃ (T : ℕ ⥤ CochainComplex (SheafOfModules.{w}
              ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ)
            (e : ∀ n : ℕ, T.obj n ≅ K.truncLE (n : ℤ))
            (ι : T ⟶ (Functor.const ℕ).obj K) (α : D ⟶ T),
            (∀ n : ℕ, ι.app n = (e n).hom ≫ K.ιTruncLE (n : ℤ)) ∧
            (∀ n : ℕ, α.app n ≫ (e n).hom = q n) ∧
            Nonempty (IsColimit (Cocone.mk K ι)) ∧
            (∀ i : ℤ, Nonempty (IsColimit
              ((HomologicalComplex.eval _ (.up ℤ) i).mapCocone (Cocone.mk K ι)))) ∧
            ∃ g : colimit T ≅ K,
              (∀ n : ℕ, colimit.ι T n ≫ g.hom = ι.app n) ∧
              colim.map α ≫ g.hom = b ∧ QuasiIso (colim.map α)) ∧
          (∀ i : ℤ, SheafOfModules.IsFlatOnSite (C := C) (J := J) (R := R)
            ((mappingCone u).X i)) ∧
          IsKFlatIndependentCoefficients (C := C) (J := J) (R := R) (mappingCone u) ∧
          ∃ (BA : CochainComplex (ModuleCat.{w} (R.obj.obj (op W))) ℤ)
            (jA : ∀ n : ℕ,
              ((SheafOfModules.evaluation _ (op W)).mapHomologicalComplex (.up ℤ)).obj
                (D.obj n) ⟶ BA)
            (tA : ∀ n : ℕ,
              ((SheafOfModules.evaluation _ (op W)).mapHomologicalComplex (.up ℤ)).obj
                (D.obj n) ⟶
              ((SheafOfModules.evaluation _ (op W)).mapHomologicalComplex (.up ℤ)).obj
                (D.obj (n + 1))) (uA : BA ⟶ BA)
            (c : ((SheafOfModules.evaluation _ (op W)).mapHomologicalComplex (.up ℤ)).obj
              B ≅ BA)
            (eP : ((SheafOfModules.evaluation _ (op W)).mapHomologicalComplex (.up ℤ)).obj
              (mappingCone u) ≅ mappingCone uA),
            (∀ n : ℕ, tA n =
              ((SheafOfModules.evaluation _ (op W)).mapHomologicalComplex (.up ℤ)).map
                (D.map (homOfLE (Nat.le_succ n)))) ∧
            Nonempty (IsColimit (Cofan.mk BA jA)) ∧
            (∀ n : ℕ, jA n ≫ uA = jA n - tA n ≫ jA (n + 1)) ∧
            (∀ n : ℕ,
              ((SheafOfModules.evaluation _ (op W)).mapHomologicalComplex (.up ℤ)).map
                (j n) ≫ c.hom = jA n) ∧
            (∀ i : ℤ, (SheafOfModules.evaluation _ (op W)).map
                ((mappingCone.inr u).f i) ≫ eP.hom.f i =
              c.hom.f i ≫ (mappingCone.inr uA).f i) ∧
            (∀ (i k : ℤ) (h : i + (-1) = k),
              (SheafOfModules.evaluation _ (op W)).map
                ((mappingCone.inl u).v i k h) ≫ eP.hom.f k =
              c.hom.f i ≫ (mappingCone.inl uA).v i k h) ∧
            (∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero
              (((SheafOfModules.evaluation _ (op W)).mapHomologicalComplex (.up ℤ)).obj
                (D.obj n) |>.X i)) ∧
            (∀ (n : ℕ) (i : ℤ), Module.Flat (R.obj.obj (op W))
              (((SheafOfModules.evaluation _ (op W)).mapHomologicalComplex (.up ℤ)).obj
                (D.obj n) |>.X i)) ∧
            (∀ F : CochainComplex (ModuleCat.{w} (R.obj.obj (op W))) ℤ,
              F.Acyclic →
                (mapBifunctor F (mappingCone uA) (MonoidalCategory.curriedTensor _)).Acyclic) ∧
            QuasiIso
              (((SheafOfModules.evaluation _ (op W)).mapHomologicalComplex (.up ℤ)).map p) := by
  classical
  let A := SheafOfModules.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)
  have : AB5OfSize.{w, w} AddCommGrpCat.{w} := inferInstance
  have : AB5OfSize.{0, 0} AddCommGrpCat.{w} := AB5OfSize_shrink _
  have hExact (I : Type) [SmallCategory I] [IsFiltered I] :
      HasExactColimitsOfShape I A := by
    have : HasColimitsOfSize.{0, 0} AddCommGrpCat.{w} := inferInstance
    exact HasExactColimitsOfShape.domain_of_functor I (SheafOfModules.toSheaf _)
  have : HasExactColimitsOfShape ℕ A := hExact ℕ
  have : HasExactColimitsOfShape (Finset (Discrete ℕ)) A := hExact _
  have : HasExactColimitsOfShape (Discrete ℕ) A :=
    hasExactColimitsOfShape_discrete_of_hasExactColimitsOfShape_finset_discrete A ℕ
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.tensorPreadditive R
  have (M : A) : PreservesColimitsOfSize.{0, 0} (tensorLeft M) := by
    have := SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R M
    exact preservesColimitsOfSize_shrink _
  have (M : A) : PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  have : ∀ X₁ X₂ X₃ : GradedObject ℤ A,
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := by infer_instance
  have : ∀ X₁ X₂ X₃ : GradedObject ℤ A,
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := by infer_instance
  have : ∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A,
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := by infer_instance
  let E := SheafOfModules.evaluation
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R) (op W)
  have : PreservesColimitsOfSize.{0, 0} E := preservesColimitsOfSize_shrink E
  have : PreservesFiniteLimits E :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits _ (op W)
  have : E.Additive := by
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts E
    exact Functor.additive_of_preservesBinaryBiproducts E
  refine adapted_telescope
    (SheafOfModules.IsFlatOnSite (R := R))
    (fun M : ModuleCat.{w} (R.obj.obj (op W)) ↦ Module.Flat (R.obj.obj (op W)) M)
    (IsKFlatIndependentCoefficients (R := R))
    (fun P ↦ ∀ F, F.Acyclic → (mapBifunctor F P (curriedTensor _)).Acyclic)
    E (flatMinusData R) hflat ?_ ?_ K
  · intro D B j u hj hb hf
    constructor
    · have (M : A) : PreservesColimitsOfShape (Discrete ℕ) ((curriedTensor A).flip.obj M) :=
        preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
      have := closedUnderColimitsOfShape_flat A (Discrete ℕ)
      have ht := flat_cone_terms D B j u hj
        (fun n i ↦ SheafOfModules.flat_to_cat R _ (hf n i))
      exact fun i ↦ (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso R _).symm (ht i).2
    · have hstage (n : ℕ) : IsKFlatIndependentCoefficients (R := R) (D n) := by
        obtain ⟨b, hb⟩ := hb n
        have : (D n).IsStrictlyLE b := ((D n).isStrictlyLE_iff b).2 hb
        exact SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
          R _ b (hf n)
      intro F hF
      have hsum : (mapBifunctor F B (curriedTensor A)).Acyclic :=
        tensor_cofan_acyclic D B j hj F (fun n ↦ hstage n F hF)
      exact tensor_cone_acyclic u F hsum hsum
  · intro D B j u hj hb hf F hF
    have hsum : (mapBifunctor F B (curriedTensor _)).Acyclic :=
      tensor_cofan_acyclic D B j hj F
        (fun n ↦ bounded_module_kflat _ (hb n) (hf n) F hF)
    exact tensor_cone_acyclic u F hsum hsum

end CochainComplex
