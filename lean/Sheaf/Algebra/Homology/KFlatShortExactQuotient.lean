/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import WeilConjectures.FromJoel.Algebra.Homology.Monoidal
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Homology.HomologySequence

/-! # Total tensor exactness and K-flatness for a flat quotient

Source: Stacks Project, Cohomology on Sites, Tag 0G7B,
`lemma-K-flat-two-out-of-three-ses`, used in Tag 0F1M
(blueprint: lem-kun-kflat-short-exact-quotient).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

/-- The left-injectivity chase for three tensor rows, carried out after epic refinements. -/
private theorem mono_bottom_of_tensor_rows
    {A : Type*} [Category* A] [Abelian A]
    {L M N : ShortComplex A} (φ : L ⟶ M) (ψ : M ⟶ N)
    (hL : L.Exact) [Mono M.f] [Mono φ.τ₃] [Epi ψ.τ₁]
    (w : φ.τ₁ ≫ ψ.τ₁ = 0) (w₂ : φ.τ₂ ≫ ψ.τ₂ = 0)
    (hcol : (ShortComplex.mk φ.τ₂ ψ.τ₂ w₂).Exact) : Mono N.f := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro Z x hx
  obtain ⟨Z₁, π₁, hπ₁, a, ha⟩ := surjective_up_to_refinements_of_epi ψ.τ₁ x
  have haz : (a ≫ M.f) ≫ ψ.τ₂ = 0 := by
    rw [Category.assoc, ← ψ.comm₁₂, ← Category.assoc, ← ha, Category.assoc, hx,
      Limits.comp_zero]
  obtain ⟨Z₂, π₂, hπ₂, b, hb⟩ := hcol.exact_up_to_refinements (a ≫ M.f) haz
  have hbz : b ≫ L.g = 0 := by
    rw [← cancel_mono φ.τ₃, Limits.zero_comp, Category.assoc, ← φ.comm₂₃,
      ← Category.assoc, ← hb]
    simp only [Category.assoc, M.zero, Limits.comp_zero]
  obtain ⟨Z₃, π₃, hπ₃, c, hc⟩ := hL.exact_up_to_refinements b hbz
  have heq : π₃ ≫ π₂ ≫ a = c ≫ φ.τ₁ := by
    rw [← cancel_mono M.f]
    calc
      (π₃ ≫ π₂ ≫ a) ≫ M.f = π₃ ≫ (π₂ ≫ (a ≫ M.f)) := by
        simp only [Category.assoc]
      _ = π₃ ≫ (b ≫ φ.τ₂) := by rw [hb]
      _ = c ≫ L.f ≫ φ.τ₂ := by rw [← Category.assoc, hc, Category.assoc]
      _ = (c ≫ φ.τ₁) ≫ M.f := by rw [Category.assoc, φ.comm₁₂]
  rw [← cancel_epi π₁, Limits.comp_zero, ← cancel_epi π₂, Limits.comp_zero,
    ← cancel_epi π₃, Limits.comp_zero]
  calc
    π₃ ≫ π₂ ≫ π₁ ≫ x = (π₃ ≫ π₂ ≫ a) ≫ ψ.τ₁ := by
      rw [ha]
      simp only [Category.assoc]
    _ = (c ≫ φ.τ₁) ≫ ψ.τ₁ := by rw [heq]
    _ = 0 := by rw [Category.assoc, w, Limits.comp_zero]

private theorem tensor_shortExact
    {A : Type*} [Category* A] [Abelian A] [MonoidalCategory A]
    [SymmetricCategory A] [MonoidalPreadditive A]
    [∀ N : A, PreservesFiniteColimits (tensorLeft N)]
    (hcover : Abelian.HasFunctorialFlatResolution A)
    (S : ShortComplex A) (hS : S.ShortExact)
    (hH : PreservesFiniteLimits (tensorRight S.X₃)) (N : A) :
    (S.map (tensorRight N)).ShortExact := by
  have hright (M : A) : PreservesFiniteColimits (tensorRight M) :=
    preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  have hrex (T : ShortComplex A) (hT : T.ShortExact) (M : A) :
      (T.map (tensorRight M)).Exact ∧ Epi ((tensorRight M).map T.g) := by
    have := hright M
    exact (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
      (tensorRight M)).1 inferInstance T hT
  have hleftrex (T : ShortComplex A) (hT : T.ShortExact) (M : A) :
      (T.map (tensorLeft M)).Exact ∧ Epi ((tensorLeft M).map T.g) :=
    (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
      (tensorLeft M)).1 inferInstance T hT
  obtain ⟨Λ⟩ := hcover
  let T := ShortComplex.kernelSequence (Λ.π.app N)
  have : Epi T.g := Λ.epi_π_app N
  have hT : T.ShortExact := ⟨ShortComplex.kernelSequence_exact _⟩
  have hP := (Λ.F.obj N).property
  have : PreservesFiniteLimits (tensorRight T.X₂) := hP.2.1
  have := hright T.X₂
  have hmiddle := hS.map_of_exact (tensorRight T.X₂)
  have := hmiddle.mono_f
  let φ := S.mapNatTrans ((curriedTensor A).flip.map T.f)
  let ψ := S.mapNatTrans ((curriedTensor A).flip.map T.g)
  have : Mono φ.τ₃ := by
    change Mono ((tensorLeft S.X₃).map T.f)
    have : PreservesFiniteLimits (tensorLeft S.X₃) :=
      preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight _).symm
    have := hT.mono_f
    infer_instance
  have : Epi ψ.τ₁ := (hleftrex T hT S.X₁).2
  have hw₁ : φ.τ₁ ≫ ψ.τ₁ = 0 := by
    change (tensorLeft S.X₁).map T.f ≫ (tensorLeft S.X₁).map T.g = 0
    rw [← Functor.map_comp, T.zero, Functor.map_zero]
  have hw₂ : φ.τ₂ ≫ ψ.τ₂ = 0 := by
    change (tensorLeft S.X₂).map T.f ≫ (tensorLeft S.X₂).map T.g = 0
    rw [← Functor.map_comp, T.zero, Functor.map_zero]
  have hcol : (ShortComplex.mk φ.τ₂ ψ.τ₂ hw₂).Exact :=
    (hleftrex T hT S.X₂).1
  have : Mono (S.map (tensorRight N)).f :=
    mono_bottom_of_tensor_rows φ ψ (hrex S hS T.X₁).1 hw₁ hw₂ hcol
  exact ShortComplex.ShortExact.mk' (hrex S hS N).1 this (hrex S hS N).2

private theorem functor_shortExact
    {A I : Type*} [Category* A] [Category* I] [Abelian A]
    (S : ShortComplex (I ⥤ A))
    (hS : ∀ i, (S.map ((CategoryTheory.evaluation I A).obj i)).ShortExact) :
    S.ShortExact := by
  have hf (i : I) : Mono (S.f.app i) := (hS i).mono_f
  have hg (i : I) : Epi (S.g.app i) := (hS i).epi_g
  have : Mono S.f := NatTrans.mono_of_mono_app S.f
  have : Epi S.g := NatTrans.epi_of_epi_app S.g
  refine ⟨?_⟩
  rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
  ext i
  exact (IsZero.of_iso
    ((ShortComplex.exact_iff_isZero_homology _).1 (hS i).exact)
    (S.mapHomologyIso ((CategoryTheory.evaluation I A).obj i)).symm).eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
private theorem total_tensor_shortExact
    {A : Type*} [Category* A] [Abelian A] [MonoidalCategory A]
    [SymmetricCategory A] [MonoidalPreadditive A] [HasCoproducts.{0} A] [AB4OfSize.{0} A]
    [∀ M : A, PreservesColimitsOfSize.{0, 0} (tensorLeft M)]
    [∀ M : A, PreservesColimitsOfSize.{0, 0} (tensorRight M)]
    (S : ShortComplex (CochainComplex A ℤ)) (K : CochainComplex A ℤ)
    (hS : ∀ p q : ℤ,
      ((S.map (HomologicalComplex.eval A (.up ℤ) p)).map
        (tensorRight (K.X q))).ShortExact) :
    (S.map (tensorRight K)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let I := {ij : ℤ × ℤ // ij.1 + ij.2 = n}
  let f : Discrete.functor (fun ij : I ↦ S.X₁.X ij.1.1 ⊗ K.X ij.1.2) ⟶
      Discrete.functor (fun ij : I ↦ S.X₂.X ij.1.1 ⊗ K.X ij.1.2) :=
    Discrete.natTrans (fun ij ↦ S.f.f ij.as.1.1 ▷ K.X ij.as.1.2)
  let g : Discrete.functor (fun ij : I ↦ S.X₂.X ij.1.1 ⊗ K.X ij.1.2) ⟶
      Discrete.functor (fun ij : I ↦ S.X₃.X ij.1.1 ⊗ K.X ij.1.2) :=
    Discrete.natTrans (fun ij ↦ S.g.f ij.as.1.1 ▷ K.X ij.as.1.2)
  have w : f ≫ g = 0 := by
    ext ij
    change (S.f.f ij.as.1.1 ▷ K.X ij.as.1.2) ≫
      (S.g.f ij.as.1.1 ▷ K.X ij.as.1.2) = 0
    rw [← comp_whiskerRight]
    have hw := congrArg (fun t ↦ t.f ij.as.1.1) S.zero
    change S.f.f ij.as.1.1 ≫ S.g.f ij.as.1.1 = 0 at hw
    rw [hw, MonoidalPreadditive.zero_whiskerRight]
  let T := ShortComplex.mk f g w
  have hT : T.ShortExact := functor_shortExact T (fun ij ↦ hS ij.as.1.1 ij.as.1.2)
  have h := hT.map_of_exact (colim (J := Discrete I) (C := A))
  let U := (S.map (tensorRight K)).map (HomologicalComplex.eval A (.up ℤ) n)
  apply ShortComplex.shortExact_of_iso (S₁ := T.map colim) (S₂ := U) _ h
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · dsimp only [U, ShortComplex.map_f, Iso.refl_hom, Category.comp_id, Category.id_comp]
    apply Sigma.hom_ext
    intro ij
    simp only [Category.comp_id, Category.id_comp]
    change HomologicalComplex.ιTensorObj S.X₁ K ij.1.1 ij.1.2 n ij.2 ≫
      (S.f ▷ K).f n = colimit.ι _ (Discrete.mk ij) ≫ colimMap f
    rw [ι_colimMap]
    change HomologicalComplex.ιMapBifunctor _ _ _ _ _ _ _ _ ≫
      (HomologicalComplex.mapBifunctorMap S.f (𝟙 K) (curriedTensor A) (.up ℤ)).f n = _
    rw [HomologicalComplex.ι_mapBifunctorMap]
    simp only [HomologicalComplex.id_f, curriedTensor_map_app, curriedTensor_obj_map,
      whiskerLeft_id]
    congr 1
    erw [Category.id_comp]
    rfl
  · dsimp only [U, ShortComplex.map_g, Iso.refl_hom, Category.comp_id, Category.id_comp]
    apply Sigma.hom_ext
    intro ij
    simp only [Category.comp_id, Category.id_comp]
    change HomologicalComplex.ιTensorObj S.X₂ K ij.1.1 ij.1.2 n ij.2 ≫
      (S.g ▷ K).f n = colimit.ι _ (Discrete.mk ij) ≫ colimMap g
    rw [ι_colimMap]
    change HomologicalComplex.ιMapBifunctor _ _ _ _ _ _ _ _ ≫
      (HomologicalComplex.mapBifunctorMap S.g (𝟙 K) (curriedTensor A) (.up ℤ)).f n = _
    rw [HomologicalComplex.ι_mapBifunctorMap]
    simp only [HomologicalComplex.id_f, curriedTensor_map_app, curriedTensor_obj_map,
      whiskerLeft_id]
    congr 1
    erw [Category.id_comp]
    rfl

private theorem acyclic_third
    {A : Type*} [Category* A] [Abelian A]
    (S : ShortComplex (CochainComplex A ℤ)) (hS : S.ShortExact)
    (h₁ : S.X₁.Acyclic) (h₂ : S.X₂.Acyclic) : S.X₃.Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  apply (hS.homology_exact₃ i (i + 1) (by simp)).isZero_X₂
  · exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (h₂ i)).eq_of_src _ _
  · exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (h₁ (i + 1))).eq_of_tgt _ _

private theorem acyclic_middle
    {A : Type*} [Category* A] [Abelian A]
    (S : ShortComplex (CochainComplex A ℤ)) (hS : S.ShortExact)
    (h₁ : S.X₁.Acyclic) (h₃ : S.X₃.Acyclic) : S.X₂.Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  apply (hS.homology_exact₂ i).isZero_X₂
  · exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (h₁ i)).eq_of_src _ _
  · exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (h₃ i)).eq_of_tgt _ _

private theorem acyclic_first
    {A : Type*} [Category* A] [Abelian A]
    (S : ShortComplex (CochainComplex A ℤ)) (hS : S.ShortExact)
    (h₂ : S.X₂.Acyclic) (h₃ : S.X₃.Acyclic) : S.X₁.Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  apply (hS.homology_exact₁ (i - 1) i (by simp)).isZero_X₂
  · exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (h₃ (i - 1))).eq_of_src _ _
  · exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (h₂ i)).eq_of_tgt _ _

namespace CochainComplex

set_option autoImplicit false in
/-- A degreewise short exact sequence with flat quotient stays degreewise short exact
under direct-sum total tensor with any complex; K-flatness satisfies all three
implications of two out of three. No boundedness or splitting is assumed.
Source: Stacks Project, Cohomology on Sites, Tag 0G7B
(blueprint: lem-kun-kflat-short-exact-quotient).

Proof:
1. Apply `lem-weil-pbc-site-flat-quotient-tensor-ses` in each bidegree `(p,q)`
   with quotient `S.X₃.X p` flat and arbitrary tensor factor `A.X q`.
2. The sheafified tensor symmetry of `def-pur-sheaf-tensor-product`, natural
   in the two sequence maps, gives the same exact sequence in the other orientation.
3. In total degree `n`, take finite biproducts over finite subsets of the pairs
   `(p,q)` with `p + q = n`. Their filtered colimit is the full sheaf coproduct.
   Exact filtered colimits from `lem-pur-ringed-site-grothendieck-abelian` give
   short exactness of that coproduct, in both tensor orientations.
4. The canonical tensor maps commute with the differential
   `d ⊗ 1 + (-1)^p (1 ⊗ d)` by the chain-map identities and tensor functoriality.
   Thus the degreewise sequences are precisely the asserted total tensor sequence.
   Every summand has just two outgoing differential components, even when unbounded.
5. For any acyclic test complex, K-flatness of two original complexes makes two
   left total tensors acyclic by `def-pc-kflat-complex`. The long exact cohomology
   sequence of `lem-weil-pbc-complex-ses-homology-long-exact` forces the third
   tensor to be acyclic: use the neighbors of Hⁿ of the third, first, or middle
   tensor, respectively. By `def-pc-acyclic-complex-modules` this is acyclicity
   in every integer degree. Quantifying over all acyclic tests proves each of
   the three K-flatness implications. -/
theorem kflat_shortExact_flat_quotient
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})
    (S : ShortComplex (CochainComplex (ringedSiteModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ))
    (hS : S.ShortExact)
    (hP : ∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (S.X₃.X i)) :
    (∀ A : CochainComplex (ringedSiteModules.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ,
      (∃ h : (S.f ▷ A) ≫ (S.g ▷ A) = 0,
        (ShortComplex.mk (S.f ▷ A) (S.g ▷ A) h).ShortExact)) ∧
    (S.X₁.IsKFlatIndependentCoefficients → S.X₂.IsKFlatIndependentCoefficients →
      S.X₃.IsKFlatIndependentCoefficients) ∧
    (S.X₁.IsKFlatIndependentCoefficients → S.X₃.IsKFlatIndependentCoefficients →
      S.X₂.IsKFlatIndependentCoefficients) ∧
    (S.X₂.IsKFlatIndependentCoefficients → S.X₃.IsKFlatIndependentCoefficients →
      S.X₁.IsKFlatIndependentCoefficients) := by
  let A := ringedSiteModules.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)
  have (M : A) : PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
    SheafOfModules.cochainTensorLeftPreservesColimits R M
  have (M : A) : PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
    SheafOfModules.cochainTensorRightPreservesColimits R M
  have : ∀ X Y : GradedObject ℤ A, GradedObject.HasTensor X Y := by infer_instance
  have : ∀ X Y Z : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X Y Z := by
    infer_instance
  have : ∀ X Y Z : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X Y Z := by
    infer_instance
  have : ∀ W X Y Z : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt W X Y Z := by
    infer_instance
  have : AB4OfSize.{0} AddCommGrpCat.{w} := AB4OfSize_shrink _
  have (I : Type) : HasColimitsOfShape (Discrete I) (Sheaf J AddCommGrpCat.{w}) :=
    ⟨fun D ↦ HasColimit.mk ⟨
      Sheaf.sheafifyCocone (colimit.cocone (D ⋙ sheafToPresheaf J AddCommGrpCat.{w})),
      Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩⟩
  have (I : Type) : HasExactColimitsOfShape (Discrete I) (Sheaf J AddCommGrpCat.{w}) :=
    CategoryTheory.Sheaf.hasExactColimitsOfShape J
  have : AB4OfSize.{0} A := ⟨fun I ↦
    HasExactColimitsOfShape.domain_of_functor (Discrete I) (SheafOfModules.toSheaf _)⟩
  have hflat (i : ℤ) : PreservesFiniteLimits (tensorRight (S.X₃.X i)) := by
    have h := (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (S.X₃.X i)) (hP i)
    exact h.1
  have hr (K : CochainComplex A ℤ) : (S.map (tensorRight K)).ShortExact := by
    apply total_tensor_shortExact S K
    intro p q
    exact tensor_shortExact (SheafOfModules.hasFunctorialFlatResolution_kfi R)
      (S.map (HomologicalComplex.eval A (.up ℤ) p))
      (hS.map_of_exact _) (hflat p) (K.X q)
  have hl (K : CochainComplex A ℤ) : (S.map (tensorLeft K)).ShortExact :=
    ShortComplex.shortExact_of_iso
      (S.mapNatIso (BraidedCategory.tensorLeftIsoTensorRight K)).symm (hr K)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K
    exact ⟨(S.map (tensorRight K)).zero, hr K⟩
  · intro h₁ h₂ K hK
    exact acyclic_third (S.map (tensorLeft K)) (hl K) (h₁ K hK) (h₂ K hK)
  · intro h₁ h₃ K hK
    exact acyclic_middle (S.map (tensorLeft K)) (hl K) (h₁ K hK) (h₃ K hK)
  · intro h₂ h₃ K hK
    exact acyclic_first (S.map (tensorLeft K)) (hl K) (h₂ K hK) (h₃ K hK)

end CochainComplex
