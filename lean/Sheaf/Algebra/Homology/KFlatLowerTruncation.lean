/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.Algebra.Homology.HomologySequence
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorColimits
import WeilConjectures.FromJoel.Algebra.Homology.Bifunctor

/-! # Lower truncation of a flat K-flat complex

Source: Stacks Project, Tags 0F1M and 0G7B.
(blueprint: lem-kun-kflat-lower-truncation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2000
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CochainComplex

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



section Tensor
variable {M : Type u} [Category.{v} M] [Abelian M]
  [MonoidalCategory M] [SymmetricCategory M] [MonoidalPreadditive M]
  [∀ N : M, PreservesColimitsOfSize.{0, 0} (tensorLeft N)]
  [Abelian.HasFunctorialFlatResolution M]

set_option backward.isDefEq.respectTransparency false in
private theorem tensor_ses
    (S : ShortComplex M)
    (hS : S.ShortExact) (hH : ObjectProperty.flat S.X₃) :
    (∀ N, (S.map (tensorRight N)).ShortExact) ∧
      (ObjectProperty.flat S.X₂ → ObjectProperty.flat S.X₁) := by
  have hright (N : M) : Limits.PreservesFiniteColimits (tensorRight N) := by
    have : PreservesFiniteColimits (tensorLeft N) := inferInstance
    exact Limits.preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight N)
  have hrex (T : ShortComplex M) (hT : T.ShortExact) (N : M) :
      (T.map (tensorRight N)).Exact ∧ Epi ((tensorRight N).map T.g) := by
    have := hright N
    exact (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
      (tensorRight N)).1 inferInstance T hT
  have hlex (N : M) (hN : ObjectProperty.flat N) : Limits.PreservesFiniteLimits (tensorLeft N) := by
    have : Limits.PreservesFiniteLimits (tensorRight N) := hN.2.1
    exact Limits.preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight N).symm
  have hleftrex (T : ShortComplex M) (hT : T.ShortExact) (N : M) :
      (T.map (tensorLeft N)).Exact ∧ Epi ((tensorLeft N).map T.g) :=
    (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
      (tensorLeft N)).1 inferInstance T hT
  have hseq (N : M) : (S.map (tensorRight N)).ShortExact := by
    let L := Classical.choice (inferInstance : Abelian.HasFunctorialFlatResolution M)
    let π := L.π
    have hP := (L.F.obj N).property
    have : Epi (π.app N) := L.epi_π_app N
    let T := ShortComplex.kernelSequence (π.app N)
    have : Epi T.g := L.epi_π_app N
    have hT : T.ShortExact := ⟨ShortComplex.kernelSequence_exact _⟩
    have : Limits.PreservesFiniteLimits (tensorRight T.X₂) := hP.2.1
    have := hright T.X₂
    have hmiddle := hS.map_of_exact (tensorRight T.X₂)
    have := hmiddle.mono_f
    let φ := S.mapNatTrans ((curriedTensor M).flip.map T.f)
    let ψ := S.mapNatTrans ((curriedTensor M).flip.map T.g)
    have : Mono φ.τ₃ := by
      change Mono ((tensorLeft S.X₃).map T.f)
      have := hlex S.X₃ hH
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
  refine ⟨hseq, ?_⟩
  intro hG
  have hmono (U V : M) (f : U ⟶ V) [Mono f] : Mono ((tensorLeft S.X₁).map f) := by
    have : Mono (S.f ▷ U) := (hseq U).mono_f
    have := hlex S.X₂ hG
    have : Mono (S.X₂ ◁ f) := (tensorLeft S.X₂).map_mono f
    have hcomp : Mono ((S.f ▷ U) ≫ (S.X₂ ◁ f)) := mono_comp _ _
    have hfac : (S.X₁ ◁ f) ≫ (S.f ▷ V) = (S.f ▷ U) ≫ (S.X₂ ◁ f) :=
      whisker_exchange S.f f
    exact mono_of_mono_fac hfac
  have : (tensorLeft S.X₁).PreservesMonomorphisms := ⟨fun f _ ↦ hmono _ _ f⟩
  have : Limits.PreservesFiniteLimits (tensorLeft S.X₁) := by
    apply (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
      (tensorLeft S.X₁)).2
    intro T hT
    have := hT.mono_f
    exact ⟨(hleftrex T hT S.X₁).1, inferInstance⟩
  exact ⟨(exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩,
    (exactFunctor_iff _).2 ⟨Limits.preservesFiniteLimits_of_natIso
      (BraidedCategory.tensorLeftIsoTensorRight S.X₁), hright S.X₁⟩⟩

variable [HasColimitsOfSize.{0, 0} M]

local instance (K L : CochainComplex M ℤ) :
    CochainComplex.HasMapBifunctor K L (curriedTensor M) := by
  intro n
  exact HasColimitsOfShape.has_colimit _

set_option backward.isDefEq.respectTransparency false in
private def totalTensorXIso
    (K A : CochainComplex M ℤ) (n : ℤ) :
      ∐ (fun p : ℤ ↦ K.X p ⊗ A.X (n - p)) ≅
        (CochainComplex.mapBifunctor K A (curriedTensor _)).X n := by
  refine ⟨Sigma.desc (fun p ↦ HomologicalComplex.ιMapBifunctor K A
    (curriedTensor _) (.up ℤ) p (n - p) n (by change p + (n - p) = n; omega)),
    HomologicalComplex.mapBifunctorDesc (fun p q hpq ↦
      eqToHom (congrArg (fun q ↦ K.X p ⊗ A.X q)
        (show q = n - p by change p + q = n at hpq; omega)) ≫
          Sigma.ι (fun p : ℤ ↦ K.X p ⊗ A.X (n - p)) p), ?_, ?_⟩
  · ext p
    simp only [Sigma.ι_desc_assoc, HomologicalComplex.ι_mapBifunctorDesc]
    simp
  · apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    have hq : q = n - p := by dsimp at hpq; omega
    subst q
    simp

omit [SymmetricCategory M]
  [∀ N : M, PreservesColimitsOfSize.{0, 0} (tensorLeft N)]
  [Abelian.HasFunctorialFlatResolution M] in
private theorem totalTensorXIso_hom
    (K A : CochainComplex M ℤ) (n : ℤ) :
    (totalTensorXIso K A n).hom = Sigma.desc (fun p ↦
      HomologicalComplex.ιMapBifunctor K A (curriedTensor _) (.up ℤ)
        p (n - p) n (by change p + (n - p) = n; omega)) := rfl

attribute [local irreducible] totalTensorXIso

variable [HasExactColimitsOfShape (Discrete ℤ) M]

set_option backward.isDefEq.respectTransparency false in
private theorem total_tensor_ses
    (S : ShortComplex (CochainComplex M ℤ))
    (hS : S.ShortExact)
    (hflat : ∀ i, ObjectProperty.flat (S.X₃.X i))
    (A : CochainComplex M ℤ) :
    (S.map (((curriedTensor _).map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ)).flip.obj A)).ShortExact := by
  classical
  have := hS.mono_f
  have := hS.epi_g
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let D : ℤ → ShortComplex M := fun p ↦
    (S.map (HomologicalComplex.eval _ (.up ℤ) p)).map (tensorRight (A.X (n - p)))
  have hD (p : ℤ) : (D p).ShortExact :=
    (tensor_ses _ (hS.map (HomologicalComplex.eval _ (.up ℤ) p)) (hflat p)).1 _
  let U : ShortComplex (Discrete ℤ ⥤ M) :=
    { X₁ := Discrete.functor (fun p ↦ (D p).X₁)
      X₂ := Discrete.functor (fun p ↦ (D p).X₂)
      X₃ := Discrete.functor (fun p ↦ (D p).X₃)
      f := Discrete.natTrans (fun p ↦ (D p.as).f)
      g := Discrete.natTrans (fun p ↦ (D p.as).g)
      zero := by
        apply NatTrans.ext
        funext p
        change (D p.as).f ≫ (D p.as).g = 0
        exact (D p.as).zero }
  have (p : Discrete ℤ) : Mono (U.f.app p) := (hD p.as).mono_f
  have (p : Discrete ℤ) : Epi (U.g.app p) := (hD p.as).epi_g
  have : Mono U.f := NatTrans.mono_of_mono_app _
  have : Epi U.g := NatTrans.epi_of_epi_app _
  have hU : U.ShortExact := by
    refine { exact := ?_ }
    rw [ShortComplex.exact_iff_isZero_homology, Functor.isZero_iff]
    intro p
    exact IsZero.of_iso
      ((ShortComplex.exact_iff_isZero_homology _).1 (hD p.as).exact)
      (U.mapHomologyIso ((CategoryTheory.evaluation (Discrete ℤ) M).obj p)).symm
  have hcol := hU.map_of_exact (colim (J := Discrete ℤ) (C := M))
  let T := S.map (((curriedTensor M).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ)).flip.obj A)
  let e := fun K ↦ totalTensorXIso K A n
  apply ShortComplex.shortExact_of_iso _ hcol
  refine ShortComplex.isoMk (e S.X₁) (e S.X₂) (e S.X₃) ?_ ?_
  all_goals
    apply Sigma.hom_ext
    intro p
    simp only [e, totalTensorXIso_hom, ShortComplex.map_f, ShortComplex.map_g,
      Functor.flip_obj_map, Functor.map₂HomologicalComplex_map_app,
      HomologicalComplex.eval_map, Sigma.ι_desc_assoc]
  · change _ = colimit.ι U.X₁ (Discrete.mk p) ≫ colim.map U.f ≫ _
    rw [colimit.ι_map_assoc]
    rw [HomologicalComplex.ι_mapBifunctorMap]
    simp only [HomologicalComplex.id_f]
    change (S.f.f p ▷ A.X (n - p)) ≫ (S.X₂.X p ◁ 𝟙 _) ≫ _ =
      (S.f.f p ▷ A.X (n - p)) ≫
        Sigma.ι (fun p : ℤ ↦ S.X₂.X p ⊗ A.X (n - p)) p ≫ _
    simp only [whiskerLeft_id, Category.id_comp, Sigma.ι_desc]
  · change _ = colimit.ι U.X₂ (Discrete.mk p) ≫ colim.map U.g ≫ _
    rw [colimit.ι_map_assoc]
    rw [HomologicalComplex.ι_mapBifunctorMap]
    simp only [HomologicalComplex.id_f]
    change (S.g.f p ▷ A.X (n - p)) ≫ (S.X₃.X p ◁ 𝟙 _) ≫ _ =
      (S.g.f p ▷ A.X (n - p)) ≫
        Sigma.ι (fun p : ℤ ↦ S.X₃.X p ⊗ A.X (n - p)) p ≫ _
    simp only [whiskerLeft_id, Category.id_comp, Sigma.ι_desc]

end Tensor


set_option backward.isDefEq.respectTransparency false in
/-- Lower truncation stays K-flat when the boundary opcycles are flat.
Source: Stacks Project, Tag 0F1M, kernel argument using Tag 0G7B
(blueprint: lem-kun-kflat-lower-truncation).

Proof: the kernel of the quotient K to its lower good truncation has K's
terms below a, the image of the incoming differential at a, and zero above a.
The short exact sequence from this image to K^a to the opcycles has flat
middle and last terms, hence flat first term. The kernel complex is therefore
bounded above and flat, hence K-flat. Tensor the quotient short exact sequence
with any acyclic complex. The flat quotient terms make the sequences exact in
every bidegree, and exact coproducts make the total sequence short exact.
Its first two terms are acyclic by K-flatness, so the long exact homology
sequence makes the last term acyclic. This is K-flatness of the truncation. -/
theorem isKFlatIndependentCoefficients_truncGE
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasSheafify J AddCommGrpCat.{w}]
    (R : Sheaf J CommRingCat.{w})
    (K : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ)
    (a : ℤ) (hK : IsKFlatIndependentCoefficients (R := R) K)
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (K.X i))
    (hop : SheafOfModules.IsFlatOnSite (J := J) (R := R) (K.opcycles a)) :
    IsKFlatIndependentCoefficients (R := R) (K.truncGE a) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory.{v, u, w} R
  let := SheafOfModules.tensorPreadditive R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let M := SheafOfModules.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)
  let := SheafOfModules.hasFunctorialFlatResolution_kfi R
  have : AB5OfSize.{w, w} AddCommGrpCat.{w} := inferInstance
  have : AB5OfSize.{0, 0} AddCommGrpCat.{w} := AB5OfSize_shrink _
  have : HasColimitsOfSize.{0, 0} AddCommGrpCat.{w} :=
    hasColimitsOfSizeShrink.{0, 0, w, w, w, w + 1} _
  have : HasColimitsOfSize.{0, 0} (Sheaf J AddCommGrpCat.{w}) := inferInstance
  have : HasColimitsOfSize.{0, 0} M := inferInstance
  have (A B : CochainComplex M ℤ) :
      CochainComplex.HasMapBifunctor A B (curriedTensor M) := by
    intro n
    exact HasColimitsOfShape.has_colimit _
  have : HasColimitsOfShape (Discrete ℤ) AddCommGrpCat.{w} := inferInstance
  have : HasColimitsOfShape (Discrete ℤ) (Sheaf J AddCommGrpCat.{w}) :=
    Sheaf.instHasColimitsOfShape (J := J) (D := AddCommGrpCat.{w}) (K := Discrete ℤ)
  have : HasExactColimitsOfShape (Discrete ℤ) (Sheaf J AddCommGrpCat.{w}) :=
    Sheaf.hasExactColimitsOfShape J
  have : HasExactColimitsOfShape (Discrete ℤ) M :=
    HasExactColimitsOfShape.domain_of_functor (Discrete ℤ) (SheafOfModules.toSheaf _)
  have (N : M) : PreservesColimitsOfSize.{0, 0} (tensorLeft N) := by
    have := SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R N
    exact preservesColimitsOfSize_shrink (tensorLeft N)
  have (N : M) : PreservesColimitsOfSize.{0, 0} (tensorRight N) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight N)
  have : ∀ X₁ X₂ : GradedObject ℤ M, GradedObject.HasTensor X₁ X₂ := by infer_instance
  have : ∀ X₁ X₂ X₃ : GradedObject ℤ M,
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := by infer_instance
  have : ∀ X₁ X₂ X₃ : GradedObject ℤ M,
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := by infer_instance
  have : ∀ X₁ X₂ X₃ X₄ : GradedObject ℤ M,
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := by infer_instance
  have flat_iso {X Y : M} (e : X ≅ Y)
      (h : SheafOfModules.IsFlatOnSite (J := J) (R := R) Y) :
      SheafOfModules.IsFlatOnSite (J := J) (R := R) X := by
    have hY := SheafOfModules.flat_to_cat R Y h
    have hX := ObjectProperty.prop_of_iso ObjectProperty.flat e.symm hY
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R X).symm hX.2
  have flat_zero {X : M} (h : IsZero X) :
      SheafOfModules.IsFlatOnSite (J := J) (R := R) X := by
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R X).symm
      (ObjectProperty.flat_of_isZero h).2
  let P := K.truncGE a
  have hP (i : ℤ) : SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X i) := by
    obtain hi | hi | hi := lt_trichotomy i a
    · exact flat_zero (P.isZero_of_isStrictlyGE a i hi)
    · subst i
      exact flat_iso (K.truncGEXIsoOpcycles a) hop
    · exact flat_iso (K.truncGEXIso a i hi) (hflat i)
  have : Epi (K.πTruncGE a) :=
    inferInstanceAs (Epi (HomologicalComplex.πTruncGE K
      (ComplexShape.embeddingUpIntGE a)))
  let S := ShortComplex.kernelSequence (K.πTruncGE a)
  have : Epi S.g := inferInstanceAs (Epi (K.πTruncGE a))
  have hS : S.ShortExact := ⟨ShortComplex.kernelSequence_exact _⟩
  have hL (i : ℤ) : SheafOfModules.IsFlatOnSite (J := J) (R := R) (S.X₁.X i) := by
    have h := (tensor_ses _ (hS.map (HomologicalComplex.eval _ (.up ℤ) i))
      (SheafOfModules.flat_to_cat R _ (hP i))).2
      (SheafOfModules.flat_to_cat R _ (hflat i))
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R _).symm h.2
  have : S.X₁.IsStrictlyLE a := by
    apply (S.X₁.isStrictlyLE_iff a).2
    intro i hi
    have hiso : IsIso ((K.πTruncGE a).f i) := by
      change IsIso ((HomologicalComplex.πTruncGE K
        (ComplexShape.embeddingUpIntGE a)).f i)
      dsimp [HomologicalComplex.πTruncGE]
      rw [ComplexShape.Embedding.isIso_liftExtend_f_iff _ _ _
        (show (ComplexShape.embeddingUpIntGE a).f (i - a).natAbs = i by
          change a + (i - a).natAbs = i
          rw [Int.natAbs_of_nonneg (by omega)]; omega)]
      apply HomologicalComplex.isIso_restrictionToTruncGE'
      rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff, Int.natAbs_eq_zero]
      omega
    have hs := hS.map (HomologicalComplex.eval _ (.up ℤ) i)
    have : Mono ((K.πTruncGE a).f i) := inferInstance
    have hf : S.f.f i = 0 := by
      rw [← cancel_mono ((K.πTruncGE a).f i), Limits.zero_comp]
      exact congrArg (fun f ↦ f.f i) S.zero
    have := hs.mono_f
    rw [IsZero.iff_id_eq_zero, ← cancel_mono (S.f.f i), hf]
    simp
  have hkL := SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
    R S.X₁ a hL
  intro A hA
  have ht := total_tensor_ses S hS (fun i ↦
    SheafOfModules.flat_to_cat R _ (hP i)) A
  have hzL : (mapBifunctor S.X₁ A (curriedTensor M)).Acyclic := by
    have hz := hkL A hA
    exact fun i ↦ (hz i).of_iso (β_ A S.X₁)
  have hzK : (mapBifunctor K A (curriedTensor M)).Acyclic := by
    have hz := hK A hA
    exact fun i ↦ (hz i).of_iso (β_ A K)
  have hzP : (mapBifunctor P A (curriedTensor M)).Acyclic := by
    intro i
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (ht.homology_exact₃ i (i + 1) (by simp)).isZero_X₂
      ((hzK i).isZero_homology.eq_of_src _ _)
      ((hzL (i + 1)).isZero_homology.eq_of_tgt _ _)
  exact fun i ↦ (hzP i).of_iso (β_ P A)

end CochainComplex
