/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import all Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatQuotientTensorSES
import Sheaf.Paper.EtaleKFlatCriteria
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Flat lower truncation and its K-flat kernel

Source: Stacks Project, Cohomology on Sites, Tag 0F1M
(lemma-bounded-below-tor-amplitude), lower truncation and kernel paragraphs
(blueprint: lem-kun-lower-truncation-flat-model).

The constant ring sheaf is the sheafification of the constant ring presheaf.
`K.truncGE a` and `K.πTruncGE a` are the existing good truncation and quotient map.
Its boundary object `K.opcycles a` is the cokernel of `K.d (a - 1) a`.
`kernel (K.πTruncGE a)` is the kernel in the category of complexes, whose
limits are computed degreewise. The boundary identification below commutes with
its inclusion into `K.X a`. Together with the chain-map equation for the kernel
inclusion, this identifies the boundary differential with the image factorization.
The lower-degree inclusions are isomorphisms, and the terms above `a` are zero.

The site has object universe `u + 1` and morphism universe `u`, and is small in
coefficient universe `u + 1`; its small model gives the skeleton convention.
-/

@[expose] public section

set_option autoImplicit false

universe u v w uC vC

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules

/-- Stacks Tags 03EX and 03EY: the flat-quotient argument uses only a flat cover,
right exact tensor functors, symmetry, and the existing tensor-row chase. -/
private theorem flat_quotient_with_covers
    {A : Type*} [Category* A] [Abelian A] [MonoidalCategory A] [BraidedCategory A]
    [MonoidalPreadditive A]
    [∀ N : A, PreservesColimitsOfSize.{0, 0} (tensorLeft N)]
    (hcover : ∀ N : A, ∃ (P : A) (π : P ⟶ N), ObjectProperty.flat P ∧ Epi π)
    (S : ShortComplex A) (hS : S.ShortExact) (hH : ObjectProperty.flat S.X₃) :
    (∀ N : A, (S.map (tensorRight N)).ShortExact) ∧
      (ObjectProperty.flat S.X₂ → ObjectProperty.flat S.X₁) := by
  have hright (N : A) : Limits.PreservesFiniteColimits (tensorRight N) :=
    Limits.preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight N)
  have hrex (T : ShortComplex A) (hT : T.ShortExact) (N : A) :
      (T.map (tensorRight N)).Exact ∧ Epi ((tensorRight N).map T.g) := by
    have := hright N
    exact (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
      (tensorRight N)).1 inferInstance T hT
  have hlex (N : A) (hN : ObjectProperty.flat N) : Limits.PreservesFiniteLimits (tensorLeft N) := by
    have : Limits.PreservesFiniteLimits (tensorRight N) := hN.2.1
    exact Limits.preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight N).symm
  have hleftrex (T : ShortComplex A) (hT : T.ShortExact) (N : A) :
      (T.map (tensorLeft N)).Exact ∧ Epi ((tensorLeft N).map T.g) :=
    (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
      (tensorLeft N)).1 inferInstance T hT
  have hseq (N : A) : (S.map (tensorRight N)).ShortExact := by
    obtain ⟨P, π, hP, hπ⟩ := hcover N
    have : Epi π := hπ
    let T := ShortComplex.kernelSequence π
    have : Epi T.g := hπ
    have hT : T.ShortExact := ⟨ShortComplex.kernelSequence_exact _⟩
    have : Limits.PreservesFiniteLimits (tensorRight T.X₂) := hP.2.1
    have := hright T.X₂
    have hmiddle := hS.map_of_exact (tensorRight T.X₂)
    have := hmiddle.mono_f
    let φ := S.mapNatTrans ((curriedTensor A).flip.map T.f)
    let ψ := S.mapNatTrans ((curriedTensor A).flip.map T.g)
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
  have hmono (U V : A) (f : U ⟶ V) [Mono f] : Mono ((tensorLeft S.X₁).map f) := by
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

end SheafOfModules

open CochainComplex

private lemma pi_f_above {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (m r : ℤ) (hr : m < r) :
    (K.πTruncGE m).f r = (K.truncGEXIso m r hr).inv := by
  dsimp only [πTruncGE, HomologicalComplex.πTruncGE, truncGEXIso,
    HomologicalComplex.truncGEXIso, Iso.trans_inv]
  have h : (ComplexShape.embeddingUpIntGE m).f (r - m).natAbs = r := by
    change m + ((r - m).natAbs : ℤ) = r
    rw [Int.natAbs_of_nonneg (by omega)]
    omega
  have hb : ¬ (ComplexShape.embeddingUpIntGE m).BoundaryGE (r - m).natAbs := by
    rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff, Int.natAbs_eq_zero]
    omega
  rw [ComplexShape.Embedding.liftExtend_f _ _ _ h,
    HomologicalComplex.restrictionToTruncGE'_f_eq_iso_hom_iso_inv _ _ h hb]
  simp

private lemma pi_f_self {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (m : ℤ) :
    (K.πTruncGE m).f m = K.pOpcycles m ≫ (K.truncGEXIsoOpcycles m).inv := by
  dsimp only [πTruncGE, HomologicalComplex.πTruncGE, truncGEXIsoOpcycles,
    HomologicalComplex.truncGEXIsoOpcycles, Iso.trans_inv]
  have h : (ComplexShape.embeddingUpIntGE m).f 0 = m := by simp
  have hb : (ComplexShape.embeddingUpIntGE m).BoundaryGE 0 := by
    rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff]
  rw [ComplexShape.Embedding.liftExtend_f _ _ _ h,
    HomologicalComplex.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv _ _ h hb]
  simp

private theorem truncation_kernel_terms
    {C : Type uC} [Category.{vC} C] [Abelian C] (K : CochainComplex C ℤ) (a : ℤ) :
    (∀ i : ℤ, i < a → IsIso ((kernel.ι (K.πTruncGE a)).f i)) ∧
    (∀ i : ℤ, a < i → IsZero ((kernel (K.πTruncGE a)).X i)) ∧
    (∃ e : (kernel (K.πTruncGE a)).X a ≅ image (K.d (a - 1) a),
      e.hom ≫ image.ι (K.d (a - 1) a) = (kernel.ι (K.πTruncGE a)).f a ∧
      (kernel (K.πTruncGE a)).d (a - 1) a ≫ e.hom =
        (kernel.ι (K.πTruncGE a)).f (a - 1) ≫ factorThruImage (K.d (a - 1) a)) := by
  let q := K.πTruncGE a
  let L := kernel q
  let ι := kernel.ι q
  have hker (i : ℤ) : IsLimit (KernelFork.ofι (ι.f i)
      (show ι.f i ≫ q.f i = 0 by
        simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
          congrArg (fun f ↦ f.f i) (kernel.condition q))) :=
    isLimitForkMapOfIsLimit' (HomologicalComplex.eval C (.up ℤ) i)
      (kernel.condition q) (kernelIsKernel q)
  have hbelow (i : ℤ) (hi : i < a) : IsIso (ι.f i) :=
    KernelFork.IsLimit.isIso_ι _ (hker i)
      (((K.truncGE a).isZero_of_isStrictlyGE a i hi).eq_of_tgt _ _)
  have habove (i : ℤ) (hi : a < i) : IsZero (L.X i) := by
    have : IsIso (q.f i) := by
      dsimp only [q]
      rw [pi_f_above K a i hi]
      infer_instance
    exact KernelFork.IsLimit.isZero_of_mono (hker i)
  have hboundary : IsLimit (KernelFork.ofι (ι.f a)
      (show ι.f a ≫ K.pOpcycles a = 0 by
        rw [← cancel_mono (K.truncGEXIsoOpcycles a).inv, Category.assoc,
          ← pi_f_self K a, zero_comp]
        simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
          congrArg (fun f ↦ f.f a) (kernel.condition q))) := by
    apply KernelFork.isLimitOfIsLimitOfIff' (hker a) (K.pOpcycles a)
    intro W f
    rw [← cancel_mono (K.truncGEXIsoOpcycles a).inv]
    simp only [Category.assoc, ← pi_f_self, zero_comp]
    rfl
  let S := ShortComplex.mk (K.d (a - 1) a) (K.pOpcycles a) (K.d_pOpcycles _ _)
  have hS : S.Exact := ShortComplex.exact_of_g_is_cokernel _
    (K.opcyclesIsCokernel (a - 1) a (by simp))
  let e : L.X a ≅ image (K.d (a - 1) a) :=
    IsLimit.conePointUniqueUpToIso hboundary hS.isLimitImage'
  have he : e.hom ≫ image.ι (K.d (a - 1) a) = ι.f a :=
    IsLimit.conePointUniqueUpToIso_hom_comp hboundary hS.isLimitImage'
      WalkingParallelPair.zero
  have hd : L.d (a - 1) a ≫ e.hom =
      ι.f (a - 1) ≫ factorThruImage (K.d (a - 1) a) := by
    rw [← cancel_mono (image.ι (K.d (a - 1) a)), Category.assoc, he,
      Category.assoc, image.fac]
    exact (ι.comm _ _).symm
  exact ⟨hbelow, habove, e, he, hd⟩

private theorem flat_site_of_iso
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})
    {M N : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)}
    (e : M ≅ N) (hM : SheafOfModules.IsFlatOnSite.{uC, vC, w, w} (J := J) (R := R) M) :
    SheafOfModules.IsFlatOnSite.{uC, vC, w, w} (J := J) (R := R) N := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  have hM' : exactFunctor _ _ (tensorRight M) :=
    (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso R M) hM
  have hN' : exactFunctor _ _ (tensorRight N) :=
    (exactFunctor _ _).prop_of_iso ((curriedTensor _).flip.mapIso e) hM'
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R N).symm hN'

private theorem flat_site_of_zero
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})
    (M : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    (hM : IsZero M) : SheafOfModules.IsFlatOnSite.{uC, vC, w, w} (J := J) (R := R) M := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.tensorPreadditive R
  exact (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso R M).symm
    (ObjectProperty.flat_of_isZero hM).2

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- Good lower truncation of a flat complex at a flat cokernel has flat terms,
is quasi-isomorphic to the original complex, and has a bounded-above flat K-flat
kernel, with the indicated terms and a degreewise short exact sequence.
Source: Stacks Project, Tag 0F1M, lower truncation and kernel paragraphs
(blueprint: lem-kun-lower-truncation-flat-model).

Proof:
1. The cokernel universal property induces the differential out of `K.opcycles a`.
The relations `d ≫ d = 0` give the quotient chain map: zero below `a`, the
cokernel projection at `a`, and the identity above `a`, under the standard
truncation identifications (def-kun-truncations, def-pc-cochain-complex-modules).
2. Below `a`, the original homology vanishes by hypothesis. At `a`, the kernel
of the induced differential is the original cycles modulo the original boundaries.
At `a + 1`, the boundaries agree since the cokernel projection is epic; above
that degree, adjacent terms and differentials are unchanged. Thus the quotient
is a quasi-isomorphism (def-pc-acyclic-complex-modules, def-pc-quasi-iso-modules).
3. Take the kernel degreewise: it is `K.X i` below `a`, the image of the incoming
differential at `a`, and zero above. The kernel inclusion is a chain map and
its boundary inclusion is the image monomorphism, so the incoming differential
is the image factorization. Every component of the quotient is epic. This
gives the short exact sequences in all degrees (def-pc-cochain-complex-modules).
4. Apply the generic flat-quotient argument to the sequence from the image to
`K.X a` to `K.opcycles a`, reusing the tensor-row chase from
lem-weil-pbc-site-flat-quotient-tensor-ses. Independent-coefficient flat resolutions
supply flat covers, and the tensor comparison transfers categorical flatness to
site flatness. The middle and quotient are flat, so the image is flat. The displayed
terms of the truncation and kernel are therefore all flat; zero sheaves are flat.
5. The kernel vanishes above `a`. Apply lem-kun-kflat-criteria (1) to its flat
terms. The existing `isKFlatIndependentCoefficients_iff_isKFlat` identifies the
criterion's predicate with the required one (def-pc-kflat-complex). -/
theorem etale_lower_truncation_flat_model
    (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (K : CochainComplex (SheafOfModules.{u + 1}
      ((sheafCompose T.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
          (CommRingCat.of Λ)))) ℤ)
    (a : ℤ)
    (hflat : ∀ i : ℤ,
      SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (K.X i))
    (hvanish : ∀ i : ℤ, i < a → IsZero (K.homology i))
    (hquotient : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (K.opcycles a)) :
    QuasiIso (K.πTruncGE a) ∧
    (∀ i : ℤ,
      SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} ((K.truncGE a).X i)) ∧
    (∀ i : ℤ, i < a → IsIso ((kernel.ι (K.πTruncGE a)).f i)) ∧
    (∃ e : (kernel (K.πTruncGE a)).X a ≅ image (K.d (a - 1) a),
      e.hom ≫ image.ι (K.d (a - 1) a) = (kernel.ι (K.πTruncGE a)).f a ∧
      (kernel (K.πTruncGE a)).d (a - 1) a ≫ e.hom =
        (kernel.ι (K.πTruncGE a)).f (a - 1) ≫ factorThruImage (K.d (a - 1) a)) ∧
    SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (image (K.d (a - 1) a)) ∧
    (∀ i : ℤ, a < i → IsZero ((kernel (K.πTruncGE a)).X i)) ∧
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      ((kernel (K.πTruncGE a)).X i)) ∧
    CochainComplex.IsKFlatIndependentCoefficients (kernel (K.πTruncGE a)) ∧
    (∀ i : ℤ, ((ShortComplex.kernelSequence (K.πTruncGE a)).map
      (HomologicalComplex.eval _ (ComplexShape.up ℤ) i)).ShortExact) := by
  let R := (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
    (CommRingCat.of Λ)
  let M := SheafOfModules.{u + 1}
    ((sheafCompose T.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.tensorPreadditive R
  have (N : M) : PreservesColimitsOfSize.{0, 0} (tensorLeft N) := by
    have := SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R N
    exact preservesColimitsOfSize_shrink (tensorLeft N)
  let q := K.πTruncGE a
  let L := kernel q
  let ι := kernel.ι q
  have ht := truncation_kernel_terms (C := M) K a
  have hbelow := ht.1
  have habove := ht.2.1
  let e := ht.2.2.choose
  have he := ht.2.2.choose_spec.1
  have hd := ht.2.2.choose_spec.2
  let S := ShortComplex.mk (K.d (a - 1) a) (K.pOpcycles a) (K.d_pOpcycles _ _)
  have hS : S.Exact := ShortComplex.exact_of_g_is_cokernel _
    (K.opcyclesIsCokernel (a - 1) a (by simp))
  have hI : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := T.smallEtaleTopology) (R := R)
      (image (K.d (a - 1) a)) := by
    let S' := ShortComplex.mk (image.ι (K.d (a - 1) a)) (K.pOpcycles a)
      (image_ι_comp_eq_zero S.zero)
    have hS' : S'.ShortExact :=
      ⟨ShortComplex.exact_of_f_is_kernel _ hS.isLimitImage'⟩
    let F := (SheafOfModules.hasFunctorialFlatResolution_kfi R).some
    have hcover (N : M) : ∃ (P : M) (π : P ⟶ N), ObjectProperty.flat P ∧ Epi π :=
      ⟨(F.F.obj N).obj, F.π.app N, (F.F.obj N).property, inferInstance⟩
    have hf := (SheafOfModules.flat_quotient_with_covers hcover S' hS'
      (SheafOfModules.flat_to_cat R _ hquotient)).2
      (SheafOfModules.flat_to_cat R _ (hflat a))
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R _).symm hf.2
  have hP (i : ℤ) : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := T.smallEtaleTopology) (R := R)
      ((K.truncGE a).X i) := by
    rcases lt_trichotomy i a with hi | rfl | hi
    · exact flat_site_of_zero R _ ((K.truncGE a).isZero_of_isStrictlyGE a i hi)
    · exact flat_site_of_iso R (K.truncGEXIsoOpcycles i).symm hquotient
    · exact flat_site_of_iso R (K.truncGEXIso a i hi).symm (hflat i)
  have hL (i : ℤ) : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := T.smallEtaleTopology) (R := R)
      (L.X i) := by
    rcases lt_trichotomy i a with hi | rfl | hi
    · have := hbelow i hi
      exact flat_site_of_iso R (asIso (ι.f i)).symm (hflat i)
    · exact flat_site_of_iso R e.symm hI
    · exact flat_site_of_zero R _ (habove i hi)
  refine ⟨?_, hP, hbelow, ⟨e, he, hd⟩, hI, habove, hL, ?_, ?_⟩
  · rw [CochainComplex.quasiIso_πTruncGE_iff, CochainComplex.isGE_iff]
    intro i hi
    exact (K.exactAt_iff_isZero_homology i).2 (hvanish i hi)
  · exact (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat L).2
      ((etale_kflat_criteria T Λ).1 L ⟨a, habove⟩ hL)
  · have : Epi q := by
      change Epi (HomologicalComplex.πTruncGE K (ComplexShape.embeddingUpIntGE a))
      infer_instance
    have : Epi (ShortComplex.kernelSequence q).g :=
      inferInstanceAs (Epi q)
    have hseq : (ShortComplex.kernelSequence q).ShortExact :=
      ⟨ShortComplex.kernelSequence_exact q⟩
    intro i
    exact hseq.map_of_exact (HomologicalComplex.eval M (.up ℤ) i)

end AlgebraicGeometry.Scheme
