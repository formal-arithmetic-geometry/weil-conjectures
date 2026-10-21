/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.Paper.ExactScalarPeriodicResolution
public import Sheaf.Algebra.Homology.RingedKFlatSingleTensorComparison
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # The zero-differential normal form of a periodic tensor

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-def-localizing-closure-ctf-equals-bc.proof.md, "The examples"; Stacks Tags 03EK, 06YU.
(blueprint: lem-sfb-periodic-tensor-normal-form)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r w

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open SheafOfModules.KFlatFixedTensor

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

/-- The prescribed normal form has M in every nonpositive degree and zero differential.
Source: blueprint, "The examples" (blueprint: lem-sfb-periodic-tensor-normal-form). -/
def periodicTensorZeroComplex (M : Modules R) : CochainComplex (Modules R) ℤ where
  X := CochainComplex.scalarPeriodicX M
  d := fun _ _ ↦ 0

/-- The nonpositive term of the normal form is M itself.
Source: blueprint, "The examples" (blueprint: lem-sfb-periodic-tensor-normal-form). -/
def periodicTensorZeroXIso (M : Modules R) (i : ℤ) (hi : i ≤ 0) :
    (periodicTensorZeroComplex R M).X i ≅ M := eqToIso (if_pos hi)

/-- The induced normal-form map is f in nonpositive degrees and zero above zero.
Source: blueprint, "The examples" (blueprint: lem-sfb-periodic-tensor-normal-form). -/
def periodicTensorZeroMap {M N : Modules R} (f : M ⟶ N) :
    periodicTensorZeroComplex R M ⟶ periodicTensorZeroComplex R N where
  f i := if hi : i ≤ 0 then
    (periodicTensorZeroXIso R M i hi).hom ≫ f ≫
      (periodicTensorZeroXIso R N i hi).inv else 0
  comm' _ _ _ := comp_zero.trans zero_comp.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalar_tensor_zero
    (t : (unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)).sections)
    (M : Modules R)
    (hM : ∀ (U : Cᵒᵖ) (m : M.val.obj U), (@id (R.obj.obj U) (t.val U)) • m = 0) :
    ((ordinaryTensor R).map (exactScalarMultiplication R t)).app M = 0 := by
  let := cochainModulesMonoidal R
  let A : Sheaf J RingCat.{r} :=
    (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R
  let S := PresheafOfModules.sheafification.{r} (R := A) (𝟙 A.obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{r} (R := A) (𝟙 A.obj)
  let f := exactScalarMultiplication R t
  change f ▷ M = 0
  have hp : f.val ▷ M.val = 0 := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro a m
    change ((@id (R.obj.obj U) a) * (@id (R.obj.obj U) (t.val U))) ⊗ₜ[R.obj.obj U] m = 0
    rw [mul_comm, ← smul_eq_mul, TensorProduct.smul_tmul, hM, TensorProduct.tmul_zero]
  have hs : S.map f.val ▷ S.obj M.val = 0 := by
    apply (cancel_mono (Functor.LaxMonoidal.μ S _ _)).mp
    rw [Functor.LaxMonoidal.μ_natural_left, hp, S.map_zero, comp_zero, zero_comp]
  let a : S.obj (unit A).val ⟶ unit A := adj.counit.app (unit A)
  let b : S.obj M.val ⟶ M := adj.counit.app M
  have : IsIso a := by dsimp [a]; infer_instance
  have : IsIso b := by dsimp [b]; infer_instance
  have hn : S.map f.val ≫ a = a ≫ f := adj.counit.naturality f
  apply (cancel_epi (a ⊗ₘ b)).mp
  rw [comp_zero]
  calc
    _ = (S.map f.val ▷ S.obj M.val) ≫ (a ⊗ₘ b) := by
      rw [tensorHom_comp_whiskerRight, ← hn, ← whiskerRight_comp_tensorHom]
    _ = 0 := by rw [hs, zero_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem periodic_tensor_d_zero
    (t : (unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)).sections)
    (ht : ∀ U : Cᵒᵖ, (@id (R.obj.obj U) (t.val U)) * (@id (R.obj.obj U) (t.val U)) = 0)
    (M : Modules R)
    (hM : ∀ (U : Cᵒᵖ) (m : M.val.obj U), (@id (R.obj.obj U) (t.val U)) • m = 0)
    (i j : ℤ) :
    ((ordinaryTensor R).flip.obj M).map ((exactScalarPeriodicComplex R t ht).d i j) = 0 := by
  by_cases hij : i + 1 = j
  · subst j
    change ((ordinaryTensor R).flip.obj M).map
      ((CochainComplex.scalarPeriodic (exactScalarMultiplication R t)
        (exactScalarMultiplication_sq R t ht)).d i (i + 1)) = 0
    simp only [CochainComplex.scalarPeriodic, CochainComplex.of_d]
    by_cases hi : i < 0
    · have hz : ((ordinaryTensor R).flip.obj M).map
          (exactScalarMultiplication R t) = 0 := scalar_tensor_zero R t M hM
      simp only [CochainComplex.scalarPeriodicD, dif_pos hi,
        CochainComplex.scalarPeriodicX, Functor.map_comp, hz, comp_zero, zero_comp]
    · simp [CochainComplex.scalarPeriodicD, hi]
  · rw [HomologicalComplex.shape _ _ _ hij]
    exact ((ordinaryTensor R).flip.obj M).map_zero _ _

private def periodic_tensor_term_iso
    (t : (unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)).sections)
    (ht : ∀ U : Cᵒᵖ, (@id (R.obj.obj U) (t.val U)) * (@id (R.obj.obj U) (t.val U)) = 0)
    (M : Modules R) (i : ℤ) :
    ((ordinaryTensor R).flip.obj M).obj ((exactScalarPeriodicComplex R t ht).X i) ≅
      (periodicTensorZeroComplex R M).X i :=
  if hi : i ≤ 0 then
    ((ordinaryTensor R).flip.obj M).mapIso (CochainComplex.scalarPeriodicXIso
      (exactScalarMultiplication R t) (exactScalarMultiplication_sq R t ht) i hi) ≪≫
        λ_ M ≪≫ (periodicTensorZeroXIso R M i hi).symm
  else
    (((ordinaryTensor R).flip.obj M).map_isZero
      (IsZero.of_iso (isZero_zero _) (eqToIso (if_neg hi)))).isoZero ≪≫
        (eqToIso (if_neg hi)).symm

private def periodic_tensor_termwise_iso
    (t : (unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)).sections)
    (ht : ∀ U : Cᵒᵖ, (@id (R.obj.obj U) (t.val U)) * (@id (R.obj.obj U) (t.val U)) = 0)
    (M : Modules R)
    (hM : ∀ (U : Cᵒᵖ) (m : M.val.obj U), (@id (R.obj.obj U) (t.val U)) • m = 0) :
    ((((ordinaryTensor R).flip.obj M).mapHomologicalComplex (.up ℤ)).obj
      (exactScalarPeriodicComplex R t ht)) ≅ periodicTensorZeroComplex R M :=
  HomologicalComplex.Hom.isoOfComponents (periodic_tensor_term_iso R t ht M) (by
    intro i j hij
    change _ ≫ 0 =
      ((ordinaryTensor R).flip.obj M).map ((exactScalarPeriodicComplex R t ht).d i j) ≫ _
    rw [periodic_tensor_d_zero R t ht M hM]
    simp)

private theorem single_tensor_inv (M : Modules R)
    (P : CochainComplex (Modules R) ℤ) (i : ℤ) :
    (CochainComplex.mapBifunctorSingle₂Iso (ordinaryTensor R) M P).inv.f i =
      (P.X i ◁ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv) ≫
        HomologicalComplex.ιMapBifunctor P
          ((HomologicalComplex.single _ (.up ℤ) 0).obj M)
          (ordinaryTensor R) (.up ℤ) i 0 i (by simp) := by
  dsimp only [CochainComplex.mapBifunctorSingle₂Iso, Iso.trans_inv,
    HomologicalComplex.comp_f, Iso.symm_inv]
  rw [CochainComplex.mapBifunctorSingle₁Iso_inv_f]
  rw [Category.assoc, HomologicalComplex.ι_mapBifunctorFlipIso_hom]
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
private theorem single_tensor_second_naturality
    {M N : Modules R} (f : M ⟶ N) (P : CochainComplex (Modules R) ℤ) (i : ℤ) :
    (CochainComplex.mapBifunctorSingle₂Iso (ordinaryTensor R) M P).inv.f i ≫
        (((totalTensor R).obj P).map
          ((HomologicalComplex.single _ (.up ℤ) 0).map f)).f i =
      (P.X i ◁ f) ≫
        (CochainComplex.mapBifunctorSingle₂Iso (ordinaryTensor R) N P).inv.f i := by
  rw [single_tensor_inv, single_tensor_inv]
  change (_ ≫ _) ≫ (HomologicalComplex.mapBifunctorMap (𝟙 P)
    ((HomologicalComplex.single _ (.up ℤ) 0).map f) (ordinaryTensor R) (.up ℤ)).f i = _
  rw [Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
  rw [HomologicalComplex.id_f, (ordinaryTensor R).map_id]
  simp only [NatTrans.id_app, Category.id_comp]
  rw [HomologicalComplex.single_map_f_self]
  change (P.X i ◁ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv) ≫
      (P.X i ◁ ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom ≫ f ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv)) ≫ _ = _
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc,
    MonoidalCategory.whiskerLeft_inv_hom_assoc]


private def zero_homology_iso (M : Modules R) (i : ℤ) :
    (periodicTensorZeroComplex R M).homology i ≅
      (periodicTensorZeroComplex R M).X i :=
  (ShortComplex.LeftHomologyData.ofZeros
    ((periodicTensorZeroComplex R M).sc i) rfl rfl).homologyIso

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Tensoring the prescribed periodic scalar complex with a module killed by the scalar
has its canonical zero-differential normal form. The formulas specify both directions
using the degree-zero total-tensor projection and the unit tensor isomorphism; locally
these are a tensor m mapped to a*m, and m mapped to 1 tensor m. Naturality is a chain-map
identity. No exactness of scalar multiplication on R and no nonvanishing are assumed.

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-def-localizing-closure-ctf-equals-bc.proof.md, "The examples"; Stacks 03EK and 06YU
(blueprint: lem-sfb-periodic-tensor-normal-form).

Proof (the node's seven steps):
1. The existing exactScalarPeriodicComplex uses scalar multiplication in negative
   degrees. Its square is zero by t squared = 0; the cutoff handles the other degrees.
2. The sectionwise balanced maps a tensor m to a*m and m to 1 tensor m are inverse
   and commute with restrictions. Sheafification (def-weil-presheaf-modules-sheafification)
   gives the unit tensor iso of def-pur-sheaf-tensor-product, including tensor with zero.
3. In total degree n all summands except (n,0) vanish. The coproduct projection and
   injection give mapBifunctorSingle₂Iso, followed in nonpositive degrees by the unit iso.
4. The second signed differential is zero. The first becomes t*a*m = a*(t*m) = 0.
   At degree zero its target vanishes; above zero its source vanishes. The graded
   inverse maps therefore commute with differentials and are inverse chain maps.
5. Linearity gives a*f(m) = f(a*m) and f(1 tensor m) = 1 tensor f(m).
   Sheafification uniqueness proves naturality; positive-degree squares are zero.
6. Kernels in the zero-differential complex are whole terms, and images are zero.
   Transport cohomology along the iso: every H^(-q) is M, including q=0, and positive
   cohomology vanishes. The same computation on the one-point site is ordinary tensor.
7. Given a K-flat resolution epsilon, lem-sf-ringed-kflat-single-tensor-comparison
   identifies the derived tensor with the localized termwise tensor. Its degree-zero
   comparison and the iso above identify this with Q(Z_M). Invert Q(epsilon) in the
   first factor. This uses the specified resolution without boundedness or flatness of M.
-/
theorem periodic_tensor_normal_form
    (t : (unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)).sections)
    (ht : ∀ U : Cᵒᵖ, (@id (R.obj.obj U) (t.val U)) * (@id (R.obj.obj U) (t.val U)) = 0)
    [HasDerivedCategory.{w} (Modules R)] :
    ∃ phi : ∀ (M : Modules R)
        (_ : ∀ (U : Cᵒᵖ) (m : M.val.obj U), (@id (R.obj.obj U) (t.val U)) • m = 0),
      CochainComplex.mapBifunctor (exactScalarPeriodicComplex R t ht)
          ((HomologicalComplex.single _ (.up ℤ) 0).obj M) (ordinaryTensor R) ≅
        periodicTensorZeroComplex R M,
      (∀ (M : Modules R)
          (hM : ∀ (U : Cᵒᵖ) (m : M.val.obj U), (@id (R.obj.obj U) (t.val U)) • m = 0)
          (i : ℤ) (hi : i ≤ 0),
        (phi M hM).hom.f i ≫ (periodicTensorZeroXIso R M i hi).hom =
          (CochainComplex.mapBifunctorSingle₂Iso (ordinaryTensor R) M
            (exactScalarPeriodicComplex R t ht)).hom.f i ≫
          ((ordinaryTensor R).map (CochainComplex.scalarPeriodicXIso
            (exactScalarMultiplication R t) (exactScalarMultiplication_sq R t ht) i hi).hom
            ).app M ≫ (λ_ M).hom) ∧
      (∀ (M : Modules R)
          (hM : ∀ (U : Cᵒᵖ) (m : M.val.obj U), (@id (R.obj.obj U) (t.val U)) • m = 0)
          (i : ℤ) (hi : i ≤ 0),
        (phi M hM).inv.f i = (periodicTensorZeroXIso R M i hi).hom ≫ (λ_ M).inv ≫
          ((ordinaryTensor R).map (CochainComplex.scalarPeriodicXIso
            (exactScalarMultiplication R t) (exactScalarMultiplication_sq R t ht) i hi).inv
            ).app M ≫
          (CochainComplex.mapBifunctorSingle₂Iso (ordinaryTensor R) M
            (exactScalarPeriodicComplex R t ht)).inv.f i) ∧
      (∀ (M N : Modules R)
          (hM : ∀ (U : Cᵒᵖ) (m : M.val.obj U), (@id (R.obj.obj U) (t.val U)) • m = 0)
          (hN : ∀ (U : Cᵒᵖ) (n : N.val.obj U), (@id (R.obj.obj U) (t.val U)) • n = 0)
          (f : M ⟶ N),
        ((totalTensor R).obj (exactScalarPeriodicComplex R t ht)).map
            ((HomologicalComplex.single _ (.up ℤ) 0).map f) ≫ (phi N hN).hom =
          (phi M hM).hom ≫ periodicTensorZeroMap R f) ∧
      (∀ (M : Modules R)
          (hM : ∀ (U : Cᵒᵖ) (m : M.val.obj U), (@id (R.obj.obj U) (t.val U)) • m = 0),
        (∀ q : ℕ, Nonempty ((CochainComplex.mapBifunctor (exactScalarPeriodicComplex R t ht)
          ((HomologicalComplex.single _ (.up ℤ) 0).obj M) (ordinaryTensor R)).homology
            (-(q : ℤ)) ≅ M)) ∧
        (∀ i : ℤ, 0 < i → IsZero ((CochainComplex.mapBifunctor
          (exactScalarPeriodicComplex R t ht)
          ((HomologicalComplex.single _ (.up ℤ) 0).obj M) (ordinaryTensor R)).homology i)) ∧
        (∀ (E : Modules R)
            (epsilon : exactScalarPeriodicComplex R t ht ⟶
              (HomologicalComplex.single _ (.up ℤ) 0).obj E)
            (hepsilon : CochainComplex.IsKFlatResolutionIndependentCoefficients epsilon),
          ∃ e : ((derivedTensor R).obj
            (DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj E))).obj
              (DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj M)) ≅
            DerivedCategory.Q.obj (periodicTensorZeroComplex R M),
            ((derivedTensor R).map (DerivedCategory.Q.map epsilon)).app _ ≫ e.hom =
              ((ringed_kFlat_single_tensor_comparison R).choose
                (exactScalarPeriodicComplex R t ht) hepsilon.2 M).hom ≫
              DerivedCategory.Q.map
                ((CochainComplex.mapBifunctorSingle₂Iso (ordinaryTensor R) M
                  (exactScalarPeriodicComplex R t ht)).inv ≫ (phi M hM).hom))) := by
  let P := exactScalarPeriodicComplex R t ht
  let delta (M : Modules R) := CochainComplex.mapBifunctorSingle₂Iso (ordinaryTensor R) M P
  let e (M : Modules R) (hM) := periodic_tensor_termwise_iso R t ht M hM
  let phi (M : Modules R) (hM) := delta M ≪≫ e M hM
  refine ⟨phi, ?_, ?_, ?_, ?_⟩
  · intro M hM i hi
    simp [phi, e, periodic_tensor_termwise_iso, periodic_tensor_term_iso, hi,
      Category.assoc]
    rfl
  · intro M hM i hi
    simp [phi, e, periodic_tensor_termwise_iso, periodic_tensor_term_iso, hi,
      Category.assoc]
    rfl
  · intro M N hM hN f
    apply HomologicalComplex.hom_ext
    intro i
    apply (cancel_epi ((delta M).inv.f i)).mp
    simp only [HomologicalComplex.comp_f, phi, Iso.trans_hom, Category.assoc]
    rw [single_tensor_second_naturality_assoc R f P i]
    have hc := congrArg (fun g ↦ HomologicalComplex.Hom.f g i) (delta M).inv_hom_id
    have hcN := congrArg (fun g ↦ HomologicalComplex.Hom.f g i) (delta N).inv_hom_id
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hc hcN
    change (P.X i ◁ f) ≫ (delta N).inv.f i ≫ (delta N).hom.f i ≫ (e N hN).hom.f i =
      (delta M).inv.f i ≫ (delta M).hom.f i ≫
        (e M hM).hom.f i ≫ (periodicTensorZeroMap R f).f i
    simp only [reassoc_of% hc, reassoc_of% hcN]
    by_cases hi : i ≤ 0
    · let s : P.X i ≅ 𝟙_ (Modules R) := CochainComplex.scalarPeriodicXIso
        (exactScalarMultiplication R t) (exactScalarMultiplication_sq R t ht) i hi
      let zM := periodicTensorZeroXIso R M i hi
      let zN := periodicTensorZeroXIso R N i hi
      simp only [e, periodic_tensor_termwise_iso,
        HomologicalComplex.Hom.isoOfComponents_hom_f, periodic_tensor_term_iso, dif_pos hi,
        Iso.trans_hom, Iso.symm_hom, periodicTensorZeroMap]
      change (P.X i ◁ f) ≫ s.hom ▷ N ≫ (λ_ N).hom ≫ zN.inv =
        s.hom ▷ M ≫ (λ_ M).hom ≫ zM.inv ≫ zM.hom ≫ f ≫ zN.inv
      have hs : (P.X i ◁ f) ≫ s.hom ▷ N =
          s.hom ▷ M ≫ (𝟙_ (Modules R)) ◁ f := whisker_exchange s.hom f
      rw [reassoc_of% hs, Iso.inv_hom_id_assoc]
      rw [leftUnitor_naturality_assoc]
    · apply IsZero.eq_of_tgt
      exact IsZero.of_iso (isZero_zero _) (eqToIso (if_neg hi))
  · intro M hM
    have hH (i : ℤ) :
        (CochainComplex.mapBifunctor P
          ((HomologicalComplex.single _ (.up ℤ) 0).obj M) (ordinaryTensor R)).homology i ≅
            (periodicTensorZeroComplex R M).X i :=
      (HomologicalComplex.homologyFunctor _ (.up ℤ) i).mapIso (phi M hM) ≪≫
        zero_homology_iso R M i
    refine ⟨?_, ?_, ?_⟩
    · intro q
      exact ⟨hH (-(q : ℤ)) ≪≫ periodicTensorZeroXIso R M _ (by omega)⟩
    · intro i hi
      exact IsZero.of_iso (IsZero.of_iso (isZero_zero _) (eqToIso (if_neg (by omega))))
        (hH i)
    · intro E epsilon hepsilon
      have := hepsilon.1
      let a := ((derivedTensor R).flip.obj
        (DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj M))).mapIso
          (asIso (DerivedCategory.Q.map epsilon))
      let c := (ringed_kFlat_single_tensor_comparison R).choose P hepsilon.2 M
      let b := DerivedCategory.Q.mapIso ((delta M).symm ≪≫ phi M hM)
      refine ⟨a.symm ≪≫ c ≪≫ b, ?_⟩
      change a.hom ≫ (a.inv ≫ c.hom ≫ b.hom) = _
      simp only [Iso.hom_inv_id_assoc]
      rfl

end SheafOfModules
