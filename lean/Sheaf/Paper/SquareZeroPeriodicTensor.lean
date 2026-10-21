/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.SixFunctors.IntrinsicDerivedTensorOfUniverses
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

import Mathlib.CategoryTheory.Abelian.Projective.Extend
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat

import Sheaf.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients

/-! # The periodic resolution for an exact square-zero divisor

Source: Weil conjectures blueprint, main-20261015, sec-proetale-coefficients,
sk-def-localizing-closure-ctf-equals-bc.proof.md, "The examples", periodic resolution;
Stacks Project, Tags 064K, 06YQ, 093J and 03CY.
(blueprint: lem-sfb-square-zero-periodic-tensor).

## Main statements

* `ModuleCat.square_zero_periodic_resolution_tensor`: the rank-one free resolution and self-Tor.
* `AlgebraicGeometry.Scheme.square_zero_periodic_tensor`: the constant-sheaf calculation.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe r u w uC vC c v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped TensorProduct

namespace ModuleCat

variable (R : Type r) [CommRing R] (t : R)

private def periodicDifferential : ModuleCat.of R R ⟶ ModuleCat.of R R :=
  ModuleCat.ofHom (LinearMap.mulLeft R t)

private theorem periodicDifferential_sq (ht : t ^ 2 = 0) :
    periodicDifferential R t ≫ periodicDifferential R t = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change t * (t * x) = 0
  rw [← mul_assoc, ← pow_two, ht, zero_mul]

private def periodicComplex (ht : t ^ 2 = 0) : ChainComplex (ModuleCat.{r} R) ℕ :=
  ChainComplex.of (fun _ ↦ ModuleCat.of R R) (fun _ ↦ periodicDifferential R t)
    (fun _ ↦ periodicDifferential_sq R t ht)

private theorem periodicComplex_d_succ (ht : t ^ 2 = 0) (n : ℕ) :
    (periodicComplex R t ht).d (n + 1) n = periodicDifferential R t := by
  exact ChainComplex.of_d (fun _ : ℕ ↦ ModuleCat.of R R)
    (fun _ ↦ periodicDifferential R t) n

private theorem periodicComplex_d_ne (ht : t ^ 2 = 0) (i j : ℕ)
    (h : i ≠ j + 1) : (periodicComplex R t ht).d i j = 0 := by
  exact ChainComplex.of_d_ne (fun _ : ℕ ↦ ModuleCat.of R R)
    (fun _ ↦ periodicDifferential R t) h

private theorem periodicComplex_exactAt_succ (ht : t ^ 2 = 0)
    (hann : ∀ a : R, t * a = 0 ↔ a ∈ Ideal.span ({t} : Set R)) (n : ℕ) :
    (periodicComplex R t ht).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  rw [CategoryTheory.ShortComplex.moduleCat_exact_iff]
  change ∀ x : R, (periodicComplex R t ht).d (n + 1) n x = 0 →
    ∃ a : R, (periodicComplex R t ht).d (n + 2) (n + 1) a = x
  rw [periodicComplex_d_succ, periodicComplex_d_succ]
  change ∀ x : R, t * x = 0 → ∃ a : R, t * a = x
  intro x hx
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp ((hann x).mp hx)
  exact ⟨a, by simpa [mul_comm] using ha⟩

private def periodicAugmentation (ht : t ^ 2 = 0) :
    periodicComplex R t ht ⟶
      (ChainComplex.single₀ (ModuleCat.{r} R)).obj
        (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R))) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨ModuleCat.ofHom (Ideal.span ({t} : Set R)).mkQ, by
      change periodicDifferential R t ≫
        ModuleCat.ofHom (Ideal.span ({t} : Set R)).mkQ = 0
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change Ideal.Quotient.mk (Ideal.span ({t} : Set R)) (t * x) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton.mpr ⟨x, rfl⟩)⟩

private theorem periodicAugmentation_epi (ht : t ^ 2 = 0) :
    Epi ((periodicAugmentation R t ht).f 0) := by
  rw [ModuleCat.epi_iff_surjective]
  change Function.Surjective (Ideal.span ({t} : Set R)).mkQ
  exact Submodule.mkQ_surjective _

private theorem periodicAugmentation_exact (ht : t ^ 2 = 0) :
    (ShortComplex.mk ((periodicComplex R t ht).d 1 0)
      ((periodicAugmentation R t ht).f 0) (by
        rw [← HomologicalComplex.Hom.comm, HomologicalComplex.single_obj_d, comp_zero])).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  change ∀ x : R, Ideal.Quotient.mk (Ideal.span ({t} : Set R)) x = 0 →
    ∃ a : R, (periodicComplex R t ht).d 1 0 a = x
  rw [periodicComplex_d_succ]
  change ∀ x : R, Ideal.Quotient.mk (Ideal.span ({t} : Set R)) x = 0 →
    ∃ a : R, t * a = x
  intro x hx
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp
    (Ideal.Quotient.eq_zero_iff_mem.mp hx)
  exact ⟨a, by simpa [mul_comm] using ha⟩

private def periodicResolution (ht : t ^ 2 = 0)
    (hann : ∀ a : R, t * a = 0 ↔ a ∈ Ideal.span ({t} : Set R)) :
    ProjectiveResolution (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R))) where
  complex := periodicComplex R t ht
  projective _ := by
    change Projective (ModuleCat.of R R)
    infer_instance
  π := periodicAugmentation R t ht
  quasiIso := ⟨fun n ↦ by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2
          ⟨periodicAugmentation_exact R t ht, periodicAugmentation_epi R t ht⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by simp [periodicComplex]) (by simp)
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact periodicComplex_exactAt_succ R t ht hann n
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

private def zeroDifferentialHomologyIso
    (K : ChainComplex (ModuleCat.{r} R) ℕ) (hd : ∀ i j, K.d i j = 0) (n : ℕ) :
    K.homology n ≅ K.X n :=
  (K.isoHomologyπ _ n rfl (hd _ _)).symm ≪≫ K.iCyclesIso n _ rfl (hd _ _)

private theorem quotient_smul_zero (x : R ⧸ Ideal.span ({t} : Set R)) :
    t • x = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk (Ideal.span ({t} : Set R)) (t * a) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton.mpr ⟨a, rfl⟩)

private theorem tensor_periodicDifferential_zero :
    (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R))) ◁ periodicDifferential R t = 0 := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  change x ⊗ₜ[R] (t • y) = 0
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', quotient_smul_zero,
    TensorProduct.zero_tmul]

private theorem tensor_periodicComplex_d_zero (ht : t ^ 2 = 0) (i j : ℕ) :
    (((tensorLeft (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R)))).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (periodicComplex R t ht)).d i j = 0 := by
  change (tensorLeft _).map ((periodicComplex R t ht).d i j) = 0
  by_cases h : i = j + 1
  · subst i
    rw [periodicComplex_d_succ]
    exact tensor_periodicDifferential_zero R t
  · rw [periodicComplex_d_ne R t ht i j h, Functor.map_zero]

private def periodicTorIso (ht : t ^ 2 = 0)
    (hann : ∀ a : R, t * a = 0 ↔ a ∈ Ideal.span ({t} : Set R)) (n : ℕ) :
    (((Tor (ModuleCat.{r} R) n).obj
      (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R)))).obj
      (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R)))) ≅
        ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R)) :=
  (periodicResolution R t ht hann).isoLeftDerivedObj (tensorLeft _) n ≪≫
    zeroDifferentialHomologyIso R _ (tensor_periodicComplex_d_zero R t ht) n ≪≫ ρ_ _

private theorem periodicDifferential_tensor_zero :
    periodicDifferential R t ▷ (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R))) = 0 := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  change (t • x) ⊗ₜ[R] y = 0
  rw [TensorProduct.smul_tmul, quotient_smul_zero, TensorProduct.tmul_zero]

private theorem periodicComplex_tensor_d_zero (ht : t ^ 2 = 0) (i j : ℕ) :
    (tensorRight (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R)))).map
      ((periodicComplex R t ht).d i j) = 0 := by
  by_cases h : i = j + 1
  · subst i
    rw [periodicComplex_d_succ]
    exact periodicDifferential_tensor_zero R t
  · rw [periodicComplex_d_ne R t ht i j h, Functor.map_zero]

private theorem periodicCochain_tensor_d_zero (ht : t ^ 2 = 0)
    (hann : ∀ a : R, t * a = 0 ↔ a ∈ Ideal.span ({t} : Set R)) (i j : ℤ) :
    (tensorRight (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R)))).map
      ((periodicResolution R t ht hann).cochainComplex.d i j) = 0 := by
  let P := periodicResolution R t ht hann
  let F := tensorRight (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R)))
  by_cases hi : i ≤ 0
  · by_cases hj : j ≤ 0
    · obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat hi
      obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat hj
      have hm : F.map (P.complex.d m n) = 0 :=
        periodicComplex_tensor_d_zero R t ht m n
      rw [P.cochainComplex_d (-m) (-n) m n rfl rfl,
        Functor.map_comp, Functor.map_comp, hm]
      simp only [zero_comp, comp_zero]
    · have hz := F.map_isZero (P.cochainComplex.isZero_of_isStrictlyLE 0 j (by omega))
      exact hz.eq_of_tgt _ _
  · have hz := F.map_isZero (P.cochainComplex.isZero_of_isStrictlyLE 0 i (by omega))
    exact hz.eq_of_src _ _

private def zeroCochainDifferentialHomologyIso
    (K : CochainComplex (ModuleCat.{r} R) ℤ) (hd : ∀ i j, K.d i j = 0) (n : ℤ) :
    K.homology n ≅ K.X n :=
  (K.isoHomologyπ _ n rfl (hd _ _)).symm ≪≫ K.iCyclesIso n _ rfl (hd _ _)

private def periodicDerivedTensorIso [HasDerivedCategory.{w} (ModuleCat.{r} R)]
    (ht : t ^ 2 = 0)
    (hann : ∀ a : R, t * a = 0 ↔ a ∈ Ideal.span ({t} : Set R)) (q : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{r} R) (-(q : ℤ))).obj
      (((DerivedCategory.singleFunctor (ModuleCat.{r} R) 0).obj
        (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R)))) ⊗
       ((DerivedCategory.singleFunctor (ModuleCat.{r} R) 0).obj
        (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R))))) ≅
          ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R)) := by
  let P := periodicResolution R t ht hann
  let F := ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R))
  let Q := DerivedCategory.Q (C := ModuleCat.{r} R)
  have : HasExactColimitsOfShape ℤ (ModuleCat.{r} R) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{r} R)
      (AsSmall.equiv (C := ℤ)).symm
  have hP : (HomologicalComplex.quasiIso (ModuleCat.{r} R) (.up ℤ)).kFlat
      P.cochainComplex :=
    CochainComplex.kFlat_of_isStrictlyLE_of_flat P.cochainComplex 0
      (fun i ↦ (ModuleCat.flat_iff_flat _).2 inferInstance)
  let e : Q.obj P.cochainComplex ≅ (DerivedCategory.singleFunctor _ 0).obj F :=
    asIso (Q.map P.π') ≪≫ (DerivedCategory.singleFunctorIsoCompQ _ 0).symm.app F
  let K := ((tensorRight F).mapHomologicalComplex (.up ℤ)).obj P.cochainComplex
  let et : (DerivedCategory.singleFunctor _ 0).obj F ⊗
      (DerivedCategory.singleFunctor _ 0).obj F ≅ Q.obj K :=
    tensorIso e.symm (Iso.refl _) ≪≫
      DerivedCategory.QObjTensorSingleFunctorObjIso P.cochainComplex hP F
  exact (DerivedCategory.homologyFunctor _ (-(q : ℤ))).mapIso et ≪≫
    (DerivedCategory.homologyFunctorFactors _ (-(q : ℤ))).app K ≪≫
    zeroCochainDifferentialHomologyIso R K (periodicCochain_tensor_d_zero R t ht hann)
      (-(q : ℤ)) ≪≫
    (tensorRight F).mapIso (P.cochainComplexXIso (-(q : ℤ)) q rfl) ≪≫ λ_ F

/-- The multiplication-by-`t` resolution and its self-tensor calculation.
Source: blueprint main-20261015, sec-proetale-coefficients,
sk-def-localizing-closure-ctf-equals-bc.proof.md, "The examples"; Stacks Tag 064K.
(blueprint: lem-sfb-square-zero-periodic-tensor).

Proof:
1. Put R in every nonnegative chain degree, with differential multiplication by t,
   and augment by R → R/(t). The square-zero equation makes a complex. The annihilator
   hypothesis says each kernel equals the incoming image tR. The quotient augmentation
   is surjective with kernel tR, so this is a free resolution of rank one in every degree.
2. Reindex by i = -q. This is bounded above and termwise flat, hence K-flat by
   lem-pc-module-bounded-flat-kflat, using def-pc-kflat-complex on the one-point site.
   The computation and independence in lem-pc-derived-tensor-second-factor-functor
   identify its total tensor with F[0] with the derived self-tensor.
3. Each nonpositive term after tensoring is F and multiplication by t is zero.
   There is only one summand in each total degree. Thus cohomology in degree -q is F,
   including q = 0. The chain-indexed calculation is exactly Tor_q(F,F). -/
theorem square_zero_periodic_resolution_tensor (R : Type r) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{r} R)]
    (t : R) (ht : t ^ 2 = 0)
    (hann : ∀ a : R, t * a = 0 ↔ a ∈ Ideal.span ({t} : Set R)) :
    (∃ P : ProjectiveResolution (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R))),
      ∃ e : ∀ n : ℕ, P.complex.X n ≅ ModuleCat.of R R,
        (∀ (n : ℕ) (x : P.complex.X (n + 1)),
          (e n).hom (P.complex.d (n + 1) n x) = t * (e (n + 1)).hom x) ∧
        (∀ x : P.complex.X 0,
          P.π.f 0 x = Ideal.Quotient.mk (Ideal.span ({t} : Set R)) ((e 0).hom x))) ∧
    (∀ q : ℕ,
      Nonempty ((((Tor (ModuleCat.{r} R) q).obj
        (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R)))).obj
          (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R)))) ≅
            ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R)))) ∧
    (∀ q : ℕ,
      Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{r} R) (-(q : ℤ))).obj
        (((DerivedCategory.singleFunctor (ModuleCat.{r} R) 0).obj
          (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R)))) ⊗
         ((DerivedCategory.singleFunctor (ModuleCat.{r} R) 0).obj
          (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R))))) ≅
            ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R)))) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨periodicResolution R t ht hann, fun _ ↦ Iso.refl _, ?_, ?_⟩
    · intro n x
      change R at x
      change (periodicComplex R t ht).d (n + 1) n x = t * x
      rw [periodicComplex_d_succ]
      rfl
    · intro x
      rfl
  · intro q
    exact ⟨periodicTorIso R t ht hann q⟩
  · intro q
    exact ⟨periodicDerivedTensorIso R t ht hann q⟩

end ModuleCat

namespace CategoryTheory

variable {D : Type c} [Category.{v} D] [Abelian D] [HasDerivedCategory.{w} D]

private theorem periodicCommonRoof {P P' : CochainComplex D ℤ}
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj P') :
    ∃ (S : CochainComplex D ℤ) (a : S ⟶ P) (b : S ⟶ P'),
      QuasiIso a ∧ QuasiIso b := by
  obtain ⟨M, a, ha, b, he⟩ := DerivedCategory.right_fac e.hom
  have ha' : QuasiIso a := (DerivedCategory.isIso_Q_map_iff_quasiIso D a).1 ha
  have hb : IsIso (DerivedCategory.Q.map b) := by
    have h : DerivedCategory.Q.map b = DerivedCategory.Q.map a ≫ e.hom := by
      rw [he]
      simp
    rw [h]
    infer_instance
  have hb' : QuasiIso b := (DerivedCategory.isIso_Q_map_iff_quasiIso D b).1 hb
  exact ⟨M, a, b, ha', hb'⟩

private theorem periodicTensorModelsComparison
    (tensor : CochainComplex D ℤ → CochainComplex D ℤ → CochainComplex D ℤ)
    (flat : CochainComplex D ℤ → Prop)
    (swap : ∀ X Y, tensor X Y ≅ tensor Y X)
    (preserve : ∀ P, flat P → ∀ {X Y} (f : X ⟶ Y), QuasiIso f →
      (DerivedCategory.Q.obj (tensor X P) ≅ DerivedCategory.Q.obj (tensor Y P)))
    (resolve : ∀ M, ∃ (T : CochainComplex D ℤ) (f : T ⟶ M), flat T ∧ QuasiIso f)
    (P P' L L' : CochainComplex D ℤ) (hP : flat P) (hP' : flat P')
    (eP : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj P')
    (eL : DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj L') :
    Nonempty (DerivedCategory.Q.obj (tensor P L) ≅
      DerivedCategory.Q.obj (tensor P' L')) := by
  obtain ⟨S, a, b, ha, hb⟩ := periodicCommonRoof eP
  obtain ⟨M, c₀, d₀, hc₀, hd₀⟩ := periodicCommonRoof eL
  obtain ⟨T, r, hT, hr⟩ := resolve M
  let c : T ⟶ L := r ≫ c₀
  let d : T ⟶ L' := r ≫ d₀
  have hc : QuasiIso c := inferInstance
  have hd : QuasiIso d := inferInstance
  let Q := DerivedCategory.Q (C := D)
  exact ⟨Q.mapIso (swap P L) ≪≫ (preserve P hP c hc).symm ≪≫
    Q.mapIso (swap T P) ≪≫ (preserve T hT a ha).symm ≪≫
    preserve T hT b hb ≪≫ Q.mapIso (swap P' T) ≪≫
    preserve P' hP' d hd ≪≫ Q.mapIso (swap L' P')⟩

end CategoryTheory

namespace SheafOfModules

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

set_option hygiene false in
local notation "𝒜" => SheafOfModules.{r}
  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)

private local instance intrinsicWeakSheafify : HasWeakSheafify J AddCommGrpCat.{r} :=
  HasSheafify.isRightAdjoint

private local instance intrinsicAbelian : Abelian 𝒜 := inferInstance

private local instance intrinsicCoproducts : HasCoproducts.{0} 𝒜 := inferInstance

private local instance intrinsicMonoidal : MonoidalCategory 𝒜 :=
  SheafOfModules.cochainModulesMonoidal R

private local instance intrinsicSymmetric : SymmetricCategory 𝒜 :=
  SheafOfModules.cochainModulesSymmetric R

private local instance intrinsicPreadditive : MonoidalPreadditive 𝒜 :=
  SheafOfModules.cochainModulesPreadditive R

variable [HasDerivedCategory.{w} 𝒜]

@[irreducible]
private def periodicTotalTensor (P L : CochainComplex 𝒜 ℤ) : CochainComplex 𝒜 ℤ :=
  CochainComplex.mapBifunctor P L (curriedTensor 𝒜)

private def totalSwap (P L : CochainComplex 𝒜 ℤ) :
    periodicTotalTensor R P L ≅
      periodicTotalTensor R L P := by
  unfold periodicTotalTensor
  exact CochainComplex.Monoidal.braiding P L

private def tensorMapIsoRight (P : CochainComplex 𝒜 ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients P)
    {X Y : CochainComplex 𝒜 ℤ} (f : X ⟶ Y) (hf : QuasiIso f) :
    DerivedCategory.Q.obj (periodicTotalTensor R X P) ≅
      DerivedCategory.Q.obj (periodicTotalTensor R Y P) := by
  unfold periodicTotalTensor
  have := CategoryTheory.kFlatTensorPreservesQuasiIsoIndependentCoefficients R P hP f hf
  exact asIso (DerivedCategory.Q.map ((CategoryTheory.koszulTensorFunctor R P).map f))

private theorem tensorModelsIso
    (P P' L L' : CochainComplex 𝒜 ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients P)
    (hP' : CochainComplex.IsKFlatIndependentCoefficients P')
    (eP : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj P')
    (eL : DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj L') :
    Nonempty (DerivedCategory.Q.obj (periodicTotalTensor R P L) ≅
      DerivedCategory.Q.obj (periodicTotalTensor R P' L')) := by
  apply CategoryTheory.periodicTensorModelsComparison
    (fun X Y ↦ periodicTotalTensor R X Y)
    CochainComplex.IsKFlatIndependentCoefficients (totalSwap R)
    (fun P hP _ _ f hf ↦ tensorMapIsoRight R P hP f hf) ?_ P P' L L' hP hP' eP eL
  intro M
  obtain ⟨T, f, hT, _, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) M
  exact ⟨T, f, hT, hf⟩

private theorem intrinsicTensorModel
    (K L : DerivedCategory 𝒜) (P L₁ : CochainComplex 𝒜 ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients P)
    (eP : DerivedCategory.Q.obj P ≅ K) (eL : DerivedCategory.Q.obj L₁ ≅ L) :
    Nonempty (ringedSiteDerivedTensorOfUniverses R K L ≅
      DerivedCategory.Q.obj (CochainComplex.mapBifunctor P L₁ (curriedTensor 𝒜))) := by
  let Q := DerivedCategory.Q (C := 𝒜)
  let K₀ := Q.objPreimage K
  let L₀ := Q.objPreimage L
  let h := CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) K₀
  let P₀ := h.choose
  let f : P₀ ⟶ K₀ := h.choose_spec.choose
  have hP₀ : CochainComplex.IsKFlatIndependentCoefficients P₀ :=
    h.choose_spec.choose_spec.1
  have hf : QuasiIso f := h.choose_spec.choose_spec.2.2.1
  let ep : Q.obj P₀ ≅ Q.obj P :=
    asIso (Q.map f) ≪≫ Q.objObjPreimageIso K ≪≫ eP.symm
  let el : Q.obj L₀ ≅ Q.obj L₁ := Q.objObjPreimageIso L ≪≫ eL.symm
  have e := tensorModelsIso R P₀ P L₀ L₁ hP₀ hP ep el
  unfold periodicTotalTensor at e
  exact e

omit [HasDerivedCategory.{w} 𝒜] in
private theorem periodicTensorZero (M N : 𝒜) (f : M ⟶ M)
    (hraw : f.val ▷ N.val = 0) : f ▷ N = 0 := by
  let O : Sheaf J RingCat.{r} :=
    (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R
  let S : PresheafOfModules.{r} O.obj ⥤ 𝒜 :=
    PresheafOfModules.sheafification.{r} (R := O) (𝟙 O.obj)
  have : S.Additive := by
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts S
    exact Functor.additive_of_preservesBinaryBiproducts S
  let e := tensorRightPresentation R N
  have h : f ▷ N ≫ e.hom.app M = e.hom.app M ≫ S.map (f.val ▷ N.val) :=
    e.hom.naturality f
  apply (cancel_mono (e.hom.app M)).1
  rw [h, hraw, S.map_zero, comp_zero, zero_comp]

end SheafOfModules

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private noncomputable def basisConst {C : Type uC} [Category.{vC} C]
    (A : CommRingCat.{r}) : ModuleCat.{r} A ⥤
      PresheafOfModules.{r} ((Functor.const Cᵒᵖ).obj (RingCat.of A)) where
  obj M :=
    { obj := fun _ ↦ M
      map := fun _ ↦ ModuleCat.ofHom LinearMap.id
      map_id := fun _ ↦ by ext; rfl
      map_comp := fun _ _ ↦ by ext; rfl }
  map f := { app := fun _ ↦ f }

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
  (J : GrothendieckTopology C)
  [HasSheafify J CommRingCat.{r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  (A B : CommRingCat.{r}) [Algebra A B]
private local instance basisWeakCommRing : HasWeakSheafify J CommRingCat.{r} :=
  HasSheafify.isRightAdjoint

private local instance basisWeakAddCommGrp : HasWeakSheafify J AddCommGrpCat.{r} :=
  HasSheafify.isRightAdjoint

private local instance basisRingLocallyBijective :
    J.WEqualsLocallyBijective CommRingCat.{r} := by
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{vC, r,
    uC, (r) + 1, r, r, r} _
private noncomputable abbrev basisRing (A : CommRingCat.{r}) :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj
    ((constantSheaf J CommRingCat.{r}).obj A)
private noncomputable def basisRingUnit (A : CommRingCat.{r}) :
    (Functor.const Cᵒᵖ).obj (RingCat.of A) ⟶ (basisRing.{r, uC, vC} J A).obj :=
  Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj A)) (forget₂ CommRingCat RingCat)
private local instance basisRingUnit_li :
    Presheaf.IsLocallyInjective J (basisRingUnit.{r, uC, vC} J A) := by
  let := basisRingLocallyBijective.{r, uC, vC} J
  exact ⟨fun x y h ↦ Presheaf.equalizerSieve_mem J
    (toSheafify J ((Functor.const Cᵒᵖ).obj (show CommRingCat.{r} from A))) x y h⟩
private local instance basisRingUnit_ls :
    Presheaf.IsLocallySurjective J (basisRingUnit.{r, uC, vC} J A) := by
  let := basisRingLocallyBijective.{r, uC, vC} J
  exact ⟨fun x ↦ Presheaf.imageSieve_mem J
    (toSheafify J ((Functor.const Cᵒᵖ).obj (show CommRingCat.{r} from A))) x⟩
private noncomputable def basisTarget : SheafOfModules.{r} (basisRing.{r, uC, vC} J A) :=
  (SheafOfModules.restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map
    ((constantSheaf J CommRingCat.{r}).map (CommRingCat.ofHom (algebraMap A B))))).obj
      (SheafOfModules.unit (basisRing.{r, uC, vC} J B))
private noncomputable def basisConstToTarget :
    (basisConst A).obj (ModuleCat.of A B) ⟶
      (PresheafOfModules.restrictScalars (basisRingUnit.{r, uC, vC} J A)).obj
        (basisTarget.{r, uC, vC} J A B).val where
  app U := ModuleCat.ofHom (Y :=
    ((PresheafOfModules.restrictScalars (basisRingUnit.{r, uC, vC} J A)).obj
      (basisTarget.{r, uC, vC} J A B).val).obj U)
    { toFun := (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app U
      map_add' := map_add _
      map_smul' := fun a b ↦ by
        rw [Algebra.smul_def]
        change (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app U
          (algebraMap A B a * b) = _
        rw [map_mul]
        congr 1
        exact congrArg (fun t ↦ t a) (NatTrans.congr_app
          (toSheafify_naturality J
            ((Functor.const Cᵒᵖ).map (CommRingCat.ofHom (algebraMap A B)))) U) }
  naturality {U V} f := by
    ext b
    exact ConcreteCategory.congr_hom
      ((toSheafify J ((Functor.const Cᵒᵖ).obj B)).naturality f) b

@[irreducible]
private noncomputable def basisLift :
    (PresheafOfModules.sheafification (basisRingUnit.{r, uC, vC} J A)).obj
      ((basisConst A).obj (ModuleCat.of A B)) ⟶ basisTarget.{r, uC, vC} J A B :=
  (PresheafOfModules.sheafificationHomEquiv _).symm (basisConstToTarget.{r, uC, vC} J A B)

private instance basisLift_iso : IsIso (basisLift.{r, uC, vC} J A B) := by
  apply (isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _)).mp
  apply (Sheaf.isLocallyBijective_iff_isIso _).mp
  rw [← Sheaf.isLocallyInjective_sheafToPresheaf_map_iff,
    ← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
  let P := ((basisConst (C := C) A).obj (ModuleCat.of A B)).presheaf
  have h : toSheafify J P ≫
      ((SheafOfModules.toSheaf _).map (basisLift.{r, uC, vC} J A B)).hom =
        (PresheafOfModules.toPresheaf _).map
          (basisConstToTarget.{r, uC, vC} J A B) := by
    let E := PresheafOfModules.sheafificationHomEquiv
      (basisRingUnit.{r, uC, vC} J A)
      (P := (basisConst (C := C) A).obj (ModuleCat.of A B))
      (F := basisTarget.{r, uC, vC} J A B)
    have hh := E.apply_symm_apply (basisConstToTarget.{r, uC, vC} J A B)
    have hh' := congrArg (fun g ↦
      (PresheafOfModules.toPresheaf ((Functor.const Cᵒᵖ).obj (RingCat.of A))).map g) hh
    change toSheafify J P ≫ (PresheafOfModules.toPresheaf _).map
      (basisLift.{r, uC, vC} J A B).val = _
    rw [basisLift]
    exact hh'
  rw [← Presheaf.comp_isLocallyInjective_iff J (toSheafify J P),
    ← Presheaf.comp_isLocallySurjective_iff J (toSheafify J P)]
  change Presheaf.IsLocallyInjective J
    (toSheafify J P ≫ ((SheafOfModules.toSheaf _).map
      (basisLift.{r, uC, vC} J A B)).hom) ∧ _
  erw [h]
  let := basisRingLocallyBijective.{r, uC, vC} J
  constructor
  · exact ⟨fun x y h ↦ Presheaf.equalizerSieve_mem J
      (toSheafify J ((Functor.const Cᵒᵖ).obj B)) x y h⟩
  · exact ⟨fun x ↦ Presheaf.imageSieve_mem J
      (toSheafify J ((Functor.const Cᵒᵖ).obj B)) x⟩

private noncomputable def periodicConstantFunctor :
    ModuleCat.{r} A ⥤
      SheafOfModules.{r} (basisRing.{r, uC, vC} J A) :=
  basisConst A ⋙ PresheafOfModules.sheafification (basisRingUnit.{r, uC, vC} J A)

private theorem periodicConstantFunctor_exact :
    PreservesFiniteLimits (periodicConstantFunctor.{r, uC, vC} J A) ∧
      PreservesFiniteColimits (periodicConstantFunctor.{r, uC, vC} J A) := by
  constructor
  · let P := basisConst (C := C) A
    have : PreservesFiniteLimits P := by
      constructor
      intro K _ _
      constructor
      intro D
      apply preservesLimit_of_preserves_limit_cone (limit.isLimit D)
      apply PresheafOfModules.evaluationJointlyReflectsLimits
      intro X
      change IsLimit ((P ⋙ PresheafOfModules.evaluation _ X).mapCone (limit.cone D))
      have he : P ⋙ PresheafOfModules.evaluation _ X ≅
          𝟭 (ModuleCat.{r} A) := Iso.refl _
      let : PreservesLimitsOfShape K (P ⋙ PresheafOfModules.evaluation _ X) :=
        preservesLimitsOfShape_of_natIso he.symm
      exact isLimitOfPreserves _ (limit.isLimit D)
    exact comp_preservesFiniteLimits P _
  · let P := basisConst (C := C) A
    have : PreservesFiniteColimits P := by
      constructor
      intro K _ _
      constructor
      intro D
      apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit D)
      apply PresheafOfModules.evaluationJointlyReflectsColimits
      intro X
      change IsColimit ((P ⋙ PresheafOfModules.evaluation _ X).mapCocone (colimit.cocone D))
      have he : P ⋙ PresheafOfModules.evaluation _ X ≅
          𝟭 (ModuleCat.{r} A) := Iso.refl _
      let : PreservesColimitsOfShape K (P ⋙ PresheafOfModules.evaluation _ X) :=
        preservesColimitsOfShape_of_natIso he.symm
      exact isColimitOfPreserves _ (colimit.isColimit D)
    exact comp_preservesFiniteColimits P _

private noncomputable def periodicConstantAlgebraIso :
    (periodicConstantFunctor.{r, uC, vC} J A).obj (ModuleCat.of A B) ≅
      basisTarget.{r, uC, vC} J A B :=
  asIso (basisLift.{r, uC, vC} J A B)

private noncomputable def periodicUnitMultiply (a : A) :
    SheafOfModules.unit (basisRing.{r, uC, vC} J A) ⟶
      SheafOfModules.unit (basisRing.{r, uC, vC} J A) where
  val :=
    { app := fun U ↦ by
        letI : CommRing ((basisRing.{r, uC, vC} J A).obj.obj U) :=
          inferInstanceAs (CommRing
            (((constantSheaf J CommRingCat.{r}).obj A).obj.obj U))
        exact ModuleCat.ofHom (LinearMap.mulLeft _
          ((basisRingUnit.{r, uC, vC} J A).app U a))
      naturality := by
        intro U V f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change (basisRing.{r, uC, vC} J A).obj.obj U at x
        symm
        change (basisRing.{r, uC, vC} J A).obj.map f
          (((basisRingUnit.{r, uC, vC} J A).app U a) * x) =
            ((basisRingUnit.{r, uC, vC} J A).app V a) *
              (basisRing.{r, uC, vC} J A).obj.map f x
        rw [map_mul]
        congr 1
        exact (ConcreteCategory.congr_hom
          ((basisRingUnit.{r, uC, vC} J A).naturality f) a).symm }

private noncomputable def periodicUnitConstToTarget :
    (basisConst (C := C) A).obj (ModuleCat.of A A) ⟶
      (PresheafOfModules.restrictScalars (basisRingUnit.{r, uC, vC} J A)).obj
        (SheafOfModules.unit (basisRing.{r, uC, vC} J A)).val where
  app U := ModuleCat.ofHom (Y :=
    ((PresheafOfModules.restrictScalars (basisRingUnit.{r, uC, vC} J A)).obj
      (SheafOfModules.unit (basisRing.{r, uC, vC} J A)).val).obj U)
    { toFun := (basisRingUnit.{r, uC, vC} J A).app U
      map_add' := map_add _
      map_smul' := fun a b ↦ by
        change (basisRingUnit.{r, uC, vC} J A).app U (a * b) =
          (basisRingUnit.{r, uC, vC} J A).app U a *
            (basisRingUnit.{r, uC, vC} J A).app U b
        exact map_mul _ a b }
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact ConcreteCategory.congr_hom ((basisRingUnit.{r, uC, vC} J A).naturality f) a

@[irreducible]
private noncomputable def periodicUnitLift :
    (periodicConstantFunctor.{r, uC, vC} J A).obj (ModuleCat.of A A) ⟶
      SheafOfModules.unit (basisRing.{r, uC, vC} J A) :=
  (PresheafOfModules.sheafificationHomEquiv _).symm
    (periodicUnitConstToTarget.{r, uC, vC} J A)

private instance periodicUnitLift_iso :
    IsIso (periodicUnitLift.{r, uC, vC} J A) := by
  apply (isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _)).mp
  apply (Sheaf.isLocallyBijective_iff_isIso _).mp
  rw [← Sheaf.isLocallyInjective_sheafToPresheaf_map_iff,
    ← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
  let P := ((basisConst (C := C) A).obj (ModuleCat.of A A)).presheaf
  have h : toSheafify J P ≫
      ((SheafOfModules.toSheaf _).map (periodicUnitLift.{r, uC, vC} J A)).hom =
        (PresheafOfModules.toPresheaf _).map
          (periodicUnitConstToTarget.{r, uC, vC} J A) := by
    let E := PresheafOfModules.sheafificationHomEquiv
      (basisRingUnit.{r, uC, vC} J A)
      (P := (basisConst (C := C) A).obj (ModuleCat.of A A))
      (F := SheafOfModules.unit (basisRing.{r, uC, vC} J A))
    have hh := E.apply_symm_apply (periodicUnitConstToTarget.{r, uC, vC} J A)
    have hh' := congrArg (fun g ↦
      (PresheafOfModules.toPresheaf ((Functor.const Cᵒᵖ).obj (RingCat.of A))).map g) hh
    change toSheafify J P ≫ (PresheafOfModules.toPresheaf _).map
      (periodicUnitLift.{r, uC, vC} J A).val = _
    rw [periodicUnitLift]
    exact hh'
  rw [← Presheaf.comp_isLocallyInjective_iff J (toSheafify J P),
    ← Presheaf.comp_isLocallySurjective_iff J (toSheafify J P)]
  change Presheaf.IsLocallyInjective J
    (toSheafify J P ≫ ((SheafOfModules.toSheaf _).map
      (periodicUnitLift.{r, uC, vC} J A)).hom) ∧ _
  erw [h]
  let := basisRingLocallyBijective.{r, uC, vC} J
  constructor
  · exact ⟨fun x y h ↦ Presheaf.equalizerSieve_mem J
      (toSheafify J ((Functor.const Cᵒᵖ).obj A)) x y h⟩
  · exact ⟨fun x ↦ Presheaf.imageSieve_mem J
      (toSheafify J ((Functor.const Cᵒᵖ).obj A)) x⟩

private theorem periodicUnitLift_comm (a : A) :
    (periodicConstantFunctor.{r, uC, vC} J A).map
        (ModuleCat.ofHom (LinearMap.mulLeft A a)) ≫
      periodicUnitLift.{r, uC, vC} J A =
    periodicUnitLift.{r, uC, vC} J A ≫ periodicUnitMultiply.{r, uC, vC} J A a := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (basisRingUnit.{r, uC, vC} J A)
  apply (adj.homEquiv _ _).injective
  change adj.homEquiv _ _
    ((PresheafOfModules.sheafification (basisRingUnit.{r, uC, vC} J A)).map
      ((basisConst A).map (ModuleCat.ofHom (LinearMap.mulLeft A a))) ≫
      periodicUnitLift.{r, uC, vC} J A) =
    adj.homEquiv _ _
      (periodicUnitLift.{r, uC, vC} J A ≫ periodicUnitMultiply.{r, uC, vC} J A a)
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  have he : adj.homEquiv _ _ (periodicUnitLift.{r, uC, vC} J A) =
      periodicUnitConstToTarget.{r, uC, vC} J A := by
    dsimp only [adj]
    rw [PresheafOfModules.sheafificationAdjunction_homEquiv_apply, periodicUnitLift]
    exact Equiv.apply_symm_apply _ _
  rw [he]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change A at x
  change (basisRingUnit.{r, uC, vC} J A).app U (a * x) =
    (basisRingUnit.{r, uC, vC} J A).app U a *
      (basisRingUnit.{r, uC, vC} J A).app U x
  exact ((basisRingUnit.{r, uC, vC} J A).app U).hom.map_mul a x

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

open MonoidalCategory in
private theorem periodicUnitMultiply_tensor_zero (a : A)
    (ha : algebraMap A B a = 0) :
    periodicUnitMultiply.{r, uC, vC} J A a ▷ basisTarget.{r, uC, vC} J A B = 0 := by
  let R := (constantSheaf J CommRingCat.{r}).obj A
  let O := basisRing.{r, uC, vC} J A
  let M := SheafOfModules.unit O
  let N := basisTarget.{r, uC, vC} J A B
  let (U : Cᵒᵖ) : CommRing (O.obj.obj U) :=
    inferInstanceAs (CommRing (R.obj.obj U))
  let f := periodicUnitMultiply.{r, uC, vC} J A a
  have hraw : f.val ▷ N.val = 0 := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    change O.obj.obj U at x
    change (((basisRingUnit.{r, uC, vC} J A).app U a) * x) ⊗ₜ[O.obj.obj U] y = 0
    rw [← smul_eq_mul, TensorProduct.smul_tmul]
    have hz : ((basisRingUnit.{r, uC, vC} J A).app U a) • y = 0 := by
      change (basisRing.{r, uC, vC} J B).obj.obj U at y
      change (((sheafCompose J (forget₂ CommRingCat RingCat)).map
        ((constantSheaf J CommRingCat.{r}).map
          (CommRingCat.ofHom (algebraMap A B)))).hom.app U
            ((basisRingUnit.{r, uC, vC} J A).app U a)) *
              y = 0
      have h := ConcreteCategory.congr_hom (NatTrans.congr_app
        (toSheafify_naturality J
          ((Functor.const Cᵒᵖ).map (CommRingCat.ofHom (algebraMap A B)))) U) a
      change (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app U (algebraMap A B a) =
        (((sheafCompose J (forget₂ CommRingCat RingCat)).map
          ((constantSheaf J CommRingCat.{r}).map
            (CommRingCat.ofHom (algebraMap A B)))).hom.app U)
              ((basisRingUnit.{r, uC, vC} J A).app U a) at h
      rw [ha, map_zero] at h
      rw [← h, zero_mul]
    rw [hz, TensorProduct.tmul_zero]
  exact SheafOfModules.periodicTensorZero R M N f hraw

open MonoidalCategory in
private theorem periodicConstantMultiply_tensor_zero (a : A)
    (ha : algebraMap A B a = 0) :
    (periodicConstantFunctor.{r, uC, vC} J A).map
        (ModuleCat.ofHom (LinearMap.mulLeft A a)) ▷
      basisTarget.{r, uC, vC} J A B = 0 := by
  let N := basisTarget.{r, uC, vC} J A B
  let e := asIso (periodicUnitLift.{r, uC, vC} J A)
  have h := congrArg (fun f ↦ f ▷ N) (periodicUnitLift_comm.{r, uC, vC} J A a)
  simp only [comp_whiskerRight] at h
  rw [periodicUnitMultiply_tensor_zero.{r, uC, vC} J A B a ha,
    comp_zero] at h
  apply (cancel_mono (e.hom ▷ N)).1
  simpa only [N, e, asIso_hom, zero_comp] using h

attribute [irreducible] periodicConstantFunctor

private instance periodicConstantFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (periodicConstantFunctor.{r, uC, vC} J A) :=
  (periodicConstantFunctor_exact.{r, uC, vC} J A).1

private instance periodicConstantFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (periodicConstantFunctor.{r, uC, vC} J A) :=
  (periodicConstantFunctor_exact.{r, uC, vC} J A).2

private instance periodicConstantFunctor_additive :
    (periodicConstantFunctor.{r, uC, vC} J A).Additive :=
  Functor.additive_of_preserves_binary_products _

end CategoryTheory

namespace ModuleCat

variable (R : Type r) [CommRing R] (t : R)

private theorem lifted_square_zero (ht : t ^ 2 = 0) :
    (ULift.up t : ULift.{u} R) ^ 2 = 0 := by
  apply ULift.ext
  exact ht

private theorem lifted_annihilator
    (hann : ∀ a : R, t * a = 0 ↔ a ∈ Ideal.span ({t} : Set R)) :
    ∀ a : ULift.{u} R, (ULift.up t : ULift.{u} R) * a = 0 ↔
      a ∈ Ideal.span ({ULift.up t} : Set (ULift.{u} R)) := by
  intro a
  constructor
  · intro ha
    have h := congrArg ULift.down ha
    change t * a.down = 0 at h
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp ((hann a.down).mp h)
    apply Ideal.mem_span_singleton'.mpr
    refine ⟨ULift.up b, ?_⟩
    apply ULift.ext
    exact hb
  · intro ha
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp ha
    have hmem : a.down ∈ Ideal.span ({t} : Set R) :=
      Ideal.mem_span_singleton'.mpr ⟨b.down, congrArg ULift.down hb⟩
    apply ULift.ext
    exact (hann a.down).mpr hmem

private theorem lifted_quotient_surjective :
    Function.Surjective (RingHom.ulift
      (Ideal.Quotient.mk (Ideal.span ({t} : Set R))) :
        ULift.{u} R →+* ULift.{u} (R ⧸ Ideal.span ({t} : Set R))) := by
  intro b
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective b.down
  exact ⟨ULift.up a, ULift.ext _ _ ha⟩

private theorem lifted_quotient_kernel :
    RingHom.ker (RingHom.ulift
      (Ideal.Quotient.mk (Ideal.span ({t} : Set R))) :
        ULift.{u} R →+* ULift.{u} (R ⧸ Ideal.span ({t} : Set R))) =
      Ideal.span ({ULift.up t} : Set (ULift.{u} R)) := by
  ext a
  rw [RingHom.mem_ker]
  constructor
  · intro ha
    have h : Ideal.Quotient.mk (Ideal.span ({t} : Set R)) a.down = 0 :=
      congrArg ULift.down ha
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp
      (Ideal.Quotient.eq_zero_iff_mem.mp h)
    exact Ideal.mem_span_singleton'.mpr ⟨ULift.up b, ULift.ext _ _ hb⟩
  · intro ha
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp ha
    have hm : a.down ∈ Ideal.span ({t} : Set R) :=
      Ideal.mem_span_singleton'.mpr ⟨b.down, congrArg ULift.down hb⟩
    apply ULift.ext
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hm

@[instance_reducible]
private def liftedQuotientAlgebra :
    Algebra (ULift.{u} R) (ULift.{u} (R ⧸ Ideal.span ({t} : Set R))) :=
  (RingHom.ulift (Ideal.Quotient.mk (Ideal.span ({t} : Set R)))).toAlgebra

private noncomputable def liftedQuotientModuleIso :
    letI := liftedQuotientAlgebra.{r, u} R t
    ModuleCat.of (ULift.{u} R)
      ((ULift.{u} R) ⧸ Ideal.span ({ULift.up t} : Set (ULift.{u} R))) ≅
      ModuleCat.of (ULift.{u} R) (ULift.{u} (R ⧸ Ideal.span ({t} : Set R))) := by
  letI := liftedQuotientAlgebra.{r, u} R t
  let f := Algebra.linearMap (ULift.{u} R)
    (ULift.{u} (R ⧸ Ideal.span ({t} : Set R)))
  have hf : Function.Surjective f := lifted_quotient_surjective.{r, u} R t
  have hk : LinearMap.ker f =
      Ideal.span ({ULift.up t} : Set (ULift.{u} R)) := by
    change RingHom.ker (RingHom.ulift
      (Ideal.Quotient.mk (Ideal.span ({t} : Set R)))) = _
    exact lifted_quotient_kernel.{r, u} R t
  exact ((Submodule.quotEquivOfEq _ _ hk.symm).trans
    (LinearMap.quotKerEquivOfSurjective f hf)).toModuleIso

end ModuleCat

namespace SheafOfModules

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

set_option hygiene false in
local notation "𝒜" => SheafOfModules.{r}
  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)

private local instance calculationWeakAddCommGrp : HasWeakSheafify J AddCommGrpCat.{r} :=
  HasSheafify.isRightAdjoint

private local instance calculationAbelian : Abelian 𝒜 := inferInstance

private local instance calculationMonoidal : MonoidalCategory 𝒜 :=
  SheafOfModules.cochainModulesMonoidal R

private local instance calculationSymmetric : SymmetricCategory 𝒜 :=
  SheafOfModules.cochainModulesSymmetric R

private local instance calculationPreadditive : MonoidalPreadditive 𝒜 :=
  SheafOfModules.cochainModulesPreadditive R

private theorem periodicSiteFlatOfCategoricalFlat
    (M : 𝒜) (h : ObjectProperty.flat M) :
    SheafOfModules.IsFlatOnSite (R := R) M :=
  (exactFunctor 𝒜 𝒜).prop_of_iso (SheafOfModules.siteSheafTensorRightIso R M).symm h.2

private def periodicSheafHomologyIso
    (K : CochainComplex 𝒜 ℤ) (hd : ∀ i j, K.d i j = 0) (n : ℤ) :
    K.homology n ≅ K.X n :=
  (K.isoHomologyπ _ n rfl (hd _ _)).symm ≪≫ K.iCyclesIso n _ rfl (hd _ _)

private theorem periodicMappedTensorCalculation
    [HasDerivedCategory.{w} 𝒜]
    (A : Type r) [CommRing A] (F : ModuleCat.{r} A ⥤ 𝒜)
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.Additive]
    (M : 𝒜) (t : A) (ht : t ^ 2 = 0)
    (hann : ∀ a : A, t * a = 0 ↔ a ∈ Ideal.span ({t} : Set A))
    (eM : F.obj (ModuleCat.of A (A ⧸ Ideal.span ({t} : Set A))) ≅ M)
    (eU : F.obj (ModuleCat.of A A) ≅ 𝟙_ 𝒜)
    (hzero : F.map (ModuleCat.periodicDifferential A t) ▷ M = 0) (q : ℕ) :
    Nonempty ((DerivedCategory.homologyFunctor.{w} 𝒜 (-(q : ℤ))).obj
      (ringedSiteDerivedTensorOfUniverses R
        ((DerivedCategory.singleFunctor.{w} 𝒜 0).obj M)
        ((DerivedCategory.singleFunctor.{w} 𝒜 0).obj M)) ≅ M) := by
  let P₀ := ModuleCat.periodicResolution A t ht hann
  let P := (F.mapHomologicalComplex (.up ℤ)).obj P₀.cochainComplex
  let Q := DerivedCategory.Q.{w} (C := 𝒜)
  let single := CochainComplex.singleFunctor 𝒜 0
  have hflat (i : ℤ) : SheafOfModules.IsFlatOnSite (R := R) (P.X i) := by
    apply periodicSiteFlatOfCategoricalFlat R
    by_cases hi : i ≤ 0
    · obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat hi
      let e : P.X (-n) ≅ (𝟙_ 𝒜) :=
        F.mapIso (P₀.cochainComplexXIso (-n) n rfl) ≪≫
          eU
      have hu : ObjectProperty.flat (𝟙_ 𝒜) :=
        ObjectProperty.flat_of_tensorIso (λ_ (𝟙_ 𝒜))
      exact ObjectProperty.prop_of_iso ObjectProperty.flat e.symm hu
    · exact ObjectProperty.flat_of_isZero
        (F.map_isZero (P₀.cochainComplex.isZero_of_isStrictlyLE 0 i (by omega)))
  have hP : CochainComplex.IsKFlatIndependentCoefficients P :=
    SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R P 0 hflat
  let ep : Q.obj P ≅ (DerivedCategory.singleFunctor.{w} 𝒜 0).obj M :=
    asIso (Q.map ((F.mapHomologicalComplex (.up ℤ)).map P₀.π')) ≪≫
      Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app _) ≪≫
      Q.mapIso (single.mapIso eM) ≪≫
      (DerivedCategory.singleFunctorIsoCompQ.{w} 𝒜 0).symm.app M
  let el : Q.obj (single.obj M) ≅ (DerivedCategory.singleFunctor.{w} 𝒜 0).obj M :=
    (DerivedCategory.singleFunctorIsoCompQ.{w} 𝒜 0).symm.app M
  obtain ⟨e⟩ := SheafOfModules.intrinsicTensorModel R
    ((DerivedCategory.singleFunctor.{w} 𝒜 0).obj M)
    ((DerivedCategory.singleFunctor.{w} 𝒜 0).obj M) P (single.obj M) hP ep el
  let T := ((tensorRight M).mapHomologicalComplex (.up ℤ)).obj P
  have hchain (i j : ℕ) :
      (tensorRight M).map (F.map (P₀.complex.d i j)) = 0 := by
    change (tensorRight M).map (F.map ((ModuleCat.periodicComplex A t ht).d i j)) = 0
    by_cases h : i = j + 1
    · subst i
      rw [ModuleCat.periodicComplex_d_succ]
      exact hzero
    · rw [ModuleCat.periodicComplex_d_ne A t ht i j h, F.map_zero,
        (tensorRight M).map_zero]
  have hd (i j : ℤ) : T.d i j = 0 := by
    change (tensorRight M).map (F.map (P₀.cochainComplex.d i j)) = 0
    by_cases hi : i ≤ 0
    · by_cases hj : j ≤ 0
      · obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat hi
        obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat hj
        rw [P₀.cochainComplex_d (-m) (-n) m n rfl rfl,
          Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp]
        simp only [hchain, zero_comp, comp_zero]
      · exact ((tensorRight M).map_isZero
          (F.map_isZero (P₀.cochainComplex.isZero_of_isStrictlyLE 0 j
            (by omega)))).eq_of_tgt _ _
    · exact ((tensorRight M).map_isZero
        (F.map_isZero (P₀.cochainComplex.isZero_of_isStrictlyLE 0 i
          (by omega)))).eq_of_src _ _
  let et := e ≪≫ Q.mapIso
    ((CochainComplex.map₂HomologicalComplexFlipObjSingleIso (curriedTensor 𝒜) M).app P)
  let ex : T.X (-(q : ℤ)) ≅ M :=
    (tensorRight M).mapIso
      (F.mapIso (P₀.cochainComplexXIso (-(q : ℤ)) q rfl) ≪≫
        eU) ≪≫ λ_ M
  exact ⟨(DerivedCategory.homologyFunctor.{w} 𝒜 (-(q : ℤ))).mapIso et ≪≫
    (DerivedCategory.homologyFunctorFactors.{w} 𝒜 (-(q : ℤ))).app T ≪≫
    periodicSheafHomologyIso R T hd (-(q : ℤ)) ≪≫ ex⟩

end SheafOfModules

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
  (J : GrothendieckTopology C)
  [HasSheafify J CommRingCat.{r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  (A B : CommRingCat.{r}) [Algebra A B]

private local instance constantCalculationWeakCommRing : HasWeakSheafify J CommRingCat.{r} :=
  HasSheafify.isRightAdjoint

private theorem periodicConstantTensorCalculation
    [HasDerivedCategory.{w} (SheafOfModules.{r} (basisRing.{r, uC, vC} J A))]
    (t : A) (ht : t ^ 2 = 0)
    (hann : ∀ a : A, t * a = 0 ↔ a ∈ Ideal.span ({t} : Set A))
    (eB : ModuleCat.of A (A ⧸ Ideal.span ({t} : Set A)) ≅ ModuleCat.of A B)
    (hB : algebraMap A B t = 0) (q : ℕ) :
    Nonempty ((DerivedCategory.homologyFunctor.{w}
      (SheafOfModules.{r} (basisRing.{r, uC, vC} J A)) (-(q : ℤ))).obj
      (SheafOfModules.ringedSiteDerivedTensorOfUniverses
        ((constantSheaf J CommRingCat.{r}).obj A)
        ((DerivedCategory.singleFunctor.{w} _ 0).obj (basisTarget.{r, uC, vC} J A B))
        ((DerivedCategory.singleFunctor.{w} _ 0).obj (basisTarget.{r, uC, vC} J A B))) ≅
          basisTarget.{r, uC, vC} J A B) := by
  exact SheafOfModules.periodicMappedTensorCalculation
    ((constantSheaf J CommRingCat.{r}).obj A) A (periodicConstantFunctor.{r, uC, vC} J A)
    (basisTarget.{r, uC, vC} J A B) t ht hann
    ((periodicConstantFunctor.{r, uC, vC} J A).mapIso eB ≪≫
      periodicConstantAlgebraIso.{r, uC, vC} J A B)
    (asIso (periodicUnitLift.{r, uC, vC} J A))
    (periodicConstantMultiply_tensor_zero.{r, uC, vC} J A B t hB) q

end CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The constant quotient F_V, as a module over the constant commutative ring sheaf R_V.
It is the unit module of the constant quotient ring sheaf restricted along the constant
quotient map. The lift only places coefficients in a universe containing the site.
Source: blueprint main-20261015, sec-proetale-coefficients,
sk-def-localizing-closure-ctf-equals-bc.proof.md, "The examples";
Stacks Project, Tags 03CY and 06YU (blueprint: lem-sfb-square-zero-periodic-tensor). -/
def squareZeroQuotientModule (R : Type r) [CommRing R] (t : R) (V : Scheme.{u}) :
    SheafOfModules.{max r (u + 1)}
      ((sheafCompose (ProEt.topology V)
        (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
          ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
            (CommRingCat.of (ULift.{u + 1} R)))) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose (ProEt.topology V)
      (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).map
        ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).map
          (CommRingCat.ofHom (RingHom.ulift
            (Ideal.Quotient.mk (Ideal.span ({t} : Set R)))))))).obj
    (SheafOfModules.unit
      ((sheafCompose (ProEt.topology V)
        (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
          ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
            (CommRingCat.of (ULift.{u + 1} (R ⧸ Ideal.span ({t} : Set R)))))))

private theorem proetaleTopology_le_jointlySurjective :
    proetaleTopology.{u} ≤ jointlySurjectiveTopology := by
  rw [jointlySurjectiveTopology_eq_toGrothendieck_jointlySurjectivePretopology]
  change proetalePrecoverage.toGrothendieck ≤
    jointlySurjectivePrecoverage.toPretopology.toGrothendieck
  rw [Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck]
  exact Precoverage.toGrothendieck_mono (le_trans inf_le_right inf_le_left)

private theorem proetale_bot_not_cover (V : Scheme.{u}) (U : V.ProEt)
    (hU : Nonempty U.left) :
    ¬ (⊥ : Sieve U) ∈ ProEt.topology V U := by
  intro h
  let F := ProEt.forget V ⋙ Over.forget V
  have hc : CoverPreserving (ProEt.topology V) proetaleTopology F :=
    CoverPreserving.of_isContinuous F (ProEt.topology V) proetaleTopology
  have hb : (⊥ : Sieve U.left) ∈ proetaleTopology U.left := by
    simpa only [Sieve.functorPushforward_bot, F, Functor.comp_obj,
      ProEt.forget, MorphismProperty.Over.forget, MorphismProperty.Comma.forget,
      Over.forget_obj] using hc.cover_preserve h
  have hs := proetaleTopology_le_jointlySurjective U.left hb
  change (⊥ : Presieve U.left) ∈ jointlySurjectivePrecoverage U.left at hs
  rw [Precoverage.mem_comap_iff, Presieve.map_bot,
    Types.mem_jointlySurjectivePrecoverage_iff] at hs
  obtain ⟨x⟩ := hU
  obtain ⟨W, f, hf, _⟩ := hs x
  exact hf

private theorem constant_ring_unit_injective
    (V : Scheme.{u}) (A : Type r) [CommRing A]
    [HasSheafify (ProEt.topology V) CommRingCat.{r}]
    [(ProEt.topology V).WEqualsLocallyBijective CommRingCat.{r}]
    (U : V.ProEt) (hU : Nonempty U.left) :
    Function.Injective ((toSheafify (ProEt.topology V)
      ((Functor.const V.ProEtᵒᵖ).obj (CommRingCat.of A))).app (op U)) := by
  intro a b hab
  by_contra hne
  have h := Presheaf.equalizerSieve_mem (ProEt.topology V)
    (toSheafify (ProEt.topology V)
      ((Functor.const V.ProEtᵒᵖ).obj (CommRingCat.of A))) a b hab
  have he : Presheaf.equalizerSieve (F :=
      (Functor.const V.ProEtᵒᵖ).obj (CommRingCat.of A))
      (X := op U) a b = ⊥ := by
    ext W f
    simp [Presheaf.equalizerSieve, hne]
  rw [he] at h
  exact proetale_bot_not_cover V U hU h

private theorem squareZeroQuotientModule_nonzero
    (R : Type r) [CommRing R] (t : R) (V : Scheme.{u})
    [Nontrivial (R ⧸ Ideal.span ({t} : Set R))] (hV : Nonempty V) :
    ¬ IsZero (squareZeroQuotientModule R t V) := by
  let J := ProEt.topology V
  let B := ULift.{u + 1} (R ⧸ Ideal.span ({t} : Set R))
  let : EssentiallySmall.{max r (u + 1)} V.ProEt := essentiallySmallSelf.{r} _
  let : J.WEqualsLocallyBijective CommRingCat.{max r (u + 1)} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u,
      max r (u + 1), u + 1, (max r (u + 1)) + 1,
      max r (u + 1), max r (u + 1), max r (u + 1)} _
  let U : V.ProEt := ProEt.mk (𝟙 V)
  intro hz
  let η := (toSheafify J ((Functor.const V.ProEtᵒᵖ).obj (CommRingCat.of B))).app (op U)
  have hid : 𝟙 (squareZeroQuotientModule R t V) = 0 := hz.eq_of_src _ _
  have he : η 1 = η 0 := by
    have h := congrArg (fun f : squareZeroQuotientModule R t V ⟶
        squareZeroQuotientModule R t V ↦ f.val.app (op U) (η 1)) hid
    change η 1 = 0 at h
    simpa only [map_zero] using h
  have hi := constant_ring_unit_injective V B U hV
  exact (one_ne_zero : (1 : B) ≠ 0) (hi he)

/-- The constant-sheaf self-tensor has F_V in every nonpositive cohomological degree.
Source: blueprint main-20261015, sec-proetale-coefficients,
sk-def-localizing-closure-ctf-equals-bc.proof.md, "The examples";
Stacks Project, Tags 093J, 06YQ, 06YU and 03CY.
(blueprint: lem-sfb-square-zero-periodic-tensor).

Proof:
1. Apply constant module sheafification to the periodic free resolution of
   ModuleCat.square_zero_periodic_resolution_tensor. Exactness follows from
   lem-weil-pbc-finite-type-constant-exact: kernels, cokernels and therefore images
   are preserved, so the augmentation to F_V[0] is a quasi-isomorphism.
2. The unit tensor maps R_V ⊗ M ≅ M identify tensoring with R_V with the identity;
   thus R_V and zero are flat (def-pur-sheaf-tensor-product, def-pc-flat-sheaf-modules).
   The resolution is bounded above, so lem-pc-bounded-above-flat-kflat-site makes it K-flat.
3. By lem-weil-derived-tensor-resolution-independent this resolution computes
   def-weil-derived-tensor. Each nonpositive total tensor term is F_V, and its
   differential is zero since t acts by zero on R/(t). The cohomology is therefore F_V
   in every degree -q, including q = 0 (def-weil-abstract-derived-category).
4. If F is nonzero and V nonempty, choose a nonzero a in F. If its constant section
   vanished, lem-sf-constant-module-unit-locally-bijective would give a cover on which
   a equals zero. Joint surjectivity of a pro-etale cover gives a nonempty member, where
   restriction of the constant presheaf is the identity, a contradiction. Hence F_V and
   all the isomorphic displayed cohomology sheaves are nonzero. -/
theorem square_zero_periodic_tensor (R : Type r) [CommRing R]
    (t : R) (ht : t ^ 2 = 0)
    (hann : ∀ a : R, t * a = 0 ↔ a ∈ Ideal.span ({t} : Set R))
    (V : Scheme.{u})
    [hD : @HasDerivedCategory.{w, max r (u + 1), (max r (u + 1)) + 1}
      (SheafOfModules.{max r (u + 1)}
        ((sheafCompose (ProEt.topology V)
          (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
            ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
              (CommRingCat.of (ULift.{u + 1} R)))))
      inferInstance
      (@SheafOfModules.instAbelian.{max r (u + 1), u, max r (u + 1), u + 1}
        V.ProEt inferInstance (ProEt.topology V)
        ((sheafCompose (ProEt.topology V)
          (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
            ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
              (CommRingCat.of (ULift.{u + 1} R))))
        (WeilConjectures.integralCoefficientAbSheafify.{u, r} V)
        (WeilConjectures.integralCoefficientAbLocallyBijective.{u, r} V))] :
    (∀ q : ℕ,
      Nonempty ((@DerivedCategory.homologyFunctor (SheafOfModules.{max r (u + 1)}
            ((sheafCompose (ProEt.topology V)
              (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
                ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
                  (CommRingCat.of (ULift.{u + 1} R)))))
          inferInstance
          (@SheafOfModules.instAbelian.{max r (u + 1), u, max r (u + 1), u + 1}
        V.ProEt inferInstance (ProEt.topology V)
        ((sheafCompose (ProEt.topology V)
          (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
            ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
              (CommRingCat.of (ULift.{u + 1} R))))
        (WeilConjectures.integralCoefficientAbSheafify.{u, r} V)
        (WeilConjectures.integralCoefficientAbLocallyBijective.{u, r} V)) hD (-(q : ℤ))).obj
        (@SheafOfModules.ringedSiteDerivedTensorOfUniverses.{u + 1, u, max r (u + 1), w}
          V.ProEt _ _ (ProEt.topology V)
          ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
            (CommRingCat.of (ULift.{u + 1} R)))
          (WeilConjectures.integralCoefficientAbSheafify.{u, r} V)
          (WeilConjectures.integralCoefficientAbLocallyBijective.{u, r} V) hD
          ((@DerivedCategory.singleFunctor (SheafOfModules.{max r (u + 1)}
            ((sheafCompose (ProEt.topology V)
              (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
                ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
                  (CommRingCat.of (ULift.{u + 1} R)))))
          inferInstance
          (@SheafOfModules.instAbelian.{max r (u + 1), u, max r (u + 1), u + 1}
        V.ProEt inferInstance (ProEt.topology V)
        ((sheafCompose (ProEt.topology V)
          (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
            ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
              (CommRingCat.of (ULift.{u + 1} R))))
        (WeilConjectures.integralCoefficientAbSheafify.{u, r} V)
        (WeilConjectures.integralCoefficientAbLocallyBijective.{u, r} V)) hD 0).obj
            (squareZeroQuotientModule R t V))
          ((@DerivedCategory.singleFunctor (SheafOfModules.{max r (u + 1)}
            ((sheafCompose (ProEt.topology V)
              (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
                ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
                  (CommRingCat.of (ULift.{u + 1} R)))))
          inferInstance
          (@SheafOfModules.instAbelian.{max r (u + 1), u, max r (u + 1), u + 1}
        V.ProEt inferInstance (ProEt.topology V)
        ((sheafCompose (ProEt.topology V)
          (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
            ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
              (CommRingCat.of (ULift.{u + 1} R))))
        (WeilConjectures.integralCoefficientAbSheafify.{u, r} V)
        (WeilConjectures.integralCoefficientAbLocallyBijective.{u, r} V)) hD 0).obj
            (squareZeroQuotientModule R t V))) ≅
            squareZeroQuotientModule R t V)) ∧
    (Nontrivial (R ⧸ Ideal.span ({t} : Set R)) → Nonempty V →
      ¬ IsZero (squareZeroQuotientModule R t V) ∧
        ∀ q : ℕ, ¬ IsZero ((@DerivedCategory.homologyFunctor (SheafOfModules.{max r (u + 1)}
            ((sheafCompose (ProEt.topology V)
              (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
                ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
                  (CommRingCat.of (ULift.{u + 1} R)))))
          inferInstance
          (@SheafOfModules.instAbelian.{max r (u + 1), u, max r (u + 1), u + 1}
        V.ProEt inferInstance (ProEt.topology V)
        ((sheafCompose (ProEt.topology V)
          (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
            ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
              (CommRingCat.of (ULift.{u + 1} R))))
        (WeilConjectures.integralCoefficientAbSheafify.{u, r} V)
        (WeilConjectures.integralCoefficientAbLocallyBijective.{u, r} V)) hD (-(q : ℤ))).obj
          (@SheafOfModules.ringedSiteDerivedTensorOfUniverses.{u + 1, u, max r (u + 1), w}
          V.ProEt _ _ (ProEt.topology V)
            ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
              (CommRingCat.of (ULift.{u + 1} R)))
          (WeilConjectures.integralCoefficientAbSheafify.{u, r} V)
          (WeilConjectures.integralCoefficientAbLocallyBijective.{u, r} V) hD
            ((@DerivedCategory.singleFunctor (SheafOfModules.{max r (u + 1)}
            ((sheafCompose (ProEt.topology V)
              (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
                ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
                  (CommRingCat.of (ULift.{u + 1} R)))))
          inferInstance
          (@SheafOfModules.instAbelian.{max r (u + 1), u, max r (u + 1), u + 1}
        V.ProEt inferInstance (ProEt.topology V)
        ((sheafCompose (ProEt.topology V)
          (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
            ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
              (CommRingCat.of (ULift.{u + 1} R))))
        (WeilConjectures.integralCoefficientAbSheafify.{u, r} V)
        (WeilConjectures.integralCoefficientAbLocallyBijective.{u, r} V)) hD 0).obj
            (squareZeroQuotientModule R t V))
            ((@DerivedCategory.singleFunctor (SheafOfModules.{max r (u + 1)}
            ((sheafCompose (ProEt.topology V)
              (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
                ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
                  (CommRingCat.of (ULift.{u + 1} R)))))
          inferInstance
          (@SheafOfModules.instAbelian.{max r (u + 1), u, max r (u + 1), u + 1}
        V.ProEt inferInstance (ProEt.topology V)
        ((sheafCompose (ProEt.topology V)
          (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
            ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
              (CommRingCat.of (ULift.{u + 1} R))))
        (WeilConjectures.integralCoefficientAbSheafify.{u, r} V)
        (WeilConjectures.integralCoefficientAbLocallyBijective.{u, r} V)) hD 0).obj
            (squareZeroQuotientModule R t V))))) := by
  let : HasSheafify (ProEt.topology V) AddCommGrpCat.{max r (u + 1)} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, r} V
  let : (ProEt.topology V).WEqualsLocallyBijective AddCommGrpCat.{max r (u + 1)} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, r} V
  let : EssentiallySmall.{max r (u + 1)} V.ProEt := essentiallySmallSelf.{r} _
  let : (ProEt.topology V).WEqualsLocallyBijective CommRingCat.{max r (u + 1)} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u,
      max r (u + 1), u + 1, (max r (u + 1)) + 1,
      max r (u + 1), max r (u + 1), max r (u + 1)} _
  let := ModuleCat.liftedQuotientAlgebra.{r, u + 1} R t
  let A := CommRingCat.of (ULift.{u + 1} R)
  let B := CommRingCat.of (ULift.{u + 1} (R ⧸ Ideal.span ({t} : Set R)))
  have hB : algebraMap A B (ULift.up t) = 0 := by
    apply ULift.ext
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self t)
  refine (fun hcalc ↦ And.intro hcalc ?_) ?_
  · intro hF hV
    let := hF
    have hN := squareZeroQuotientModule_nonzero R t V hV
    refine ⟨hN, ?_⟩
    intro q hz
    obtain ⟨e⟩ := hcalc q
    exact hN (e.isZero_iff.1 hz)
  · intro q
    exact CategoryTheory.periodicConstantTensorCalculation.{max r (u + 1), w, u + 1, u}
      (ProEt.topology V) A B (ULift.up t)
      (ModuleCat.lifted_square_zero.{r, u + 1} R t ht)
      (ModuleCat.lifted_annihilator.{r, u + 1} R t hann)
      (ModuleCat.liftedQuotientModuleIso.{r, u + 1} R t) hB q

end AlgebraicGeometry.Scheme
