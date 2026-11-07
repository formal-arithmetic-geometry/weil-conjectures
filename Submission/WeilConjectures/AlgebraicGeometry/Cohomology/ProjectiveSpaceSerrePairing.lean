/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Submission.WeilConjectures.AlgebraicGeometry.Cohomology.Affine.LerayNatural
public import Submission.WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistMul
public import Submission.WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveFinite
import Submission.WeilConjectures.Compactification.Defs
import Mathlib.Algebra.Category.ModuleCat.Projective

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# The Serre pairing on projective space

Let `A` be a commutative ring and `ℙ = ℙ(n; Spec A)` with `Fintype.card n = d + 1`. Multiplying
by a global section `t` of `𝒪(a)` is a morphism `𝒪(b) ⟶ 𝒪(a + b)` (`twistMulHom`); the induced
map on cohomology gives the `A`-bilinear **Serre pairing**
`H⁰(ℙ, 𝒪(a)) × H^q(ℙ, 𝒪(b)) → H^q(ℙ, 𝒪(a + b))`, `(t, x) ↦ H^q(t ·)(x)`
(`AlgebraicGeometry.ProjectiveSpace.twistMulPairing`).

For `d ≥ 1`, `m ≤ -d - 1` and `D = -m - d - 1`, composing with the trace
`Hᵈ(ℙ, 𝒪(-d-1)) ≅ A` gives a perfect pairing `H⁰(ℙ, 𝒪(D)) × Hᵈ(ℙ, 𝒪(m)) → A`
(`AlgebraicGeometry.ProjectiveSpace.isPerfPair_twistSerrePairing`), and the induced isomorphism
`Hᵈ(ℙ, 𝒪(m)) ≅ Hom_A(A[x₀, …, x_d]_D, A)` is described by
`AlgebraicGeometry.ProjectiveSpace.twistHTopLinearEquivDual_apply`.

The proof transports the problem to the monomial Čech complex, where the perfectness is
`AlgebraicGeometry.ProjectiveSpace.monomialCechComplexHomologyTopLinearEquivDual_apply`:

* Leray's isomorphism is chosen naturally in the sheaf (`cechComplexHomologyLinearEquivH`), which
  gives a named isomorphism `H^q(ℙ, 𝒪(m)) ≅ H^q` of the monomial Čech complex
  (`twistHLinearEquivMonomialCechHomology`) natural for morphisms of twisting sheaves which are
  compatible with morphisms of monomial Čech complexes;
* the product of Laurent polynomial sections is the section of the product
  (`twistTensorIso_hom_app_twistLaurentSection`), so multiplication by the global section of a
  polynomial `F` corresponds to multiplication by `F` on the monomial Čech complex
  (`cechComplexTwistIso_hom_comp_monomialCechMul`);
* global sections of `𝒪(D)`, `D ≥ 0`, are the homogeneous polynomials of degree `D`
  (`bijective_homogeneousSubmoduleToTwist`).

## Main definitions and statements

- `AlgebraicGeometry.ProjectiveSpace.twistMulPairing`: the Serre pairing.
- `AlgebraicGeometry.ProjectiveSpace.twistTopTrace`: the trace `Hᵈ(ℙ, 𝒪(-d-1)) ≅ A`.
- `AlgebraicGeometry.ProjectiveSpace.twistSerrePairing`: the Serre pairing followed by the trace.
- `AlgebraicGeometry.ProjectiveSpace.isPerfPair_twistSerrePairing`: it is perfect.
- `AlgebraicGeometry.ProjectiveSpace.twistHTopLinearEquivDual` and
  `AlgebraicGeometry.ProjectiveSpace.twistHTopLinearEquivDual_apply`: the induced isomorphism
  `Hᵈ(ℙ, 𝒪(m)) ≅ Hom_A(A[x₀, …, x_d]_D, A)`.
- `AlgebraicGeometry.ProjectiveSpace.homogeneousSubmoduleLinearEquivTwist`:
  `A[x₀, …, x_d]_D ≅ H⁰(ℙ, 𝒪(D))`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

noncomputable section

namespace AlgebraicGeometry.ProjectiveSpace

open Scheme.Modules MvPolynomial

variable {n : Type u} [Fintype n] {A : Type u} [CommRing A]

section LaurentSection

variable (A) in
/-- The structure ring homomorphism `A ⟶ Γ(ℙ(n; Spec A), ⊤)`. -/
abbrev structureRingHom : A →+* Γ(ℙ(n; Spec (.of A)), ⊤) :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫ (ℙ(n; Spec (.of A)) ↘ Spec (.of A)).appTop).hom

variable (A) in
/-- The structure ring homomorphism `A ⟶ Γ(ℙ(n; Spec A), U)` of an open `U`. -/
abbrev structureRingHomOpen (U : (ℙ(n; Spec (.of A))).Opens) : A →+* Γ(ℙ(n; Spec (.of A)), U) :=
  ((ℙ(n; Spec (.of A))).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp
    (structureRingHom A)

open Classical in
variable (A) in
/-- The Laurent monomial `xᵉ` as a section of `𝒪(m)` over `U_s = ⋂_{i ∈ s} D₊(xᵢ)` if it is
regular there, and `0` otherwise. -/
def twistLaurentMonomial (m : ℤ) (s : Set n) (e : n → ℤ) :
    Γ(twist n (Spec (.of A)) m, toProjInt n (Spec (.of A)) ⁻¹ᵁ basicOpenInt n s) :=
  if h : e ∈ laurentExponents s m then twistMonomialSection (Spec (.of A)) s ⟨e, h⟩ else 0

/-- A Laurent monomial regular on `U_s` is the section `xᵉ`. -/
lemma twistLaurentMonomial_of_mem {m : ℤ} {s : Set n} {e : n → ℤ}
    (h : e ∈ laurentExponents s m) :
    twistLaurentMonomial A m s e = twistMonomialSection (Spec (.of A)) s ⟨e, h⟩ :=
  dite_eq_left h

variable (A) in
/-- The `A`-linear map sending a finitely supported family of coefficients `(cₑ)` to the
section `∑ cₑ xᵉ` of `𝒪(m)` over `U_s = ⋂_{i ∈ s} D₊(xᵢ)`, the Laurent monomials which are not
regular on `U_s` being dropped. -/
def twistLaurentLinearMap (m : ℤ) (s : Set n) :
    ((n → ℤ) →₀ A) →ₗ[A] (ModuleCat.restrictScalars (structureRingHom (n := n) A)).obj
      ((twist n (Spec (.of A)) m).presheafModuleCat.obj
        (op (toProjInt n (Spec (.of A)) ⁻¹ᵁ basicOpenInt n s))) :=
  Finsupp.linearCombination A (twistLaurentMonomial A m s)

variable (A) in
/-- **The section of `𝒪(m)` of a Laurent polynomial**: the section `∑ cₑ xᵉ` of `𝒪(m)` over
`U_s = ⋂_{i ∈ s} D₊(xᵢ)` of a finitely supported family of coefficients `(cₑ)`, the Laurent
monomials which are not regular on `U_s` being dropped. -/
def twistLaurentSection (m : ℤ) (s : Set n) (c : (n → ℤ) →₀ A) :
    Γ(twist n (Spec (.of A)) m, toProjInt n (Spec (.of A)) ⁻¹ᵁ basicOpenInt n s) :=
  twistLaurentLinearMap A m s c

/-- On families supported on the Laurent monomials regular on `U_s`, `twistLaurentLinearMap` is
`twistMonomialLinearMap`. -/
lemma twistMonomialLinearMap_supportedEquivFinsupp {m : ℤ} {s : Set n}
    (c : Finsupp.supported A A (laurentExponents s m)) :
    twistMonomialLinearMap A m s (Finsupp.supportedEquivFinsupp _ c) =
      twistLaurentLinearMap A m s c := by
  have h := LinearMap.congr_fun (Finsupp.linearCombination_restrict (R := A)
    (v := fun e ↦ twistLaurentLinearMap A m s (Finsupp.single e 1)) (laurentExponents s m))
    (Finsupp.supportedEquivFinsupp _ c)
  have hv : (laurentExponents s m).domRestrict
      (fun e ↦ twistLaurentLinearMap A m s (Finsupp.single e 1)) =
      fun e ↦ twistMonomialSection (Spec (.of A)) s e := by
    funext e
    simp only [Set.domRestrict_apply, twistLaurentLinearMap,
      Finsupp.linearCombination_single, one_smul]
    exact twistLaurentMonomial_of_mem e.2
  rw [hv] at h
  simp only [Finsupp.linearCombinationOn, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Submodule.coe_subtype,
    LinearMap.codRestrict_apply] at h
  refine h.trans ?_
  rw [twistLaurentLinearMap, Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
  refine Finsupp.sum_congr fun e _ ↦ ?_
  simp only [Finsupp.linearCombination_single, one_smul]

/-- The section of a single Laurent monomial `r xᵉ`. -/
lemma twistLaurentSection_single (m : ℤ) (s : Set n) (e : n → ℤ) (r : A) :
    twistLaurentSection A m s (Finsupp.single e r) =
      structureRingHomOpen A (toProjInt n (Spec (.of A)) ⁻¹ᵁ basicOpenInt n s) r •
        twistLaurentMonomial A m s e := by
  rw [twistLaurentSection, twistLaurentLinearMap, Finsupp.linearCombination_single]
  rfl

/-- `twistLaurentSection` is `A`-linear. -/
lemma twistLaurentSection_smul (m : ℤ) (s : Set n) (r : A) (c : (n → ℤ) →₀ A) :
    twistLaurentSection A m s (r • c) =
      structureRingHomOpen A (toProjInt n (Spec (.of A)) ⁻¹ᵁ basicOpenInt n s) r •
        twistLaurentSection A m s c := by
  rw [twistLaurentSection, LinearMap.map_smul]
  rfl

/-- `twistLaurentSection` is additive. -/
lemma twistLaurentSection_add (m : ℤ) (s : Set n) (c c' : (n → ℤ) →₀ A) :
    twistLaurentSection A m s (c + c') =
      twistLaurentSection A m s c + twistLaurentSection A m s c' :=
  map_add _ _ _

/-- `twistLaurentSection` sends `0` to `0`. -/
lemma twistLaurentSection_zero (m : ℤ) (s : Set n) :
    twistLaurentSection A m s 0 = 0 :=
  map_zero _


omit [Fintype n] in
/-- The structure morphism `A ⟶ Γ(ℙ, U)` is compatible with restriction. -/
lemma presheaf_map_structureRingHomOpen {U V : (ℙ(n; Spec (.of A))).Opens} (h : V ≤ U) (r : A) :
    (ℙ(n; Spec (.of A))).presheaf.map (homOfLE h).op (structureRingHomOpen A U r) =
      structureRingHomOpen A V r := by
  simp only [structureRingHomOpen, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- **Restriction of Laurent polynomial sections**: for `t ⊆ s`, the restriction to `U_s` of
the section of a Laurent polynomial regular on `U_t` is its section over `U_s`. -/
lemma twistLaurentSection_map {m : ℤ} {s t : Set n} (hts : t ⊆ s) {c : (n → ℤ) →₀ A}
    (hc : c ∈ Finsupp.supported A A (laurentExponents t m)) :
    (twist n (Spec (.of A)) m).presheaf.map (homOfLE ((toProjInt n (Spec (.of A))).preimage_mono
        (Proj.basicOpen_monomialToNat_indicator_mono (R := ULift.{u} ℤ) hts))).op
        (twistLaurentSection A m t c) =
      twistLaurentSection A m s c := by
  rw [Finsupp.supported_eq_span_single] at hc
  induction hc using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, he, rfl⟩ := hx
    rw [twistLaurentSection_single, twistLaurentSection_single, map_smul,
      presheaf_map_structureRingHomOpen, twistLaurentMonomial_of_mem he,
      twistLaurentMonomial_of_mem (laurentExponents_mono hts m he),
      twist_presheaf_map_twistMonomialSection hts]
  | zero => rw [twistLaurentSection_zero, map_zero, twistLaurentSection_zero]
  | add x x' _ _ h h' => rw [twistLaurentSection_add, map_add, h, h', twistLaurentSection_add]
  | smul r x _ h =>
    rw [twistLaurentSection_smul, map_smul, presheaf_map_structureRingHomOpen, h,
      twistLaurentSection_smul]

variable (n) in
/-- `U_∅ = D₊(1)` is all of `ℙ(n; S)`. -/
lemma preimage_basicOpenInt_empty (S : Scheme.{u}) :
    toProjInt n S ⁻¹ᵁ basicOpenInt n (∅ : Set n) = ⊤ :=
  eq_top_iff.2 fun _ _ ↦ Proj.mem_basicOpen_monomialToNat_indicator.2 fun _ hi ↦ hi.elim

/-- Monomials are Laurent monomials regular on every `U_s`. -/
lemma monomialExponents_subset_laurentExponents {m : ℤ} (s : Set n) :
    monomialExponents n m ⊆ laurentExponents s m :=
  fun _ he ↦ ⟨he.1, fun i _ ↦ he.2 i⟩

variable (A) in
/-- **The global section of `𝒪(a)` of a polynomial**: the section `∑ cₑ xᵉ` of `𝒪(a)` over
`ℙ(n; Spec A)` of a family of coefficients `(cₑ)`, the terms with `e ≱ 0` or `∑ eᵢ ≠ a` being
dropped. -/
def twistPolynomialSection (a : ℤ) (c : (n → ℤ) →₀ A) : Γ(twist n (Spec (.of A)) a, ⊤) :=
  (twist n (Spec (.of A)) a).presheaf.map
    (homOfLE (preimage_basicOpenInt_empty n (Spec (.of A))).ge).op (twistLaurentSection A a ∅ c)

/-- The restriction of the global section of a polynomial to `U_s` is its section over `U_s`. -/
lemma twistPolynomialSection_map {a : ℤ} (s : Set n) {c : (n → ℤ) →₀ A}
    (hc : c ∈ Finsupp.supported A A (monomialExponents n a)) :
    (twist n (Spec (.of A)) a).presheaf.map
        (homOfLE (le_top : toProjInt n (Spec (.of A)) ⁻¹ᵁ basicOpenInt n s ≤ ⊤)).op
        (twistPolynomialSection A a c) =
      twistLaurentSection A a s c := by
  rw [twistPolynomialSection, presheaf_map_homOfLE_map_homOfLE]
  exact twistLaurentSection_map (Set.empty_subset s)
    (Finsupp.supported_mono (monomialExponents_subset_laurentExponents ∅) hc)

end LaurentSection

section Cech

variable {a b b' : ℤ}


end Cech


section Leray

omit [Fintype n] in
variable (A) in
/-- The finite intersections of the standard opens of `ℙ(n; Spec A)` are affine. -/
lemma isAffineOpen_biInf_standardOpen [Finite n] (s : Finset n) (hs : s.Nonempty) :
    IsAffineOpen (⨅ i ∈ s, standardOpen n (Spec (.of A)) i) :=
  have := Fintype.ofFinite n
  haveI : IsSeparated (terminal.from ℙ(n; Spec (.of A))) := by
    rw [← terminal.comp_from (ℙ(n; Spec (.of A)) ↘ Spec (.of A))]
    infer_instance
  IsAffineOpen.biInf (s : Set n) s.finite_toSet hs fun i _ ↦ isAffineOpen_standardOpen n _ i

variable (A) in
/-- **The cohomology of `𝒪(m)` on `ℙ(n; Spec A)` is that of the monomial Čech complex**, as
`A`-modules: Leray's isomorphism `cechComplexHomologyLinearEquivH` for the standard affine
covering, followed by the identification `cechComplexTwistIso` of the Čech complex of `𝒪(m)`
with the monomial Čech complex. It is natural for morphisms of twisting sheaves which are
compatible with morphisms of monomial Čech complexes
(`twistHLinearEquivMonomialCechHomology_map`).

(blueprint: `lem-pc-projective-space-twist-cohomology`) -/
def twistHLinearEquivMonomialCechHomology (m : ℤ) (q : ℕ) :
    letI := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) (twist n (Spec (.of A)) m) q
    (twist n (Spec (.of A)) m).H q ≃ₗ[A] (monomialCechComplex n A m).homology q :=
  letI := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) (twist n (Spec (.of A)) m) q
  let e₁ := cechComplexHomologyLinearEquivH (standardOpen n (Spec (.of A)))
    (isAffineOpen_biInf_standardOpen A) (iSup_standardOpen n _) (twist n (Spec (.of A)) m) q
  ({ e₁.symm.toAddEquiv with map_smul' := fun c x ↦ e₁.symm.map_smul (structureRingHom A c) x } :
      (twist n (Spec (.of A)) m).H q ≃ₗ[A] (ModuleCat.restrictScalars (structureRingHom A)).obj
        (((cechComplexFunctor (standardOpen n (Spec (.of A)))).obj
          (twist n (Spec (.of A)) m).presheafModuleCat).homology q)) ≪≫ₗ
    ((ModuleCat.restrictScalarsHomologyIso (structureRingHom A) _ q).symm ≪≫
      (HomologicalComplex.homologyFunctor _ _ q).mapIso (cechComplexTwistIso n A m)).toLinearEquiv


end Leray

section Pairing

omit [Fintype n] in
/-- Multiplication by `r • t`, for `r ∈ A` and a global section `t` of `𝒪(a)`, is
multiplication by `t` followed by multiplication by `r`. -/
lemma twistMulHom_smul_structureRingHom {a b c : ℤ} (h : a + b = c) (r : A)
    (t : (ModuleCat.restrictScalars (structureRingHom (n := n) A)).obj
      ((twist n (Spec (.of A)) a).presheafModuleCat.obj (op ⊤))) :
    twistMulHom h (r • t) =
      twistMulHom h t ≫ (twist n (Spec (.of A)) c).smulHom (structureRingHom A r) := by
  rw [← twistMulHom_smul]
  congr 1
  rw [ModuleCat.restrictScalars.smul_def, ModuleCat.restrictScalars.smul_def]
  congr 1
  rw [Subsingleton.elim (isTerminalTop.op.to (op ⊤)) (𝟙 (op (⊤ : (ℙ(n; Spec (.of A))).Opens)))]
  exact ConcreteCategory.congr_hom ((ℙ(n; Spec (.of A))).presheaf.map_id _) _

omit [Fintype n] in
variable (A) in
/-- **The Serre pairing** `H⁰(ℙⁿ_A, 𝒪(a)) × H^q(ℙⁿ_A, 𝒪(b)) → H^q(ℙⁿ_A, 𝒪(a + b))`: a global
section `t` of `𝒪(a)` and a class `x` pair to the image `H^q(t ·)(x)` of `x` under the map
induced by multiplication by `t`, `𝒪(b) ⟶ 𝒪(a + b)` (`twistMulHom`). It is `A`-bilinear.

(blueprint: `lem-pc-projective-space-serre-pairing`) -/
def twistMulPairing {a b c : ℤ} (h : a + b = c) (q : ℕ) :
    letI := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) (twist n (Spec (.of A)) b) q
    letI := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) (twist n (Spec (.of A)) c) q
    (ModuleCat.restrictScalars (structureRingHom (n := n) A)).obj
        ((twist n (Spec (.of A)) a).presheafModuleCat.obj (op ⊤)) →ₗ[A]
      (twist n (Spec (.of A)) b).H q →ₗ[A] (twist n (Spec (.of A)) c).H q :=
  letI := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) (twist n (Spec (.of A)) b) q
  letI := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) (twist n (Spec (.of A)) c) q
  LinearMap.mk₂ A (fun t x ↦ H.map (twistMulHom h t) q x)
    (fun t t' x ↦ (congrArg (fun φ ↦ H.map φ q x) (twistMulHom_add h t t')).trans
      (H.map_add_apply _ _ q x))
    (fun r t x ↦ (congrArg (fun φ ↦ H.map φ q x) (twistMulHom_smul_structureRingHom h r t)).trans
      (H.map_comp_apply _ _ q x))
    (fun _ _ _ ↦ map_add _ _ _)
    (fun r _ x ↦ H.map_smul _ q (structureRingHom A r) x)


variable (A) in
/-- The `A`-linear map sending a family of coefficients `(cₑ)` to the global section
`∑ cₑ xᵉ` of `𝒪(a)` (`twistPolynomialSection`). -/
def twistPolynomialLinearMap (a : ℤ) :
    ((n → ℤ) →₀ A) →ₗ[A] (ModuleCat.restrictScalars (structureRingHom (n := n) A)).obj
      ((twist n (Spec (.of A)) a).presheafModuleCat.obj (op ⊤)) :=
  ((ModuleCat.restrictScalars (structureRingHom (n := n) A)).map
    ((twist n (Spec (.of A)) a).presheafModuleCat.map
      (homOfLE (preimage_basicOpenInt_empty n (Spec (.of A))).ge).op)).hom ∘ₗ
    twistLaurentLinearMap A a ∅


variable (A) in
/-- The coefficients of a homogeneous polynomial, as a Laurent polynomial. -/
def homogeneousSubmoduleCoeff (D : ℕ) :
    MvPolynomial.homogeneousSubmodule n A D →ₗ[A] ((n → ℤ) →₀ A) where
  toFun f := (toLaurent n A f).coeff
  map_add' f g := by
    rw [Submodule.coe_add, map_add, AddMonoidAlgebra.coeff_add]
  map_smul' r f := by
    rw [Submodule.coe_smul, toLaurent_smul, AddMonoidAlgebra.coeff_smul, RingHom.id_apply]

variable (A) in
/-- **Homogeneous polynomials as global sections**: a homogeneous polynomial `f` of degree `D`
goes to the global section of `𝒪(D)` it defines on `ℙ(n; Spec A)`.

(blueprint: `lem-pc-projective-space-twist-cohomology` (i)) -/
def homogeneousSubmoduleToTwist (D : ℕ) :
    MvPolynomial.homogeneousSubmodule n A D →ₗ[A]
      (ModuleCat.restrictScalars (structureRingHom (n := n) A)).obj
        ((twist n (Spec (.of A)) D).presheafModuleCat.obj (op ⊤)) :=
  twistPolynomialLinearMap A D ∘ₗ homogeneousSubmoduleCoeff A D

variable (A) in
/-- **The trace** `Hᵈ(ℙᵈ_A, 𝒪(-d-1)) ≅ A`, `d ≥ 1`: the top cohomology of `𝒪(-d-1)` is free of
rank one, with basis the class of the Čech cocycle `x₀⁻¹ ⋯ x_d⁻¹`.

(blueprint: `lem-pc-projective-space-twist-cohomology` (ii),
`lem-pc-projective-space-serre-pairing`) -/
def twistTopTrace {p : ℕ} (hn : Fintype.card n = p + 1 + 1) :
    letI := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A))
      (twist n (Spec (.of A)) (-((p + 1 : ℕ) : ℤ) - 1)) (p + 1)
    (twist n (Spec (.of A)) (-((p + 1 : ℕ) : ℤ) - 1)).H (p + 1) ≃ₗ[A] A :=
  twistHLinearEquivMonomialCechHomology A _ (p + 1) ≪≫ₗ monomialCechTrace n A hn

variable (A) in
/-- **The top cohomology of the twisting sheaves as a dual**: for `d ≥ 1` and `m ≤ -d - 1`,
`Hᵈ(ℙᵈ_A, 𝒪(m)) ≅ Hom_A(A[x₀, …, x_d]_{-m-d-1}, A)`. It is the isomorphism induced by the Serre
pairing and the trace (`twistHTopLinearEquivDual_apply`).

(blueprint: `lem-pc-projective-space-serre-pairing`) -/
def twistHTopLinearEquivDual {p : ℕ} (hn : Fintype.card n = p + 1 + 1) {m : ℤ}
    (hm : m ≤ -((p + 1 : ℕ) : ℤ) - 1) :
    letI := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) (twist n (Spec (.of A)) m) (p + 1)
    (twist n (Spec (.of A)) m).H (p + 1) ≃ₗ[A]
      Module.Dual A (MvPolynomial.homogeneousSubmodule n A (-m - ((p + 1 : ℕ) : ℤ) - 1).toNat) :=
  twistHLinearEquivMonomialCechHomology A m (p + 1) ≪≫ₗ
    monomialCechComplexHomologyTopLinearEquivDual n A m hn hm


/-! ### Global sections of `𝒪(D)` -/

/-- A Laurent polynomial regular on `U_s` is determined by its section over `U_s`. -/
lemma twistLaurentSection_injective {m : ℤ} {s : Set n} (hs : s.Nonempty) {c c' : (n → ℤ) →₀ A}
    (hc : c ∈ Finsupp.supported A A (laurentExponents s m))
    (hc' : c' ∈ Finsupp.supported A A (laurentExponents s m))
    (h : twistLaurentSection A m s c = twistLaurentSection A m s c') : c = c' := by
  have hm : twistMonomialLinearMap A m s (Finsupp.supportedEquivFinsupp _ ⟨c, hc⟩) =
      twistMonomialLinearMap A m s (Finsupp.supportedEquivFinsupp _ ⟨c', hc'⟩) := by
    rw [twistMonomialLinearMap_supportedEquivFinsupp, twistMonomialLinearMap_supportedEquivFinsupp]
    exact h
  exact congrArg Subtype.val ((Finsupp.supportedEquivFinsupp _).injective
    ((bijective_twistMonomialLinearMap hs).1 hm))

/-- Every section of `𝒪(m)` over `U_s` is the section of a Laurent polynomial regular on `U_s`. -/
lemma exists_twistLaurentSection_eq {m : ℤ} {s : Set n} (hs : s.Nonempty)
    (x : Γ(twist n (Spec (.of A)) m, toProjInt n (Spec (.of A)) ⁻¹ᵁ basicOpenInt n s)) :
    ∃ c ∈ Finsupp.supported A A (laurentExponents s m), twistLaurentSection A m s c = x := by
  obtain ⟨g, hg⟩ := (bijective_twistMonomialLinearMap (k := A) (m := m) hs).2 x
  refine ⟨((Finsupp.supportedEquivFinsupp (M := A) (R := A) _).symm g : (n → ℤ) →₀ A),
    ((Finsupp.supportedEquivFinsupp _).symm g).2, ?_⟩
  rw [← hg, ← LinearEquiv.apply_symm_apply (Finsupp.supportedEquivFinsupp (M := A) (R := A) _) g,
    twistMonomialLinearMap_supportedEquivFinsupp, LinearEquiv.symm_apply_apply]
  rfl

variable (n) in
/-- `U_{i} = D₊(xᵢ)`. -/
lemma preimage_basicOpenInt_singleton (S : Scheme.{u}) (i : n) :
    toProjInt n S ⁻¹ᵁ basicOpenInt n {i} = standardOpen n S i :=
  le_antisymm (preimage_basicOpenInt_le_standardOpen S rfl) fun _ hx ↦
    Proj.mem_basicOpen_monomialToNat_indicator.2 fun _ hj ↦ (Set.mem_singleton_iff.1 hj) ▸ hx

/-- **Global sections of `𝒪(m)` are polynomials**: for `m ≥ 0`, every global section of `𝒪(m)`
on `ℙ(n; Spec A)` is the section of a polynomial of degree `m`. Its restrictions to the standard
opens `D₊(xᵢ)` are Laurent polynomials, which agree on the overlaps and hence are a single
polynomial.

(blueprint: `lem-pc-projective-space-twist-cohomology` (i)) -/
lemma exists_twistPolynomialSection_eq [Nonempty n] {m : ℤ} (hm : 0 ≤ m)
    (t : Γ(twist n (Spec (.of A)) m, ⊤)) :
    ∃ c ∈ Finsupp.supported A A (monomialExponents n m), twistPolynomialSection A m c = t := by
  choose G hG hGt using fun i : n ↦ exists_twistLaurentSection_eq (A := A) (m := m)
    (Set.singleton_nonempty i) ((twist n (Spec (.of A)) m).presheaf.map (homOfLE le_top).op t)
  have hsub (i j : n) : ({i} : Set n) ⊆ {i, j} := Set.singleton_subset_iff.2 (Set.mem_insert i _)
  have hsub' (i j : n) : ({j} : Set n) ⊆ {i, j} :=
    Set.singleton_subset_iff.2 (Set.mem_insert_of_mem i rfl)
  have hG' (i j : n) : G i = G j := by
    refine twistLaurentSection_injective (s := {i, j}) ⟨i, Set.mem_insert i _⟩
      (Finsupp.supported_mono (laurentExponents_mono (hsub i j) m) (hG i))
      (Finsupp.supported_mono (laurentExponents_mono (hsub' i j) m) (hG j)) ?_
    rw [← twistLaurentSection_map (hsub i j) (hG i), ← twistLaurentSection_map (hsub' i j) (hG j),
      hGt i, hGt j, presheaf_map_homOfLE_map_homOfLE, presheaf_map_homOfLE_map_homOfLE]
  obtain ⟨i₀⟩ := ‹Nonempty n›
  have hmem : G i₀ ∈ Finsupp.supported A A (monomialExponents n m) := by
    intro e he
    have hl (j : n) : e ∈ laurentExponents {j} m := hG j (by rwa [← hG' i₀ j])
    refine ⟨(hl i₀).1, fun l ↦ ?_⟩
    by_cases h : ∃ j, j ≠ l
    · obtain ⟨j, hj⟩ := h
      exact (hl j).2 l fun h' ↦ hj (Set.mem_singleton_iff.1 h').symm
    · push Not at h
      have hs := (hl l).1
      rw [Fintype.sum_eq_single l fun j hj ↦ absurd (h j) hj] at hs
      exact hs ▸ hm
  refine ⟨G i₀, hmem, TopCat.Sheaf.eq_of_locally_eq'
    ⟨(twist n (Spec (.of A)) m).presheaf, (twist n (Spec (.of A)) m).isSheaf⟩
    (fun i ↦ toProjInt n (Spec (.of A)) ⁻¹ᵁ basicOpenInt n {i}) ⊤ (fun _ ↦ homOfLE le_top)
    ?_ _ _ fun i ↦ ?_⟩
  · simp only [preimage_basicOpenInt_singleton, iSup_standardOpen, le_refl]
  · rw [← hGt i, hG' i₀ i]
    exact twistPolynomialSection_map _ (hG' i₀ i ▸ hmem)

/-- A polynomial is determined by its global section. -/
lemma twistPolynomialSection_injective [Nonempty n] {m : ℤ} {c c' : (n → ℤ) →₀ A}
    (hc : c ∈ Finsupp.supported A A (monomialExponents n m))
    (hc' : c' ∈ Finsupp.supported A A (monomialExponents n m))
    (h : twistPolynomialSection A m c = twistPolynomialSection A m c') : c = c' := by
  obtain ⟨i⟩ := ‹Nonempty n›
  refine twistLaurentSection_injective (Set.singleton_nonempty i)
    (Finsupp.supported_mono (monomialExponents_subset_laurentExponents _) hc)
    (Finsupp.supported_mono (monomialExponents_subset_laurentExponents _) hc') ?_
  rw [← twistPolynomialSection_map _ hc, ← twistPolynomialSection_map _ hc', h]

omit [Fintype n] in
/-- `natCastExponents` is injective. -/
lemma natCastExponents_injective : Function.Injective (natCastExponents n) :=
  fun _ _ h ↦ Finsupp.ext fun i ↦ Int.ofNat_inj.1 (congr_fun h i)

omit [Fintype n] in
/-- The coefficients of a homogeneous polynomial, as a Laurent polynomial. -/
lemma homogeneousSubmoduleCoeff_apply (D : ℕ) (f : MvPolynomial.homogeneousSubmodule n A D) :
    homogeneousSubmoduleCoeff A D f =
      Finsupp.mapDomain (natCastExponents n) (AddMonoidAlgebra.coeff (f : MvPolynomial n A)) :=
  rfl

omit [Fintype n] in
/-- A homogeneous polynomial is determined by its coefficients as a Laurent polynomial. -/
lemma homogeneousSubmoduleCoeff_injective (D : ℕ) :
    Function.Injective (homogeneousSubmoduleCoeff A (n := n) D) := fun f g h ↦ by
  rw [homogeneousSubmoduleCoeff_apply, homogeneousSubmoduleCoeff_apply] at h
  exact Subtype.ext (AddMonoidAlgebra.coeff_injective
    (Finsupp.mapDomain_injective natCastExponents_injective h))

/-- Every family of coefficients supported on the monomials of degree `D` comes from a
homogeneous polynomial of degree `D`. -/
lemma exists_homogeneousSubmoduleCoeff_eq {D : ℕ} {c : (n → ℤ) →₀ A}
    (hc : c ∈ Finsupp.supported A A (monomialExponents n D)) :
    ∃ f, homogeneousSubmoduleCoeff A D f = c := by
  have hrange : ↑c.support ⊆ Set.range (natCastExponents n) := fun e he ↦
    ⟨Finsupp.equivFunOnFinite.symm fun i ↦ (e i).toNat,
      funext fun i ↦ Int.toNat_of_nonneg ((hc he).2 i)⟩
  let G := Finsupp.comapDomain (natCastExponents n) c natCastExponents_injective.injOn
  refine ⟨⟨AddMonoidAlgebra.ofCoeff G, fun s hs ↦ ?_⟩, ?_⟩
  · have he : natCastExponents n s ∈ c.support := Finsupp.mem_support_iff.2 hs
    have hsum : ∑ i, ((s i : ℕ) : ℤ) = D := (hc he).1
    have hd : s.degree = D := by
      rw [Finsupp.degree_eq_sum]
      exact_mod_cast hsum
    rwa [Finsupp.degree_eq_weight_one] at hd
  · rw [homogeneousSubmoduleCoeff_apply]
    exact Finsupp.mapDomain_comapDomain _ natCastExponents_injective c hrange

/-- **`H⁰(ℙⁿ_A, 𝒪(D)) ≅ A[x₀, …, xₙ]_D`**: the global sections of `𝒪(D)`, `D ≥ 0`, are the
homogeneous polynomials of degree `D`.

(blueprint: `lem-pc-projective-space-twist-cohomology` (i)) -/
theorem bijective_homogeneousSubmoduleToTwist [Nonempty n] (D : ℕ) :
    Function.Bijective (homogeneousSubmoduleToTwist (n := n) A D) := by
  refine ⟨fun f g h ↦ homogeneousSubmoduleCoeff_injective D
    (twistPolynomialSection_injective (coeff_toLaurent_mem f.2) (coeff_toLaurent_mem g.2) h),
    fun t ↦ ?_⟩
  obtain ⟨c, hc, rfl⟩ := exists_twistPolynomialSection_eq (Int.natCast_nonneg D) t
  obtain ⟨f, rfl⟩ := exists_homogeneousSubmoduleCoeff_eq hc
  exact ⟨f, rfl⟩

variable (A) in
/-- **`H⁰(ℙⁿ_A, 𝒪(D)) ≅ A[x₀, …, xₙ]_D`**, as `A`-modules.

(blueprint: `lem-pc-projective-space-twist-cohomology` (i)) -/
def homogeneousSubmoduleLinearEquivTwist [Nonempty n] (D : ℕ) :
    MvPolynomial.homogeneousSubmodule n A D ≃ₗ[A]
      (ModuleCat.restrictScalars (structureRingHom (n := n) A)).obj
        ((twist n (Spec (.of A)) D).presheafModuleCat.obj (op ⊤)) :=
  LinearEquiv.ofBijective _ (bijective_homogeneousSubmoduleToTwist D)

variable (A) in
/-- **The Serre pairing with values in `A`**: for `d ≥ 1`, `m ≤ -d - 1` and `D = -m - d - 1`,
the pairing `H⁰(ℙᵈ_A, 𝒪(D)) × Hᵈ(ℙᵈ_A, 𝒪(m)) → Hᵈ(ℙᵈ_A, 𝒪(-d-1)) ≅ A`, `(t, x) ↦ tr (t x)`,
of the Serre pairing `twistMulPairing` with the trace `twistTopTrace`. It is perfect
(`isPerfPair_twistSerrePairing`).

(blueprint: `lem-pc-projective-space-serre-pairing`) -/
def twistSerrePairing {p : ℕ} (hn : Fintype.card n = p + 1 + 1) {m : ℤ}
    (hm : m ≤ -((p + 1 : ℕ) : ℤ) - 1) :
    letI := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) (twist n (Spec (.of A)) m) (p + 1)
    (ModuleCat.restrictScalars (structureRingHom (n := n) A)).obj
        ((twist n (Spec (.of A)) (-m - ((p + 1 : ℕ) : ℤ) - 1).toNat).presheafModuleCat.obj
          (op ⊤)) →ₗ[A] (twist n (Spec (.of A)) m).H (p + 1) →ₗ[A] A :=
  letI := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) (twist n (Spec (.of A)) m) (p + 1)
  letI := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A))
    (twist n (Spec (.of A)) (-((p + 1 : ℕ) : ℤ) - 1)) (p + 1)
  (twistMulPairing A (monomialCechPairing_aux hm) (p + 1)).compr₂ (twistTopTrace A hn).toLinearMap


end Pairing
section Canonical

variable (A) in
/-- **`H⁰(ℙ(n; Spec A), 𝒪(D)) ≅ A[xᵢ]_D`**, as `A`-modules, stated on the cohomology `.H 0`: a
class of `H⁰` is a global section of `𝒪(D)` (`H.zeroLinearEquiv`), which is the section of a
unique homogeneous polynomial of degree `D` (`homogeneousSubmoduleLinearEquivTwist`).

(blueprint: `lem-pc-projective-space-twist-cohomology` (i), `det-thm-picard-pn`) -/
def twistHZeroLinearEquiv [Nonempty n] (D : ℕ) :
    letI := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) (twist n (Spec (.of A)) D) 0
    (twist n (Spec (.of A)) D).H 0 ≃ₗ[A] MvPolynomial.homogeneousSubmodule n A D :=
  letI := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) (twist n (Spec (.of A)) D) 0
  ({ (H.zeroLinearEquiv (twist n (Spec (.of A)) D)).toAddEquiv with
      map_smul' c x := by
        refine ((H.zeroLinearEquiv _).map_smul (structureRingHom A c) x).trans ?_
        change _ = (ℙ(n; Spec (.of A))).presheaf.map
            (homOfLE le_top : (⊤ : (ℙ(n; Spec (.of A))).Opens) ⟶ ⊤).op (structureRingHom A c) •
          H.zeroLinearEquiv (twist n (Spec (.of A)) D) x
        rw [Scheme.presheaf_map_id_apply] } :
    (twist n (Spec (.of A)) D).H 0 ≃ₗ[A]
      (ModuleCat.restrictScalars (structureRingHom (n := n) A)).obj
        ((twist n (Spec (.of A)) D).presheafModuleCat.obj (op ⊤))) ≪≫ₗ
    (homogeneousSubmoduleLinearEquivTwist A D).symm


variable (A) in
/-- **The monomial basis of the top cohomology of `𝒪(m)`**: with `d + 1` homogeneous
coordinates ordered by `E : Fin (d + 1) ≃ n`, `Hᵈ(ℙ(n; Spec A), 𝒪(m))` is free on the strictly
negative exponent vectors `e` of sum `m`, the basis vector of `e` being the class of the Čech
cocycle `xᵉ` on `U_{E 0} ∩ ⋯ ∩ U_{E d}` (for `d = 0` this requires `m < 0`). It is the
monomial basis of the monomial Čech complex transported along the canonical Leray isomorphism
`twistHLinearEquivMonomialCechHomology`; the ordering `E` only fixes the signs.

(blueprint: `lem-pc-projective-space-twist-cohomology` (ii)) -/
def twistHTopBasis {d : ℕ} (hn : Fintype.card n = d + 1) (E : Fin (d + 1) ≃ n) {m : ℤ}
    (hm : d ≠ 0 ∨ m < 0) :
    letI := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) (twist n (Spec (.of A)) m) d
    Module.Basis (negativeExponents n m) A ((twist n (Spec (.of A)) m).H d) :=
  letI := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) (twist n (Spec (.of A)) m) d
  .ofRepr (twistHLinearEquivMonomialCechHomology A m d ≪≫ₗ
    monomialCechComplexHomologyTopLinearEquiv n A m hn E hm)


end Canonical

end AlgebraicGeometry.ProjectiveSpace
