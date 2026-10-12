/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.LerayNatural
public import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveSpaceTwist
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistMul

/-!
# The Serre pairing on projective space

TODO
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

lemma twistLaurentMonomial_of_mem {m : ℤ} {s : Set n} {e : n → ℤ}
    (h : e ∈ laurentExponents s m) :
    twistLaurentMonomial A m s e = twistMonomialSection (Spec (.of A)) s ⟨e, h⟩ :=
  dif_pos h

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

lemma twistLaurentSection_single (m : ℤ) (s : Set n) (e : n → ℤ) (r : A) :
    twistLaurentSection A m s (Finsupp.single e r) =
      structureRingHomOpen A (toProjInt n (Spec (.of A)) ⁻¹ᵁ basicOpenInt n s) r •
        twistLaurentMonomial A m s e := by
  rw [twistLaurentSection, twistLaurentLinearMap, Finsupp.linearCombination_single]
  rfl

lemma twistLaurentSection_smul (m : ℤ) (s : Set n) (r : A) (c : (n → ℤ) →₀ A) :
    twistLaurentSection A m s (r • c) =
      structureRingHomOpen A (toProjInt n (Spec (.of A)) ⁻¹ᵁ basicOpenInt n s) r •
        twistLaurentSection A m s c := by
  rw [twistLaurentSection, LinearMap.map_smul]
  rfl

lemma twistLaurentSection_add (m : ℤ) (s : Set n) (c c' : (n → ℤ) →₀ A) :
    twistLaurentSection A m s (c + c') =
      twistLaurentSection A m s c + twistLaurentSection A m s c' :=
  map_add _ _ _

lemma twistLaurentSection_zero (m : ℤ) (s : Set n) :
    twistLaurentSection A m s 0 = 0 :=
  map_zero _

/-- **Products of Laurent polynomial sections**: over `U_s` (`s` nonempty), the canonical
isomorphism `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)` sends `F ⊗ G` to `F G`, for Laurent polynomials `F` and
`G` of degrees `a` and `b` regular on `U_s`.

(blueprint: `lem-pc-twist-tensor`, `lem-pc-projective-space-serre-pairing`) -/
lemma twistTensorIso_hom_app_twistLaurentSection {s : Set n} (hs : s.Nonempty) {a b : ℤ}
    {x y : (n → ℤ) →₀ A} (hx : x ∈ Finsupp.supported A A (laurentExponents s a))
    (hy : y ∈ Finsupp.supported A A (laurentExponents s b)) :
    (twistTensorIso n (Spec (.of A)) a b).hom.app
        (toProjInt n (Spec (.of A)) ⁻¹ᵁ basicOpenInt n s)
        (tmulSection (twistLaurentSection A a s x) (twistLaurentSection A b s y)) =
      twistLaurentSection A (a + b) s
        (AddMonoidAlgebra.ofCoeff x * AddMonoidAlgebra.ofCoeff y).coeff := by
  rw [Finsupp.supported_eq_span_single] at hx hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, he, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨e', he', rfl⟩ := hy
      rw [AddMonoidAlgebra.ofCoeff_single, AddMonoidAlgebra.ofCoeff_single,
        AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.coeff_single,
        twistLaurentSection_single, twistLaurentSection_single,
        twistLaurentSection_single, twistLaurentMonomial_of_mem he,
        twistLaurentMonomial_of_mem he',
        twistLaurentMonomial_of_mem (e := e + e') (Proj.addExponent a b ⟨e, he⟩ ⟨e', he'⟩).2,
        smul_tmulSection, tmulSection_smul, Hom.app_smul, Hom.app_smul,
        twistTensorIso_hom_app_twistMonomialSection _ hs, mul_one, map_one, one_smul, one_smul,
        one_smul]
      rfl
    | zero =>
      rw [twistLaurentSection_zero, tmulSection_zero, map_zero, AddMonoidAlgebra.ofCoeff_zero,
        mul_zero, AddMonoidAlgebra.coeff_zero, twistLaurentSection_zero]
    | add y y' _ _ h h' =>
      rw [twistLaurentSection_add, tmulSection_add, map_add, h, h',
        AddMonoidAlgebra.ofCoeff_add, mul_add, AddMonoidAlgebra.coeff_add,
        twistLaurentSection_add]
    | smul r y _ h =>
      rw [twistLaurentSection_smul, tmulSection_smul, Hom.app_smul, h,
        AddMonoidAlgebra.ofCoeff_smul, mul_smul_comm, AddMonoidAlgebra.coeff_smul,
        twistLaurentSection_smul]
  | zero =>
    rw [twistLaurentSection_zero, zero_tmulSection, map_zero, AddMonoidAlgebra.ofCoeff_zero,
      zero_mul, AddMonoidAlgebra.coeff_zero, twistLaurentSection_zero]
  | add x x' _ _ h h' =>
    rw [twistLaurentSection_add, add_tmulSection, map_add, h, h', AddMonoidAlgebra.ofCoeff_add,
      add_mul, AddMonoidAlgebra.coeff_add, twistLaurentSection_add]
  | smul r x _ h =>
    rw [twistLaurentSection_smul, smul_tmulSection, Hom.app_smul, h,
      AddMonoidAlgebra.ofCoeff_smul, smul_mul_assoc, AddMonoidAlgebra.coeff_smul,
      twistLaurentSection_smul]

end LaurentSection

end AlgebraicGeometry.ProjectiveSpace
