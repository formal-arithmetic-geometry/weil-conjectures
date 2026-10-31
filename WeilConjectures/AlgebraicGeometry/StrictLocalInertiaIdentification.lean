/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.InertiaStrictHenselization
public import WeilConjectures.RingTheory.StrictHenselizationPresentationIn
public import WeilConjectures.RingTheory.StrictHenselizationTriples
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import WeilConjectures.AlgebraicGeometry.StrictLocalInertiaRingCore
import WeilConjectures.AlgebraicGeometry.StrictLocalInertiaSchemeCore

/-!
# Strict-local inertia identification

Source: Stacks Project, pione.tex, Tag 0BSW (lemma-identify-inertia), setup before
`equation-inertia-diagram-pione` and the scheme paragraph after its proof.
(blueprint: lem-dl-a1-strict-local-inertia-identification).

## Main statements

* `strictLocalInertiaIdentification` states the strict-local fraction-field and inertia
  identification, including conjugacy for every embedding and the scheme-local form.
-/

@[expose] public section

set_option autoImplicit false

universe u v w z t

open CategoryTheory AlgebraicGeometry

private theorem embedding_fixingSubgroup_conjugacy
    {F E Ω : Type u} [Field F] [Field E] [Field Ω]
    [Algebra F E] [Algebra F Ω] [Normal F Ω]
    (e e' : E →ₐ[F] Ω) :
    ∃ g : Ω ≃ₐ[F] Ω, ∀ h : Ω ≃ₐ[F] Ω,
      h ∈ e'.fieldRange.fixingSubgroup ↔
        g⁻¹ * h * g ∈ e.fieldRange.fixingSubgroup := by
  classical
  let : Algebra E Ω := e.toRingHom.toAlgebra
  let : IsScalarTower F E Ω :=
    IsScalarTower.of_algebraMap_eq (fun r ↦ (e.commutes r).symm)
  let g : Ω ≃ₐ[F] Ω := AlgEquiv.ofBijective (e'.liftNormal Ω)
    (AlgHom.normal_bijective F Ω Ω _)
  have hg (x : E) : g (e x) = e' x := e'.liftNormal_commutes Ω x
  have mem (f : E →ₐ[F] Ω) (σ : Ω ≃ₐ[F] Ω) :
      σ ∈ f.fieldRange.fixingSubgroup ↔ ∀ x : E, σ (f x) = f x := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x
      exact h (f x) ⟨x, rfl⟩
    · intro h y hy
      obtain ⟨x, rfl⟩ := hy
      exact h x
  refine ⟨g, fun h ↦ ?_⟩
  rw [mem, mem]
  constructor
  · intro hh x
    change g.symm (h (g (e x))) = e x
    apply g.injective
    simpa only [AlgEquiv.apply_symm_apply, hg] using hh x
  · intro hh x
    have hx := congrArg g (hh x)
    change g (g.symm (h (g (e x)))) = g (e x) at hx
    simpa only [AlgEquiv.apply_symm_apply, hg] using hx

-- Retain the named proof binders of the universal scheme conclusion verbatim.
set_option linter.unusedVariables false in
/-- The fraction field of a strict henselization is the fixed field of the inertia subgroup
of the corresponding prime in the separable normalization, and all choices of embedding are
conjugate.

Source: Stacks Project, pione.tex, Tag 0BSW, lemma-identify-inertia, its setup and the
scheme paragraph following the proof (blueprint: lem-dl-a1-strict-local-inertia-identification).

Proof (Steps 1-4 of the node; Step 5 extracts the scheme corollary below):
1. The ring-core theorem `strictLocalInertiaIdentificationRingCore` (Steps 1-7 of the
   Stacks argument) gives a local `A`-map `u : C → B_Q` and an `F`-embedding `e : E → Ω`
   compatible on `C` with `Ω^{I_Q} = e(E)`. Then `u` is injective, since `C → E` and `e` are,
   and `E / F` is separable, being embedded by `e` in the separable extension `Ω / F`.
2. The inertia group is closed in the Krull topology, so `I_Q` is the fixing subgroup of its
   fixed field (`Ideal.fixingSubgroup_fixedField_inertia`); with Step 1, `I_Q` is the fixing
   subgroup of `e(E)`.
3. For another `F`-embedding `e'`, `Ω / F` is normal, so `e'` composed with the inverse of `e`
   extends to an `F`-automorphism `g` of `Ω` with `g ∘ e = e'` (`AlgHom.liftNormal`). An
   automorphism `h` fixes `e'(E)` if and only if `g⁻¹ h g` fixes `e(E)`, by evaluation at each
   `e(x)`; with Step 2 this is the conjugacy with `I_Q`.
4. The scheme clause is the scheme-core theorem `strictLocalInertiaIdentificationSchemeCore`
   (affine integral-closure localization at the stalk, Steps 9-10 of the Stacks argument).
-/
theorem strictLocalInertiaIdentification
    (A F K C E Ω : Type u)
    [CommRing A] [IsLocalRing A] [Field F] [Field K] [CommRing C] [Field E] [Field Ω]
    [Algebra A F] [IsFractionRing A F]
    [Algebra (IsLocalRing.ResidueField A) K]
    [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [Algebra A C] [Algebra A E] [Algebra C E] [IsFractionRing C E]
    [Algebra F E] [IsScalarTower A C E] [IsScalarTower A F E]
    [Algebra A Ω] [Algebra F Ω] [IsScalarTower A F Ω]
    [SMulCommClass (Ω ≃ₐ[F] Ω) A Ω] [IsSepClosure F Ω]
    (hC : Algebra.IsStrictHenselization A K C)
    (hA : IsDomain A ∧ IsIntegrallyClosed A)
    (hCnormal : IsDomain C ∧ IsIntegrallyClosed C)
    (hAC : Function.Injective (algebraMap A C))
    (Q : Ideal (integralClosure A Ω)) [Q.IsMaximal]
    (hQ : Q.comap (algebraMap A (integralClosure A Ω)) = IsLocalRing.maximalIdeal A) :
    Algebra.IsSeparable F E ∧ Nonempty (E →ₐ[F] Ω) ∧
      (∃ u : C →ₐ[A] Localization.AtPrime Q,
        Function.Injective u ∧
        ∃ e : E →ₐ[F] Ω,
          e.toRingHom.comp (algebraMap C E) =
            (Ideal.atPrimeToField Q).comp u.toRingHom ∧
          IntermediateField.fixedField (Q.inertia (Ω ≃ₐ[F] Ω)) = e.fieldRange ∧
          Q.inertia (Ω ≃ₐ[F] Ω) = e.fieldRange.fixingSubgroup ∧
          ∀ e' : E →ₐ[F] Ω, ∃ g : Ω ≃ₐ[F] Ω,
            ∀ h : Ω ≃ₐ[F] Ω,
              h ∈ e'.fieldRange.fixingSubgroup ↔
                g⁻¹ * h * g ∈ Q.inertia (Ω ≃ₐ[F] Ω)) ∧
      ∀ (X : Scheme.{u}) [IsIntegral X]
          (hnormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
          (x : X) (K' C' : Type (max u w)) [Field K'] [CommRing C']
          [Algebra (IsLocalRing.ResidueField (X.presheaf.stalk x)) K']
          [IsSepClosure (IsLocalRing.ResidueField (X.presheaf.stalk x)) K']
          [Algebra (X.presheaf.stalk x) K']
          [IsScalarTower (X.presheaf.stalk x)
            (IsLocalRing.ResidueField (X.presheaf.stalk x)) K']
          [Algebra (X.presheaf.stalk x) C']
          (hC' : Algebra.StrictHenselizationPresentationIn.{u, w}
            (X.presheaf.stalk x) K' C')
          (E' : Type z) [Field E'] [Algebra C' E'] [IsFractionRing C' E']
          [Algebra (X.presheaf.stalk x) E']
          [IsScalarTower (X.presheaf.stalk x) C' E']
          [Algebra X.functionField E']
          [IsScalarTower (X.presheaf.stalk x) X.functionField E']
          [Algebra X.functionField Ω] [IsSepClosure X.functionField Ω]
          (e' : E' →ₐ[X.functionField] Ω),
          ∀ (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
            [Algebra Γ(X, U) Ω] [IsScalarTower Γ(X, U) X.functionField Ω]
            (r : PrimeSpectrum (integralClosure Γ(X, U) Ω)),
            (Spec.map (CommRingCat.ofHom
              (algebraMap Γ(X, U) (integralClosure Γ(X, U) Ω))) ≫ hU.fromSpec) r = x →
            ∃ g : Ω ≃ₐ[X.functionField] Ω, ∀ h : Ω ≃ₐ[X.functionField] Ω,
              h ∈ r.asIdeal.inertia (Ω ≃ₐ[X.functionField] Ω) ↔
                g⁻¹ * h * g ∈ e'.fieldRange.fixingSubgroup := by
  obtain ⟨u, e, hcompat, hfixed⟩ :=
    strictLocalInertiaIdentificationRingCore A F K C E Ω hC hA hCnormal hAC Q hQ
  have hu : Function.Injective u := by
    let : IsDomain C := hCnormal.1
    intro a b hab
    apply IsFractionRing.injective C E
    apply e.injective
    exact (RingHom.congr_fun hcompat a).trans
      ((congrArg (Ideal.atPrimeToField Q) hab).trans (RingHom.congr_fun hcompat b).symm)
  have hsep : Algebra.IsSeparable F E := Algebra.IsSeparable.of_algHom F Ω e
  have hgroup : Q.inertia (Ω ≃ₐ[F] Ω) = e.fieldRange.fixingSubgroup := by
    rw [← hfixed]
    exact (Ideal.fixingSubgroup_fixedField_inertia Q).symm
  refine ⟨hsep, ⟨e⟩, ⟨u, hu, e, hcompat, hfixed, hgroup, ?_⟩, ?_⟩
  · intro e'
    obtain ⟨g, hg⟩ := embedding_fixingSubgroup_conjugacy e e'
    exact ⟨g, fun h ↦ (hg h).trans (by rw [hgroup])⟩
  · intro X _ hnormal x K' C' _ _ _ _ _ _ _ hC'
    exact strictLocalInertiaIdentificationSchemeCore Ω X hnormal x K' C' hC'

private theorem integralClosure_maximal_comap_field
    (Ω : Type u) [Field Ω] (Q : Ideal (integralClosure Ω Ω)) [Q.IsPrime] :
    Q.comap (algebraMap Ω (integralClosure Ω Ω)) = IsLocalRing.maximalIdeal Ω := by
  rw [IsLocalRing.maximalIdeal_eq_bot]
  exact Ideal.eq_bot_of_prime _

/-- For every point of the separable normalization of a normal integral scheme, inertia is
conjugate to the fixing subgroup for any embedding of a strict-local fraction field.
A point of the normalization is represented in an arbitrary affine normalization chart
by `r`; this includes nonclosed points, and its residue field is `Frac(B / r)`.
Source: Stacks Project, pione.tex, Tag 0BSW, scheme setup following lemma-identify-inertia
(blueprint: lem-dl-a1-strict-local-inertia-identification).

Proof (step 5 of the node): this is the scheme conjunct of `strictLocalInertiaIdentification`,
which is the scheme-core theorem `strictLocalInertiaIdentificationSchemeCore` (integral-closure
localization identifies the chart prime with a maximal prime of the integral closure of the
stalk, with the same residue field and inertia; the stalk/function-field identification and
normality of etale local colimits apply the ring core to every strict henselization). To
extract it, instantiate
the independent ring parameters by the separably closed field `Ω` itself: the inverse of the
residue map gives the residue-field algebra, the identity pointing is terminal in the pointed
etale diagram so its pointing cocone is a colimit, and a maximal ideal of the integral closure
of `Ω` in itself contracts to the zero ideal of `Ω`. No residue perfection or Noetherianity is
used.
-/
theorem AlgebraicGeometry.Scheme.strictLocalInertiaIdentification
    (X : Scheme.{u}) [IsIntegral X]
    (_hnormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (Ω : Type u) [Field Ω] [Algebra X.functionField Ω] [IsSepClosure X.functionField Ω]
    (x : X) (K C : Type (max u w))
    [Field K] [Algebra (IsLocalRing.ResidueField (X.presheaf.stalk x)) K]
    [IsSepClosure (IsLocalRing.ResidueField (X.presheaf.stalk x)) K]
    [Algebra (X.presheaf.stalk x) K]
    [IsScalarTower (X.presheaf.stalk x) (IsLocalRing.ResidueField (X.presheaf.stalk x)) K]
    [CommRing C] [Algebra (X.presheaf.stalk x) C]
    (_P : Algebra.StrictHenselizationPresentationIn.{u, w} (X.presheaf.stalk x) K C)
    (E : Type z) [Field E] [Algebra C E] [IsFractionRing C E]
    [Algebra (X.presheaf.stalk x) E] [IsScalarTower (X.presheaf.stalk x) C E]
    [Algebra X.functionField E] [IsScalarTower (X.presheaf.stalk x) X.functionField E]
    (e : E →ₐ[X.functionField] Ω) :
    ∀ (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
      [Algebra Γ(X, U) Ω] [IsScalarTower Γ(X, U) X.functionField Ω]
      (r : PrimeSpectrum (integralClosure Γ(X, U) Ω)),
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (integralClosure Γ(X, U) Ω))) ≫
        hU.fromSpec) r = x →
      ∃ g : Ω ≃ₐ[X.functionField] Ω, ∀ h : Ω ≃ₐ[X.functionField] Ω,
        h ∈ r.asIdeal.inertia (Ω ≃ₐ[X.functionField] Ω) ↔
          g⁻¹ * h * g ∈ e.fieldRange.fixingSubgroup := by
  classical
  -- A separably closed field supplies the auxiliary ring inputs of the bundled theorem.
  let r : IsLocalRing.ResidueField Ω →+* Ω :=
    IsLocalRing.ResidueField.lift (RingHom.id Ω)
  let : Algebra (IsLocalRing.ResidueField Ω) Ω := r.toAlgebra
  let : IsScalarTower Ω (IsLocalRing.ResidueField Ω) Ω :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsSepClosed Ω := IsSepClosure.sep_closed X.functionField
  let : Algebra.IsSeparable (IsLocalRing.ResidueField Ω) Ω :=
    ⟨fun a ↦ by
      change IsSeparable (IsLocalRing.ResidueField Ω)
        (algebraMap (IsLocalRing.ResidueField Ω) Ω (IsLocalRing.residue Ω a))
      exact isSeparable_algebraMap _⟩
  let : IsSepClosure (IsLocalRing.ResidueField Ω) Ω := ⟨inferInstance, inferInstance⟩
  -- The identity pointing is terminal, so its forgetful diagram has colimit Ω.
  let P : ObjectProperty (Over (CommAlgCat.of Ω Ω)) :=
    fun S ↦ Algebra.Etale Ω S.left
  let t : P.FullSubcategory := ⟨Over.mk (𝟙 (CommAlgCat.of Ω Ω)), by
    change Algebra.Etale Ω Ω
    infer_instance⟩
  let c := Algebra.strictHenselizationPointingCocone Ω Ω
  have hc : CategoryTheory.Limits.IsColimit c :=
    { desc := fun s ↦ s.ι.app t
      fac := by
        intro s S
        let f : S ⟶ t := ObjectProperty.homMk (Over.homMk S.obj.hom (by simp [t]))
        exact s.w f
      uniq := by
        intro s m hm
        have h := hm t
        change (𝟙 (CommAlgCat.of Ω Ω)) ≫ m = s.ι.app t at h
        simpa only [Category.id_comp] using h }
  have hstrict : Algebra.IsStrictHenselization Ω Ω Ω :=
    ⟨c, ⟨hc⟩, ⟨Iso.refl _⟩⟩
  obtain ⟨Q, hQ⟩ := Ideal.exists_maximal (integralClosure Ω Ω)
  let := hQ
  have hcontract := integralClosure_maximal_comap_field Ω Q
  exact (_root_.strictLocalInertiaIdentification Ω Ω Ω Ω Ω Ω hstrict
    ⟨inferInstance, inferInstance⟩ ⟨inferInstance, inferInstance⟩
    (Function.injective_id) Q hcontract).2.2.2 X _hnormal x K C _P E e
