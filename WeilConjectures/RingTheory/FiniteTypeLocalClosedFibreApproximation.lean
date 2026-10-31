/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.PrincipalIdealDomain

/-! # Finite-presentation local approximation preserving the closed fibre

Source: Stacks Project, Tag 05UV, proof before applying Tag 00R7
(blueprint: lem-sfb-finite-type-local-closed-fibre-approximation).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

/-- An essentially finite type local algebra is a surjective image of a local algebra
which is a localization of a finitely presented algebra, with the same closed fibre.

Source: Stacks Project, Tag 05UV, proof before applying Tag 00R7
(blueprint: lem-sfb-finite-type-local-closed-fibre-approximation).

Proof: Choose a finite set σ in B such that every b in B has a unit denominator y
with y and by in R[σ]. Evaluate Q = R[X_i : i ∈ σ] in B and let q be the inverse
image of its maximal ideal. The resulting map v : A = Q_q → B is surjective:
lift y and by to Q, and take their fraction. Since v is a surjection from a local
ring it is local. The locality assertions for the final approximation follow below.

The algebra A is essentially of finite type over R. Its closed fibre F is
therefore essentially of finite type over the field R/m_R, hence Noetherian.
Put J = ker v. The localization ideal correspondence shows that J is the
extension of the kernel of Q → B. Consequently its image in F is generated
by the images of polynomial kernel elements. Choose a finite subset of those
polynomials generating the same ideal in F. Let K be their ideal in Q and L
its extension to A. Then K is finitely generated, L ≤ J, and equality of their
images in F gives L + m_R A = J + m_R A.

Take T = A/L and P = Q/K. The map v factors through a surjection f : T → B.
The quotient T is nonzero (it maps to B) and local, f is local, and locality of
R → B implies locality of R → T. Finite generation of K makes P finitely
presented. The quotient-localization instance identifies T with the localization
of P at the image of q's complement, compatibly with R.

Finally f maps m_R T onto m_R B. Pull back these ideals along A → T and
A → B: their inverse images are respectively L + m_R A and J + m_R A.
Their equality and surjectivity of A → T show f⁻¹(m_R B) = m_R T. The induced
quotient map is thus injective as well as surjective. The associated ring
isomorphism sends each class [t] to [f(t)] by construction. -/
theorem exists_finitePresentation_local_approximation_closedFibre
    (R : Type u) (B : Type v) [CommRing R] [CommRing B]
    [IsLocalRing R] [IsLocalRing B] [Algebra R B]
    [IsLocalHom (algebraMap R B)] [EssFiniteType R B] :
    ∃ (T : Type (max u v)) (_ : CommRing T) (_ : IsLocalRing T) (_ : Algebra R T),
      ∃ f : T →ₐ[R] B,
        IsLocalHom (algebraMap R T) ∧ IsLocalHom f.toRingHom ∧
        Function.Surjective f ∧
        (∃ (P : Type (max u v)) (_ : CommRing P) (_ : Algebra R P),
          FinitePresentation R P ∧ ∃ W : Submonoid P, Nonempty (T ≃ₐ[R] Localization W)) ∧
        ∃ e :
          (T ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R T)) ≃+*
            (B ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R B)),
          ∀ t : T,
            e (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R T)) t) =
              Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R B)) (f t) := by
  classical
  obtain ⟨σ, hσ⟩ := (essFiniteType_iff R B).mp inferInstance
  let Q := MvPolynomial σ R
  let h : Q →ₐ[R] B := MvPolynomial.aeval (fun x : σ => (x : B))
  have hrange : h.range = adjoin R (σ : Set B) := by
    exact (Algebra.adjoin_eq_range R (σ : Set B)).symm
  let q : Ideal Q := (IsLocalRing.maximalIdeal B).comap h.toRingHom
  have : q.IsPrime := Ideal.comap_isPrime _ _
  let A := Localization.AtPrime q
  have hunits : ∀ s : q.primeCompl, IsUnit (h s) := by
    intro s
    exact not_not.mp s.property
  let v : A →ₐ[R] B := IsLocalization.liftAlgHom hunits
  have hvmap (x : Q) : v (algebraMap Q A x) = h x := by
    exact IsLocalization.lift_eq hunits x
  have hvsurj : Function.Surjective v := by
    intro b
    obtain ⟨y, hy, hyunit, hby⟩ := hσ b
    rw [← hrange] at hy hby
    obtain ⟨s, hs⟩ := hy
    obtain ⟨p, hp⟩ := hby
    change h s = y at hs
    change h p = b * y at hp
    have hsunit : s ∈ q.primeCompl := by
      change ¬ ¬ IsUnit (h s)
      rw [hs]
      exact not_not.mpr hyunit
    refine ⟨IsLocalization.mk' A p ⟨s, hsunit⟩, ?_⟩
    apply (IsLocalization.lift_mk'_spec hunits p b ⟨s, hsunit⟩).mpr
    change h p = h s * b
    rw [hs, hp, mul_comm]
  let m : Ideal A := (IsLocalRing.maximalIdeal R).map (algebraMap R A)
  let F := A ⧸ m
  have : EssFiniteType R A := inferInstance
  let : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  have : IsNoetherianRing F := EssFiniteType.isNoetherianRing
    (R ⧸ IsLocalRing.maximalIdeal R) F
  let J : Ideal A := RingHom.ker v.toRingHom
  have hJ : (RingHom.ker h.toRingHom).map (algebraMap Q A) = J := by
    have hc : J.comap (algebraMap Q A) = RingHom.ker h.toRingHom := by
      ext x
      change v (algebraMap Q A x) = 0 ↔ h x = 0
      rw [hvmap]
    rw [← hc]
    exact IsLocalization.map_under q.primeCompl A J
  let g : Q →+* F := (Ideal.Quotient.mk m).comp (algebraMap Q A)
  have hfg : ((RingHom.ker h.toRingHom).map g).FG := Ideal.fg_of_isNoetherianRing _
  obtain ⟨t, ht, hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset
      (g '' (RingHom.ker h.toRingHom : Set Q))).mp hfg
  have hlift : ∃ s ⊆ (RingHom.ker h.toRingHom : Set Q), s.Finite ∧
      Ideal.span (g '' s) = (RingHom.ker h.toRingHom).map g := by
    apply (Set.exists_subset_image_finite_and (f := g)
      (p := fun t => Ideal.span t = (RingHom.ker h.toRingHom).map g)).mp
    exact ⟨t, ht, t.finite_toSet, hspan.symm⟩
  obtain ⟨s, hs, hsfinite, hsmap⟩ := hlift
  let K : Ideal Q := Ideal.span s
  have hKfg : K.FG := ⟨hsfinite.toFinset, by simp [K]⟩
  have hKker : K ≤ RingHom.ker h.toRingHom := Ideal.span_le.mpr hs
  let L : Ideal A := K.map (algebraMap Q A)
  have hLJ : L ≤ J := hJ ▸ Ideal.map_mono hKker
  have hmaps : L.map (Ideal.Quotient.mk m) = J.map (Ideal.Quotient.mk m) := by
    change (K.map (algebraMap Q A)).map (Ideal.Quotient.mk m) = _
    rw [Ideal.map_map, ← hJ, Ideal.map_map]
    exact (Ideal.map_span g s).trans hsmap
  have hsup : L ⊔ m = J ⊔ m := by
    have he := congrArg (Ideal.comap (Ideal.Quotient.mk m)) hmaps
    simpa only [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] using he
  let T := A ⧸ L
  let f : T →ₐ[R] B := Ideal.Quotient.liftₐ L v (fun x hx => hLJ hx)
  have hfsurj : Function.Surjective f :=
    Ideal.Quotient.lift_surjective_of_surjective L (fun x hx => hLJ hx) hvsurj
  have : Nontrivial T := f.toRingHom.domain_nontrivial
  have : IsLocalRing T :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk L) Ideal.Quotient.mk_surjective
  have : IsLocalHom f.toRingHom := hfsurj.isLocalHom
  have : IsLocalHom (algebraMap R T) := by
    have : IsLocalHom (f.toRingHom.comp (algebraMap R T)) := by
      have he : f.toRingHom.comp (algebraMap R T) = algebraMap R B := by
        ext r
        exact f.commutes r
      rw [he]
      infer_instance
    exact isLocalHom_of_comp (algebraMap R T) f.toRingHom
  refine ⟨T, inferInstance, inferInstance, inferInstance, f,
    inferInstance, inferInstance, hfsurj, ?_, ?_⟩
  · let P := Q ⧸ K
    have : FinitePresentation R P := FinitePresentation.quotient hKfg
    let W := Algebra.algebraMapSubmonoid P q.primeCompl
    have : IsLocalization W T := inferInstance
    have : IsScalarTower R P T := IsScalarTower.of_algebraMap_eq fun r => by
      change algebraMap Q T (algebraMap R Q r) =
        algebraMap P T (algebraMap Q P (algebraMap R Q r))
      exact IsScalarTower.algebraMap_apply Q P T _
    exact ⟨P, inferInstance, inferInstance, inferInstance, W,
      ⟨(IsLocalization.algEquiv W T (Localization W)).restrictScalars R⟩⟩
  · let mT := (IsLocalRing.maximalIdeal R).map (algebraMap R T)
    let mB := (IsLocalRing.maximalIdeal R).map (algebraMap R B)
    have hmB : m.map v.toRingHom = mB := by
      change ((IsLocalRing.maximalIdeal R).map (algebraMap R A)).map v.toRingHom = _
      rw [Ideal.map_map]
      congr 1
      ext r
      exact v.commutes r
    have hmT : m.map (Ideal.Quotient.mk L) = mT := by
      change ((IsLocalRing.maximalIdeal R).map (algebraMap R A)).map
        (Ideal.Quotient.mk L) = _
      rw [Ideal.map_map]
      rfl
    have heq : mB.comap f.toRingHom = mT := by
      apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk L)
        Ideal.Quotient.mk_surjective
      rw [Ideal.comap_comap]
      change mB.comap v.toRingHom = mT.comap (Ideal.Quotient.mk L)
      rw [← hmB, ← hmT,
        Ideal.comap_map_of_surjective v.toRingHom hvsurj,
        Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
      have hker : Ideal.comap (Ideal.Quotient.mk L) ⊥ = L := Ideal.mk_ker
      rw [hker]
      change m ⊔ J = m ⊔ L
      exact (sup_comm m J).trans (hsup.symm.trans (sup_comm L m))
    let fbar := Ideal.quotientMap mB f.toRingHom heq.ge
    refine ⟨RingEquiv.ofBijective fbar
      ⟨Ideal.quotientMap_injective' heq.le,
        Ideal.quotientMap_surjective hfsurj⟩, ?_⟩
    intro t
    rfl

end Algebra
