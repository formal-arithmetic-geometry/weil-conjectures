/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.TensorProduct.Basic

import Sheaf.RingTheory.MonomialIdealTensorPresentation
import Mathlib.Algebra.MonoidAlgebra.Ideal

/-! # Eliminating a split unit group from a monomial ideal tensor

Source: ILO, Exposé VI 3.7(a), printed p. 75, and Exposé VIII, proof of 3.4.3,
printed p. 110; the elementary split-group calculation in that chart context
(blueprint: lem-trf-split-unit-group-ideal-tensor).

Monoids are written multiplicatively: `1` denotes the additive zero of the source.
We write the coefficient factor first in the tensor, using tensor symmetry to identify
`A ⊗ I` with the source's `I ⊗ A`. The helpers merely expose Mathlib's tensor with
the specified coefficient action and bundle the characterizing equations of the comparison.
-/

@[expose] public section

set_option autoImplicit false

universe u v w w'

open scoped TensorProduct

namespace MonoidAlgebra
namespace SplitUnitGroupIdealTensor

/-- The ordinary ideal tensor with its specified coefficient action and its coefficient-ring
module structure. Source: Stacks 00CX; ILO VIII 3.4.3
(blueprint: lem-trf-split-unit-group-ideal-tensor). -/
noncomputable def tensor {R : Type u} {A : Type w} [CommRing R] [CommRing A]
    (e : R →+* A) (I : Ideal R) : ModuleCat.{max u w} A :=
  letI := e.toAlgebra
  ModuleCat.of A (A ⊗[R] I)

/-- The pure tensor, with the ideal factor written first as in the source.
Source: Stacks 00CX; ILO VIII 3.4.3
(blueprint: lem-trf-split-unit-group-ideal-tensor). -/
noncomputable def pure {R : Type u} {A : Type w} [CommRing R] [CommRing A]
    (e : R →+* A) (I : Ideal R) (x : I) (a : A) : tensor e I :=
  letI := e.toAlgebra
  a ⊗ₜ[R] x

/-- Canonical tensor multiplication, `x tensor a ↦ e(x) * a`.
Source: Stacks 00CX; ILO VIII 3.4.3
(blueprint: lem-trf-split-unit-group-ideal-tensor). -/
noncomputable def multiplication {R : Type u} {A : Type w} [CommRing R] [CommRing A]
    (e : R →+* A) (I : Ideal R) : tensor e I →ₗ[A] A :=
  letI := e.toAlgebra
  LinearMap.liftBaseChange A ((Algebra.linearMap R A).comp I.subtype)

/-- Evaluation of integer monomials at the chosen character.
Source: ILO VI 3.7(a) and VIII 3.4.3
(blueprint: lem-trf-split-unit-group-ideal-tensor). -/
noncomputable def evaluation {Q : Type u} {A : Type w} [CommMonoid Q] [CommRing A]
    (c : Q →* A) : MonoidAlgebra ℤ Q →+* A :=
  (MonoidAlgebra.lift ℤ A Q c).toRingHom

/-- Evaluation of the product chart, `z^(q,g) ↦ c(q) * v(g)`.
Source: ILO VI 3.7(a) and VIII 3.4.3
(blueprint: lem-trf-split-unit-group-ideal-tensor). -/
noncomputable def splitEvaluation {Q : Type u} {G : Type v} {A : Type w}
    [CommMonoid Q] [CommGroup G] [CommRing A] (c : Q →* A) (v : G →* Aˣ) :
    MonoidAlgebra ℤ (Q × G) →+* A :=
  evaluation (c.coprod ((Units.coeHom A).comp v))

/-- The specified split-chart comparison, bundled with all its characterizing equations.
This is a package of the conclusions, not an additional hypothesis on the rings or characters.
Source: ILO VI 3.7(a) and VIII 3.4.3; elementary split-group calculation
(blueprint: lem-trf-split-unit-group-ideal-tensor). -/
structure Comparison {Q : Type u} {G : Type v} {A : Type w}
    [CommMonoid Q] [CommGroup G] [CommRing A] (c : Q →* A) (v : G →* Aˣ)
    (I : Ideal (MonoidAlgebra ℤ Q)) (J : Ideal (MonoidAlgebra ℤ (Q × G))) where
  /-- The coefficient-linear isomorphism. -/
  equiv : tensor (splitEvaluation c v) J ≃ₗ[A] tensor (evaluation c) I
  /-- The forward map on every monomial pure tensor. -/
  monomial : ∀ (q : Q) (g : G) (x : I) (y : J) (a : A),
    (x : MonoidAlgebra ℤ Q) = MonoidAlgebra.single q 1 →
    (y : MonoidAlgebra ℤ (Q × G)) = MonoidAlgebra.single (q, g) 1 →
    equiv (pure (splitEvaluation c v) J y a) = pure (evaluation c) I x ((v g : A) * a)
  /-- The inverse is the actual ideal-tensor map induced by the inclusion and identity on A. -/
  inverse : ∀ (x : I) (y : J) (a : A),
    (y : MonoidAlgebra ℤ (Q × G)) =
      MonoidAlgebra.mapDomainRingHom ℤ (MonoidHom.inl Q G) (x : MonoidAlgebra ℤ Q) →
    equiv.symm (pure (evaluation c) I x a) = pure (splitEvaluation c v) J y a
  /-- Compatibility with the canonical multiplication maps to A. -/
  multiplication :
    (SplitUnitGroupIdealTensor.multiplication (evaluation c) I).comp equiv.toLinearMap =
      SplitUnitGroupIdealTensor.multiplication (splitEvaluation c v) J

local notation "P" => MonomialIdealTensorPresentation.monomial

private theorem evaluation_of {Q : Type u} {A : Type w}
    [CommMonoid Q] [CommRing A] (c : Q →* A) (q : Q) :
    evaluation c (MonoidAlgebra.single q 1) = c q := by
  simp [evaluation]

private theorem splitEvaluation_of {Q : Type u} {G : Type v} {A : Type w}
    [CommMonoid Q] [CommGroup G] [CommRing A]
    (c : Q →* A) (v : G →* Aˣ) (q : Q) (g : G) :
    splitEvaluation c v (MonoidAlgebra.single (q, g) 1) = c q * (v g : A) := by
  simp [splitEvaluation, evaluation_of, MonoidHom.coprod_apply]

private theorem ideal_extension {Q : Type u} {G : Type v}
    [CommMonoid Q] [CommGroup G] (K : Set Q)
    (I : Ideal (MonoidAlgebra ℤ Q))
    (hI : I = Ideal.span (MonoidAlgebra.of ℤ Q '' K))
    (J : Ideal (MonoidAlgebra ℤ (Q × G)))
    (hJ : J = Ideal.span (MonoidAlgebra.of ℤ (Q × G) '' (K ×ˢ Set.univ))) :
    I.map (MonoidAlgebra.mapDomainRingHom ℤ (MonoidHom.inl Q G)) = J := by
  let ι := MonoidAlgebra.mapDomainRingHom ℤ (MonoidHom.inl Q G)
  have hι (q : Q) : ι (MonoidAlgebra.of ℤ Q q) =
      MonoidAlgebra.of ℤ (Q × G) (q, 1) := by
    simp [ι, MonoidAlgebra.mapDomainRingHom, MonoidAlgebra.of_apply]
  apply le_antisymm
  · rw [hI, Ideal.map_span, hJ]
    apply Ideal.span_le.mpr
    rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    rw [hι]
    exact Ideal.subset_span ⟨(q, 1), ⟨hq, Set.mem_univ _⟩, rfl⟩
  · rw [hJ]
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨q, g⟩, ⟨hq, _⟩, rfl⟩
    have hmem : ι (MonoidAlgebra.of ℤ Q q) ∈ I.map ι :=
      Ideal.mem_map_of_mem ι (hI ▸ Ideal.subset_span ⟨q, hq, rfl⟩)
    rw [hι] at hmem
    simpa [ι] using Ideal.mul_mem_right (MonoidAlgebra.of ℤ (Q × G) (1, g))
      (I.map ι) hmem

private noncomputable def tensorMap
    {R : Type*} {S : Type*} {A : Type*} {B : Type*}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    (e : R →+* A) (e' : S →+* B) (f : R →+* S) (φ : A →+* B)
    (h : ∀ r, e' (f r) = φ (e r)) (I : Ideal R) (J : Ideal S)
    (hIJ : ∀ x ∈ I, f x ∈ J) : tensor e I →ₛₗ[φ] tensor e' J := by
  let := e.toAlgebra
  let := e'.toAlgebra
  let α : A →ₛₗ[f] B :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun r a ↦ by
        change φ (e r * a) = e' (f r) * φ a
        rw [map_mul, h] }
  let γ : I →ₛₗ[f] J :=
    { toFun := fun x ↦ ⟨f x, hIJ x x.2⟩
      map_add' := fun x y ↦ Subtype.ext (f.map_add x y)
      map_smul' := fun r x ↦ Subtype.ext (f.map_mul r x) }
  let β := TensorProduct.map α γ
  refine { β.toAddMonoidHom with map_smul' := ?_ }
  intro a t
  change β (a • t) = φ a • β t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [smul_add, hx, hy]
  | tmul b x =>
    change (TensorProduct.map α γ) ((a * b) ⊗ₜ[R] x) =
      φ a • (TensorProduct.map α γ) (b ⊗ₜ[R] x)
    rw [TensorProduct.map_tmul, TensorProduct.map_tmul]
    change φ (a * b) ⊗ₜ[S] γ x = (φ a * φ b) ⊗ₜ[S] γ x
    rw [map_mul]

private theorem tensorMap_pure
    {R : Type*} {S : Type*} {A : Type*} {B : Type*}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    (e : R →+* A) (e' : S →+* B) (f : R →+* S) (φ : A →+* B)
    (h : ∀ r, e' (f r) = φ (e r)) (I : Ideal R) (J : Ideal S)
    (hIJ : ∀ x ∈ I, f x ∈ J) (x : I) (a : A) :
    tensorMap e e' f φ h I J hIJ (pure e I x a) =
      pure e' J ⟨f x, hIJ x x.2⟩ (φ a) := rfl

private theorem multiplication_pure {R : Type*} {A : Type*}
    [CommRing R] [CommRing A] (e : R →+* A) (I : Ideal R) (x : I) (a : A) :
    multiplication e I (pure e I x a) = a * e x := rfl

private theorem smul_pure {R : Type*} {A : Type*}
    [CommRing R] [CommRing A] (e : R →+* A) (I : Ideal R)
    (x : I) (a b : A) : a • pure e I x b = pure e I x (a * b) := by
  let := e.toAlgebra
  exact (TensorProduct.smul_tmul' a b x).symm

private theorem pure_monomial_mul {Q : Type u} {A : Type w}
    [CommMonoid Q] [CommRing A] {K : Set Q} {I : Ideal (MonoidAlgebra ℤ Q)}
    (hI : I = Ideal.span (MonoidAlgebra.of ℤ Q '' K))
    (e : MonoidAlgebra ℤ Q →+* A) (hK : ∀ q ∈ K, ∀ r : Q, q * r ∈ K)
    (q : Q) (hq : q ∈ K) (r : Q) (a : A) :
    pure e I (P K I hI (q * r) (hK q hq r)) a =
      pure e I (P K I hI q hq) (e (MonoidAlgebra.of ℤ Q r) * a) :=
  MonomialIdealTensorPresentation.tmul_monomial_mul hI e hK q hq r a

private theorem tensorMap_multiplication
    {R : Type*} {S : Type*} {A : Type*} {B : Type*}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    (e : R →+* A) (e' : S →+* B) (f : R →+* S) (φ : A →+* B)
    (h : ∀ r, e' (f r) = φ (e r)) (I : Ideal R) (J : Ideal S)
    (hIJ : ∀ x ∈ I, f x ∈ J) (t : tensor e I) :
    multiplication e' J (tensorMap e e' f φ h I J hIJ t) =
      φ (multiplication e I t) := by
  let := e.toAlgebra
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul a x =>
    change multiplication e' J (tensorMap e e' f φ h I J hIJ (pure e I x a)) =
      φ (multiplication e I (pure e I x a))
    rw [tensorMap_pure, multiplication_pure, multiplication_pure]
    change φ a * e' (f x) = φ (a * e x)
    rw [h, map_mul]

private theorem evaluation_change {Q : Type u} {A : Type w} {B : Type w'}
    [CommMonoid Q] [CommRing A] [CommRing B]
    (c : Q →* A) (c' : Q →* B) (φ : A →+* B) (hc : ∀ q, c' q = φ (c q)) :
    ∀ r, evaluation c' r = φ (evaluation c r) := by
  have H : evaluation c' = φ.comp (evaluation c) := by
    apply MonoidAlgebra.ringHom_ext'
    · exact Subsingleton.elim _ _
    · apply MonoidHom.ext
      intro q
      change evaluation c' (MonoidAlgebra.of ℤ Q q) =
        φ (evaluation c (MonoidAlgebra.of ℤ Q q))
      simpa only [MonoidAlgebra.of_apply, evaluation_of] using hc q
  exact RingHom.congr_fun H

private theorem splitEvaluation_change
    {Q : Type u} {G : Type v} {A : Type w} {B : Type w'}
    [CommMonoid Q] [CommGroup G] [CommRing A] [CommRing B]
    (c : Q →* A) (v : G →* Aˣ) (c' : Q →* B) (v' : G →* Bˣ)
    (φ : A →+* B) (hc : ∀ q, c' q = φ (c q))
    (hv : ∀ g, (v' g : B) = φ (v g : A)) :
    ∀ r, splitEvaluation c' v' r = φ (splitEvaluation c v r) := by
  apply evaluation_change
  rintro ⟨q, g⟩
  simp [MonoidHom.coprod_apply, hc, hv, map_mul]

private theorem inclusion_evaluation {Q : Type u} {G : Type v} {A : Type w}
    [CommMonoid Q] [CommGroup G] [CommRing A] (c : Q →* A) (v : G →* Aˣ) :
    ∀ r, splitEvaluation c v
      (MonoidAlgebra.mapDomainRingHom ℤ (MonoidHom.inl Q G) r) = evaluation c r := by
  have H : (splitEvaluation c v).comp
      (MonoidAlgebra.mapDomainRingHom ℤ (MonoidHom.inl Q G)) = evaluation c := by
    apply MonoidAlgebra.ringHom_ext'
    · exact Subsingleton.elim _ _
    · apply MonoidHom.ext
      intro q
      change splitEvaluation c v
        (MonoidAlgebra.mapDomainRingHom ℤ (MonoidHom.inl Q G) (MonoidAlgebra.of ℤ Q q)) =
          evaluation c (MonoidAlgebra.of ℤ Q q)
      simp [MonoidAlgebra.mapDomainRingHom, MonoidAlgebra.of_apply, evaluation, splitEvaluation]
  exact RingHom.congr_fun H

private theorem exists_comparison
    {Q : Type u} {G : Type v} {A : Type w}
    [CommMonoid Q] [CommGroup G] [CommRing A]
    (c : Q →* A) (v : G →* Aˣ)
    (K : Set Q) (hK : ∀ q ∈ K, ∀ r : Q, q * r ∈ K)
    (I : Ideal (MonoidAlgebra ℤ Q))
    (hI : I = Ideal.span (MonoidAlgebra.of ℤ Q '' K))
    (J : Ideal (MonoidAlgebra ℤ (Q × G)))
    (hJ : J = Ideal.span (MonoidAlgebra.of ℤ (Q × G) '' (K ×ˢ Set.univ))) :
    Nonempty (Comparison c v I J) := by
  let L := K ×ˢ (Set.univ : Set G)
  have hL : ∀ p ∈ L, ∀ r : Q × G, p * r ∈ L :=
    fun p hp r ↦ ⟨hK p.1 hp.1 r.1, Set.mem_univ _⟩
  let e := evaluation c
  let s := splitEvaluation c v
  let := e.toAlgebra
  let := s.toAlgebra
  let b : L → tensor e I := fun p ↦ pure e I (P K I hI p.1.1 p.2.1) (v p.1.2)
  have hb : ∀ (p : Q × G) (hp : p ∈ L) (r : Q × G),
      b ⟨p * r, hL p hp r⟩ = s (MonoidAlgebra.of ℤ (Q × G) r) • b ⟨p, hp⟩ := by
    rintro ⟨q, g⟩ hp ⟨r, h⟩
    change pure e I (P K I hI (q * r) (hK q hp.1 r)) (v (g * h)) =
      s (MonoidAlgebra.of ℤ (Q × G) (r, h)) • pure e I (P K I hI q hp.1) (v g)
    rw [pure_monomial_mul hI e hK q hp.1 r, smul_pure]
    congr 1
    simp [e, s, evaluation_of, splitEvaluation_of, mul_left_comm, mul_comm]
  obtain ⟨F, hF⟩ := MonomialIdealTensorPresentation.exists_lift hJ s hL b hb
  have hF' (q : Q) (hq : q ∈ K) (g : G) (a : A) :
      F (pure s J (P L J hJ (q, g) ⟨hq, Set.mem_univ _⟩) a) =
        pure e I (P K I hI q hq) ((v g : A) * a) := by
    have H := hF (q, g) ⟨hq, Set.mem_univ _⟩ a
    change F (pure s J (P L J hJ (q, g) ⟨hq, Set.mem_univ _⟩) a) =
      a • pure e I (P K I hI q hq) (v g) at H
    rw [smul_pure, mul_comm a] at H
    exact H
  let ι := MonoidAlgebra.mapDomainRingHom ℤ (MonoidHom.inl Q G)
  have hIJ : ∀ x ∈ I, ι x ∈ J := fun x hx ↦
    ideal_extension K I hI J hJ ▸ Ideal.mem_map_of_mem ι hx
  let T : tensor e I →ₗ[A] tensor s J :=
    tensorMap e s ι (RingHom.id A) (inclusion_evaluation c v) I J hIJ
  have hT (x : I) (a : A) :
      T (pure e I x a) = pure s J ⟨ι x, hIJ x x.2⟩ a := rfl
  have hι (q : Q) (hq : q ∈ K) :
      (⟨ι (P K I hI q hq), hIJ _ (P K I hI q hq).2⟩ : J) =
        P L J hJ (q, 1) ⟨hq, Set.mem_univ _⟩ := by
    apply Subtype.ext
    simp [ι, MonomialIdealTensorPresentation.monomial,
      MonoidAlgebra.mapDomainRingHom, MonoidAlgebra.of_apply]
  have hFT : F.comp T = LinearMap.id := by
    apply LinearMap.toAddMonoidHom_injective
    apply MonomialIdealTensorPresentation.addHom_ext hI e
    intro q hq a
    change F (T (pure e I (P K I hI q hq) a)) = pure e I (P K I hI q hq) a
    rw [hT, hι q hq, hF' q hq 1 a]
    simp
  have hTF : T.comp F = LinearMap.id := by
    apply LinearMap.toAddMonoidHom_injective
    apply MonomialIdealTensorPresentation.addHom_ext hJ s
    rintro ⟨q, g⟩ hq a
    change T (F (pure s J (P L J hJ (q, g) hq) a)) =
      pure s J (P L J hJ (q, g) hq) a
    rw [hF' q hq.1 g a, hT, hι q hq.1]
    have H := pure_monomial_mul hJ s hL (q, 1) ⟨hq.1, Set.mem_univ _⟩ (1, g) a
    simpa [s, splitEvaluation_of] using H.symm
  let E : tensor s J ≃ₗ[A] tensor e I :=
    { F with
      invFun := T
      left_inv := fun t ↦ LinearMap.congr_fun hTF t
      right_inv := fun t ↦ LinearMap.congr_fun hFT t }
  refine ⟨{ equiv := E, monomial := ?_, inverse := ?_, multiplication := ?_ }⟩
  · intro q g x y a hx hy
    have hq : q ∈ K := by
      have hxmem : MonoidAlgebra.single q 1 ∈ I := by rw [← hx]; exact x.2
      have hm : MonoidAlgebra.single q 1 ∈
          Ideal.span (MonoidAlgebra.of ℤ Q '' K) := by simpa only [hI] using hxmem
      obtain ⟨q₀, hq₀, r, hr⟩ := MonoidAlgebra.mem_ideal_span_of_image.mp hm q
        (by simp)
      rw [hr, mul_comm]
      exact hK q₀ hq₀ r
    have hx' : x = P K I hI q hq := Subtype.ext hx
    have hy' : y = P L J hJ (q, g) ⟨hq, Set.mem_univ _⟩ := Subtype.ext hy
    subst x; subst y
    exact hF' q hq g a
  · intro x y a hy
    change T (pure e I x a) = pure s J y a
    rw [hT]
    congr 1
    exact Subtype.ext hy.symm
  · apply LinearMap.toAddMonoidHom_injective
    apply MonomialIdealTensorPresentation.addHom_ext hJ s
    rintro ⟨q, g⟩ hq a
    change multiplication e I (F (pure s J (P L J hJ (q, g) hq) a)) =
      multiplication s J (pure s J (P L J hJ (q, g) hq) a)
    rw [hF' q hq.1 g a, multiplication_pure, multiplication_pure]
    change (v g : A) * a * evaluation c (MonoidAlgebra.of ℤ Q q) =
      a * splitEvaluation c v (MonoidAlgebra.of ℤ (Q × G) (q, g))
    simp [evaluation_of, splitEvaluation_of, mul_left_comm, mul_comm]

/-- The extension of the monomial ideal is the product monomial ideal, and eliminating the
split unit group gives the specified natural coefficient-linear tensor comparison.

Source: ILO VI 3.7(a), printed p. 75, and VIII, proof of 3.4.3, printed p. 110;
the elementary split-group calculation in that chart context
(blueprint: lem-trf-split-unit-group-ideal-tensor).

Proof:
1. Put R = Z[Q], S = Z[Q × G], I = Z[K], J = Z[K × G]. Closure of K under
multiplication makes its additive monomial span an ideal. Inclusion sends I into J.
Conversely z^(q,g) = z^(q,1) z^(1,g), so J is exactly the extension of I.
2. On monomials set B(z^(q,g),a) = z^q tensor v(g)a. The character identities and
tensor balancing give B(z^(qr,gh),a) = B(z^(q,g),c(r)v(h)a). Extend by integer
linearity and additivity; Stacks 00CX, def-weil-pbc-module-tensor-product, induces sigma.
Its formula also shows A-linearity.
3. Insertion of the identity group coordinate sends z^q tensor a to z^(q,1) tensor a.
The same balancing relations make this the ideal-tensor map induced by inclusion
and the identity on A, by def-weil-pbc-module-tensor-product.
4. The two composites are identity on monomial pure tensors: v(1) = 1 in one
direction, and moving z^(1,g) across the tensor gives the other. Such tensors generate
by def-weil-pbc-module-tensor-product, giving the linear equivalence.
5. Both multiplication maps send the compared tensors to c(q)v(g)a. For a coefficient
map phi, both orders of comparison and coefficient change send a monomial tensor to
z^q tensor phi(v(g)a). Insertion and multiplication similarly commute with phi.
Generation by monomial pure tensors proves all the naturality equations.
-/
theorem split_unit_group_ideal_tensor
    {Q : Type u} {G : Type v} {A : Type w}
    [CommMonoid Q] [CommGroup G] [CommRing A]
    (c : Q →* A) (v : G →* Aˣ)
    (K : Set Q) (hK : ∀ q ∈ K, ∀ r : Q, q * r ∈ K)
    (I : Ideal (MonoidAlgebra ℤ Q))
    (hI : I = Ideal.span (MonoidAlgebra.of ℤ Q '' K))
    (J : Ideal (MonoidAlgebra ℤ (Q × G)))
    (hJ : J = Ideal.span (MonoidAlgebra.of ℤ (Q × G) '' (K ×ˢ Set.univ))) :
    I.map (MonoidAlgebra.mapDomainRingHom ℤ (MonoidHom.inl Q G)) = J ∧
    ∃ σ : Comparison c v I J,
      ∀ (A' : Type w') [CommRing A'] (φ : A →+* A')
        (c' : Q →* A') (v' : G →* A'ˣ)
        (_hc : ∀ q, c' q = φ (c q)) (_hv : ∀ g, (v' g : A') = φ (v g : A)),
        ∃ (σ' : Comparison c' v' I J)
          (βK : tensor (evaluation c) I →+ tensor (evaluation c') I)
          (βL : tensor (splitEvaluation c v) J →+ tensor (splitEvaluation c' v') J),
          (∀ (x : I) (a : A),
            βK (pure (evaluation c) I x a) = pure (evaluation c') I x (φ a)) ∧
          (∀ (y : J) (a : A), βL (pure (splitEvaluation c v) J y a) =
            pure (splitEvaluation c' v') J y (φ a)) ∧
          (∀ t, σ'.equiv (βL t) = βK (σ.equiv t)) ∧
          (∀ t, σ'.equiv.symm (βK t) = βL (σ.equiv.symm t)) ∧
          (∀ t, multiplication (evaluation c') I (βK t) =
            φ (multiplication (evaluation c) I t)) ∧
          (∀ t, multiplication (splitEvaluation c' v') J (βL t) =
            φ (multiplication (splitEvaluation c v) J t)) := by
  classical
  have hExt := ideal_extension K I hI J hJ
  obtain ⟨σ⟩ := exists_comparison c v K hK I hI J hJ
  refine ⟨hExt, σ, ?_⟩
  intro A' _ φ c' v' hc hv
  obtain ⟨σ'⟩ := exists_comparison c' v' K hK I hI J hJ
  let βK := tensorMap (evaluation c) (evaluation c') (RingHom.id _) φ
    (evaluation_change c c' φ hc) I I (fun _ hx ↦ hx)
  let βL := tensorMap (splitEvaluation c v) (splitEvaluation c' v') (RingHom.id _) φ
    (splitEvaluation_change c v c' v' φ hc hv) J J (fun _ hx ↦ hx)
  have hβK (x : I) (a : A) : βK (pure (evaluation c) I x a) =
      pure (evaluation c') I x (φ a) := rfl
  have hβL (y : J) (a : A) : βL (pure (splitEvaluation c v) J y a) =
      pure (splitEvaluation c' v') J y (φ a) := rfl
  have hInv : ∀ t, σ'.equiv.symm (βK t) = βL (σ.equiv.symm t) := by
    let := (evaluation c).toAlgebra
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul a x =>
      let ι := MonoidAlgebra.mapDomainRingHom ℤ (MonoidHom.inl Q G)
      let y : J := ⟨ι x, hExt ▸ Ideal.mem_map_of_mem ι x.2⟩
      change σ'.equiv.symm (βK (pure (evaluation c) I x a)) =
        βL (σ.equiv.symm (pure (evaluation c) I x a))
      rw [hβK, σ'.inverse x y (φ a) rfl, σ.inverse x y a rfl, hβL]
  refine ⟨σ', βK.toAddMonoidHom, βL.toAddMonoidHom, hβK, hβL, ?_, hInv, ?_, ?_⟩
  · intro t
    apply σ'.equiv.symm.injective
    change σ'.equiv.symm (σ'.equiv (βL t)) = σ'.equiv.symm (βK (σ.equiv t))
    simpa only [LinearEquiv.symm_apply_apply] using (hInv (σ.equiv t)).symm
  · intro t
    change multiplication (evaluation c') I (βK t) = φ (multiplication (evaluation c) I t)
    exact tensorMap_multiplication (evaluation c) (evaluation c') (RingHom.id _) φ
      (evaluation_change c c' φ hc) I I (fun _ hx ↦ hx) t
  · intro t
    change multiplication (splitEvaluation c' v') J (βL t) =
      φ (multiplication (splitEvaluation c v) J t)
    exact tensorMap_multiplication (splitEvaluation c v) (splitEvaluation c' v')
      (RingHom.id _) φ (splitEvaluation_change c v c' v' φ hc hv) J J (fun _ hx ↦ hx) t

end SplitUnitGroupIdealTensor
end MonoidAlgebra
