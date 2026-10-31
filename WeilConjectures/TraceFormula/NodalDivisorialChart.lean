/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FineSaturatedLogBlowup
public import Mathlib.GroupTheory.Congruence.Hom
public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Nodal divisorial chart

Source: Illusie–Laszlo–Orgogozo, Exposé VI, Proposition 1.9 proof, printed p. 71
(blueprint: lem-trf-nodal-divisorial-chart).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open AlgebraicGeometry

namespace AlgebraicGeometry

/-- The multiplicative encoding of `ℤ ⊕ P` used in the nodal pushout.
Source: ILO, Exposé VI, Proposition 1.9 (blueprint: lem-trf-nodal-divisorial-chart). -/
abbrev nodalDivisorialBase (P : Type u) [CommMonoid P] := Multiplicative ℤ × P

/-- The relation used to form the explicit nodal amalgamated monoid: the generator
`(1,1)` of `ℕ²` is identified with `(1,a)` of `ℤ ⊕ P` (multiplicatively,
`ofAdd (1,1)` with `(ofAdd 1, a)`).
Source: ILO, Exposé VI, Proposition 1.9 (blueprint: lem-trf-nodal-divisorial-chart). -/
def nodalDivisorialRelation {P : Type u} [CommMonoid P] (a : P) :
    Con (Multiplicative (ℕ × ℕ) × nodalDivisorialBase P) :=
  conGen (fun x y ↦
    x = (Multiplicative.ofAdd ((1, 1) : ℕ × ℕ), 1) ∧
        y = (1, (Multiplicative.ofAdd (1 : ℤ), a)) ∨
      y = (Multiplicative.ofAdd ((1, 1) : ℕ × ℕ), 1) ∧
        x = (1, (Multiplicative.ofAdd (1 : ℤ), a)))

/-- The commutative monoid `ℕ² ⨿_ℕ (ℤ ⊕ P)` as an explicit quotient.
Source: ILO, Exposé VI, Proposition 1.9 (blueprint: lem-trf-nodal-divisorial-chart). -/
def nodalDivisorialMonoid {P : Type u} [CommMonoid P] (a : P) :=
  (nodalDivisorialRelation a).Quotient

instance nodalDivisorialMonoid.commMonoid {P : Type u} [CommMonoid P] (a : P) :
    CommMonoid (nodalDivisorialMonoid a) := by
  dsimp [nodalDivisorialMonoid]
  infer_instance

/-- The quotient map used in the nodal chart construction.
Source: ILO, Exposé VI, Proposition 1.9 (blueprint: lem-trf-nodal-divisorial-chart). -/
def nodalDivisorialQuotient {P : Type u} [CommMonoid P] (a : P) :
    Multiplicative (ℕ × ℕ) × nodalDivisorialBase P →*
      nodalDivisorialMonoid a :=
  Con.mk' _

/-- The canonical map from `ℤ ⊕ P` into the nodal amalgamated monoid.
Source: ILO, Exposé VI, Proposition 1.9 (blueprint: lem-trf-nodal-divisorial-chart). -/
def nodalDivisorialBaseMap {P : Type u} [CommMonoid P] (a : P) :
    nodalDivisorialBase P →* nodalDivisorialMonoid a :=
  (nodalDivisorialQuotient a).comp (MonoidHom.inr _ _)

/-- The map of the two branch generators into the nodal amalgamated monoid.
Source: ILO, Exposé VI, Proposition 1.9 (blueprint: lem-trf-nodal-divisorial-chart). -/
def nodalDivisorialBranchMap {P : Type u} [CommMonoid P] (a : P) :
    Multiplicative (ℕ × ℕ) →* nodalDivisorialMonoid a :=
  (nodalDivisorialQuotient a).comp (MonoidHom.inl _ _)

/-- The group-completion map induced by the base map of the nodal pushout.
Source: ILO, Exposé VI, Proposition 1.9 (blueprint: lem-trf-nodal-divisorial-chart). -/
noncomputable def nodalDivisorialGroupMap {P : Type u} [CommMonoid P] (a : P) :
    Algebra.GrothendieckGroup (nodalDivisorialBase P) →*
      Algebra.GrothendieckGroup (nodalDivisorialMonoid a) :=
  Algebra.GrothendieckGroup.lift
    ((Algebra.GrothendieckGroup.of (M := nodalDivisorialMonoid a)).comp
      (nodalDivisorialBaseMap a))

/-- The canonical monoid homomorphism evaluating the base chart on a ring.
Source: ILO, Exposé VI, Proposition 1.9 proof, printed p. 71
(blueprint: lem-trf-nodal-divisorial-chart). -/
noncomputable def nodalDivisorialBaseEvaluation
    {P : Type u} [CommMonoid P] {A : Type v} [CommRing A]
    (α : P →* A) (ε : Aˣ) : nodalDivisorialBase P →* A :=
  { toFun := fun r ↦ ((ε ^ r.1.toAdd : Aˣ) : A) * α r.2
    map_one' := by simp
    map_mul' := by
      intro x y
      change ((↑(ε ^ (x.1 * y.1).toAdd) : A) * α (x.2 * y.2)) = _
      rw [show (x.1 * y.1).toAdd = x.1.toAdd + y.1.toAdd by rfl]
      have hp := congrArg (fun z : Aˣ ↦ (z : A))
        (zpow_add ε x.1.toAdd y.1.toAdd)
      rw [hp]
      simp only [map_mul, Units.val_mul]
      ring_nf }

/-- The canonical `ℤ[R]`-algebra structure on a coefficient ring.
Source: ILO, Exposé VI, Proposition 1.9 proof, printed p. 71
(blueprint: lem-trf-nodal-divisorial-chart). -/
@[instance_reducible]
noncomputable def nodalDivisorialCoefficientAlgebra
    {P : Type u} [CommMonoid P] {A : Type v} [CommRing A]
    (α : P →* A) (ε : Aˣ) :
    Algebra (MonoidAlgebra ℤ (nodalDivisorialBase P)) A :=
  (MonoidAlgebra.lift ℤ A (nodalDivisorialBase P)
      (nodalDivisorialBaseEvaluation α ε)).toRingHom.toAlgebra

/-- The canonical base algebra structure on the monoid algebra of the nodal pushout.
Source: ILO, Exposé VI, Proposition 1.9 proof, printed p. 71
(blueprint: lem-trf-nodal-divisorial-chart). -/
@[instance_reducible]
noncomputable def nodalDivisorialMonoidAlgebraBaseAlgebra
    {P : Type u} [CommMonoid P] (a : P) :
    Algebra (MonoidAlgebra ℤ (nodalDivisorialBase P))
      (MonoidAlgebra ℤ (nodalDivisorialMonoid a)) :=
  (MonoidAlgebra.mapDomainRingHom ℤ (nodalDivisorialBaseMap a)).toAlgebra

/-- The tensor product equipped with its canonical coefficient-ring algebra structure.
Source: ILO, Exposé VI, Proposition 1.9 proof, printed p. 71
(blueprint: lem-trf-nodal-divisorial-chart). -/
@[instance_reducible]
noncomputable def nodalDivisorialTensorAlgebra
    {P : Type u} [CommMonoid P] {A : Type v} [CommRing A] (a : P)
    (α : P →* A) (ε : Aˣ) :
    Algebra A (@TensorProduct (MonoidAlgebra ℤ (nodalDivisorialBase P)) _ A
      (MonoidAlgebra ℤ (nodalDivisorialMonoid a)) _ _
      (nodalDivisorialCoefficientAlgebra α ε).toModule
      (nodalDivisorialMonoidAlgebraBaseAlgebra a).toModule) := by
  letI : Algebra (MonoidAlgebra ℤ (nodalDivisorialBase P)) A :=
    nodalDivisorialCoefficientAlgebra α ε
  letI : Algebra (MonoidAlgebra ℤ (nodalDivisorialBase P))
      (MonoidAlgebra ℤ (nodalDivisorialMonoid a)) :=
    nodalDivisorialMonoidAlgebraBaseAlgebra a
  exact (Algebra.TensorProduct.includeLeft
    (R := MonoidAlgebra ℤ (nodalDivisorialBase P))
    (S := A) (A := A)
    (B := MonoidAlgebra ℤ (nodalDivisorialMonoid a))).toRingHom.toAlgebra

/-- Canonical tensor representatives of the nodal branch and base monomials.
Source: ILO, Exposé VI, Proposition 1.9 proof, printed p. 71
(blueprint: lem-trf-nodal-divisorial-chart). -/
noncomputable def nodalDivisorialTensorMonomial
    {P : Type u} [CommMonoid P] {A : Type v} [CommRing A] (a : P)
    (α : P →* A) (ε : Aˣ) (q : nodalDivisorialMonoid a) :
    @TensorProduct (MonoidAlgebra ℤ (nodalDivisorialBase P)) _ A
      (MonoidAlgebra ℤ (nodalDivisorialMonoid a)) _ _
      (nodalDivisorialCoefficientAlgebra α ε).toModule
      (nodalDivisorialMonoidAlgebraBaseAlgebra a).toModule :=
  @TensorProduct.tmul (MonoidAlgebra ℤ (nodalDivisorialBase P)) _ A
    (MonoidAlgebra ℤ (nodalDivisorialMonoid a)) _ _
    (nodalDivisorialCoefficientAlgebra α ε).toModule
    (nodalDivisorialMonoidAlgebraBaseAlgebra a).toModule 1
    (MonoidAlgebra.single q 1)

/-- The nodal divisorial chart calculation. Source: ILO, Exposé VI, Proposition 1.9
proof, printed p. 71 (blueprint: lem-trf-nodal-divisorial-chart).

Proof (written additively, `u, v` the branch generators, `e = g(1,0)`):
1. Put `H = ℤ ⊕ ℤ ⊕ Pᵍᵖ`; `u ↦ (1,0,0)`, `v ↦ (-1,1,a)`, `g(n,p) ↦ (0,n,p)` respects the
   relation and gives `h : Q → H`, with `(x,y,n,p) ↦ (x-y, n+y, p+ya)`; applying the relation
   `k = min(x,y)` times reduces a representative to one with a branch coordinate zero.
2. Reduced representatives of `(m,t,b)` are `(m₊, m₋, t-m₋, b-m₋a)`, so `h` is injective
   (`P → Pᵍᵖ` injective) with image `{(m,t,b) | b - m₋a ∈ P}`.
3. `hᵍᵖ : Qᵍᵖ → H` is an isomorphism (inverse `(m,t,b) ↦ mu + te + gᵍᵖ(0,b)`, using
   `v = e + g(0,a) - u`); hence `Q → Qᵍᵖ` is injective, `Q` is generated by `u, v, ±e` and the
   generators of `P`, and saturation of `P` with `(rm)₋ = r m₋` gives saturation of `Q`.
4. `gᵍᵖ(n,p) = (0,n,p)` is injective and projection to `m` identifies the cokernel with `ℤ`.
5. With `B = A[U,V]/(UV - εα(a))`, `(x,y,n,p) ↦ UˣVʸεⁿα(p)` respects the relation and gives
   `ℤ[Q] → B` restricting to the structure map on `ℤ[R]`, hence `F : A ⊗_{ℤ[R]} ℤ[Q] → B`.
6. `U ↦ 1⊗[u]`, `V ↦ 1⊗[v]` kills `UV - εα(a)` (as `1⊗[u+v] = εα(a)⊗[0]`), giving `G`;
   `F, G` are mutually inverse on generators, with the stated generator images. -/
theorem nodalDivisorialChart
    {P : Type u} [CommMonoid P] (hP : IsFineSaturatedMonoid P) (a : P) :
    IsFineSaturatedMonoid (nodalDivisorialMonoid a) ∧
      Function.Injective (nodalDivisorialGroupMap a) ∧
      Nonempty
        ((Algebra.GrothendieckGroup (nodalDivisorialMonoid a) ⧸
            Subgroup.map (nodalDivisorialGroupMap a) ⊤) ≃*
          Multiplicative ℤ) ∧
      ∀ (A : Type v) [CommRing A] (α : P →* A) (ε : Aˣ),
        ∃ φ :
            @AlgEquiv A
              (@TensorProduct (MonoidAlgebra ℤ (nodalDivisorialBase P)) _ A
                (MonoidAlgebra ℤ (nodalDivisorialMonoid a)) _ _
                (nodalDivisorialCoefficientAlgebra α ε).toModule
                (nodalDivisorialMonoidAlgebraBaseAlgebra a).toModule)
              ((MvPolynomial (Fin 2) A) ⧸
                Ideal.span
                  ({MvPolynomial.X 0 * MvPolynomial.X 1 -
                      MvPolynomial.C (((ε : Aˣ) : A) * α a)} :
                    Set (MvPolynomial (Fin 2) A))) _ _ _
              (nodalDivisorialTensorAlgebra a α ε) inferInstance,
          φ (nodalDivisorialTensorMonomial a α ε
              (nodalDivisorialBranchMap a (1, 0))) =
            Ideal.Quotient.mk _ (MvPolynomial.X 0) ∧
          φ (nodalDivisorialTensorMonomial a α ε
              (nodalDivisorialBranchMap a (0, 1))) =
            Ideal.Quotient.mk _ (MvPolynomial.X 1) ∧
          ∀ r : nodalDivisorialBase P,
            φ (nodalDivisorialTensorMonomial a α ε
                (nodalDivisorialBaseMap a r)) =
              Ideal.Quotient.mk _
                (MvPolynomial.C (((ε ^ r.1.toAdd : Aˣ) : A) * α r.2)) := by
  sorry

end AlgebraicGeometry
