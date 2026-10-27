/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import Sheaf.LinearAlgebra.ProjectiveDeterminantExactSequence
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import WeilConjectures.RingTheory.CoverModuleExact

/-!
# Scalar comparisons for finite projective exterior powers, duals and determinants

Source: Stacks Project, More on Algebra, Tags 0FJ9, 0FJA and 0FJB; Perfect Complexes,
Tag 0FJY (blueprint: lem-trf-projective-exterior-scalar-comparisons).

The three predicates characterize the canonical maps by their values, including their
inclusions in the exterior algebra. The existence statement and coherence statements use
these characterizations, so no arbitrary choice of comparison is an extra hypothesis.
All coefficient extensions are ordinary scalar extensions, with no flatness requirement.
-/

@[expose] public section

set_option autoImplicit false
universe u v w z t a

open scoped TensorProduct

namespace Module

section Comparisons

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable {V : Type w} [AddCommGroup V] [Module A V]

/-- The exterior comparison is the restriction of the canonical exterior-algebra map.
On pure wedges this is exactly the displayed wedge formula, including degree zero.
Source: Stacks, Tags 0FJ9 and 0FJY.
(blueprint: lem-trf-projective-exterior-scalar-comparisons) -/
def IsExteriorScalarComparison (r : ℕ)
    (e : (B ⊗[A] (⋀[A]^r V)) ≃ₗ[B] (⋀[B]^r (B ⊗[A] V))) : Prop :=
  (∀ (b : B) (x : ⋀[A]^r V),
    (e (b ⊗ₜ[A] x)).val = b • ExteriorAlgebra.scalarExtensionMap
      (TensorProduct.mk A B V 1) x.val) ∧
  ∀ (b : B) (v : Fin r → V),
    e (b ⊗ₜ[A] exteriorPower.ιMulti A r v) =
      b • exteriorPower.ιMulti B r (fun j ↦ (1 : B) ⊗ₜ[A] v j)

/-- The canonical dual comparison, with the contravariant dual convention.
Source: Stacks, Tag 0FJY, affine scalar extension; the finite dual-frame formula.
(blueprint: lem-trf-projective-exterior-scalar-comparisons) -/
def IsDualScalarComparison
    (e : (B ⊗[A] Dual A V) ≃ₗ[B] Dual B (B ⊗[A] V)) : Prop :=
  ∀ (b b' : B) (l : Dual A V) (x : V),
    e (b ⊗ₜ[A] l) (b' ⊗ₜ[A] x) = b * b' * algebraMap A B (l x)

/-- The determinant comparison is the restriction to the socle of the same canonical
exterior-algebra map, also when the rank varies on the base.
Source: Stacks, Tags 0FJA and 0FJY.
(blueprint: lem-trf-projective-exterior-scalar-comparisons) -/
def IsDeterminantScalarComparison
    (e : (B ⊗[A] determinantModule A V) ≃ₗ[B] determinantModule B (B ⊗[A] V)) : Prop :=
  ∀ (b : B) (x : determinantModule A V),
    (e (b ⊗ₜ[A] x)).val = b • ExteriorAlgebra.scalarExtensionMap
      (TensorProduct.mk A B V 1) x.val

/-- The three canonical comparisons exist and are uniquely determined by their formulas.
The determinant and exterior comparisons have the same ambient exterior-algebra formula.
Source: Stacks, Tags 0FJ9, 0FJA, 0FJB and 0FJY.
(blueprint: lem-trf-projective-exterior-scalar-comparisons)

Proof: (1) tensor a finite-free retract to obtain a finite-free retract over B, using
multiplication to identify B tensor A^n with B^n; no flatness is used. (2) A finite dual
frame v_j,l_j gives the inverse h ↦ sum_j h(1 tensor v_j) tensor l_j. Both composites are
identities by the frame expansion. (3) The alternating universal property extends the
wedge formula. Its inverse on wedges of b_j tensor v_j is (product b_j) tensor wedge v_j.
Balancing is immediate; alternation follows by cancellation of paired off-diagonal terms,
also in characteristic two. Pure wedges span, giving both inverse equations, including
r=0. (4) Restrict the multiplicative exterior map to the socle: annihilation by 1 tensor v
implies annihilation by every vector, by spanning. (5) On a finite standard free cover the
map is the top-degree exterior comparison. Chart descent for the socle identifies its
localizations. Glue the local inverses by module-cover exactness and detect both inverse
equations on that cover. (6) Tensor generators and the injective socle inclusion give
uniqueness of all three maps. This does not assert that tensoring preserves annihilators. -/
theorem projectiveScalarComparisons [Module.Finite A V] [Module.Projective A V] :
    (∀ r : ℕ, ∃! e : (B ⊗[A] (⋀[A]^r V)) ≃ₗ[B] (⋀[B]^r (B ⊗[A] V)),
      IsExteriorScalarComparison r e) ∧
    (∃! e : (B ⊗[A] Dual A V) ≃ₗ[B] Dual B (B ⊗[A] V),
      IsDualScalarComparison e) ∧
    (∃! e : (B ⊗[A] determinantModule A V) ≃ₗ[B] determinantModule B (B ⊗[A] V),
      IsDeterminantScalarComparison e) := sorry

variable {W : Type z} [AddCommGroup W] [Module A W]

/-- Naturality in arbitrary linear maps, and contravariant naturality of the dual map.
Source: Stacks, Tags 0FJ9 and 0FJY.
(blueprint: lem-trf-projective-exterior-scalar-comparisons)

Proof: on b tensor wedge v_j, both exterior composites give b times wedge (1 tensor f v_j).
For the dual equation evaluate on b' tensor v: both sides give bb' alpha(l(f(v))).
Pure tensors and pure wedges span, so these generator equations give the asserted
identities on arbitrary elements. The hypotheses specify the unique canonical comparisons
of projectiveScalarComparisons; they impose no condition on f. -/
theorem scalarComparisons_naturality (r : ℕ) (f : V →ₗ[A] W)
    (cV : (B ⊗[A] (⋀[A]^r V)) ≃ₗ[B] (⋀[B]^r (B ⊗[A] V)))
    (cW : (B ⊗[A] (⋀[A]^r W)) ≃ₗ[B] (⋀[B]^r (B ⊗[A] W)))
    (hcV : IsExteriorScalarComparison r cV) (hcW : IsExteriorScalarComparison r cW)
    (dV : (B ⊗[A] Dual A V) ≃ₗ[B] Dual B (B ⊗[A] V))
    (dW : (B ⊗[A] Dual A W) ≃ₗ[B] Dual B (B ⊗[A] W))
    (hdV : IsDualScalarComparison dV) (hdW : IsDualScalarComparison dW) :
    (∀ x : B ⊗[A] (⋀[A]^r V),
      exteriorPower.map r (f.baseChange B) (cV x) =
        cW ((exteriorPower.map r f).baseChange B x)) ∧
    ∀ x : B ⊗[A] Dual A W,
      (f.baseChange B).dualMap (dW x) = dV (f.dualMap.baseChange B x) := sorry

/-- Evaluation commutes with scalar extension, on arbitrary dual tensors and vectors.
Source: Stacks, Tag 0FJY, affine scalar extension.
(blueprint: lem-trf-projective-exterior-scalar-comparisons)

Proof: first take x=b tensor l and y=b' tensor v. Both sides are bb' alpha(l(v))
by the defining dual formula and the tensor-distribution formula. Extend additively in
both variables, since pure tensors span. The rid map is multiplication B tensor A → B,
so this is the full evaluation square rather than just its value at unit coefficients. -/
theorem scalarDual_evaluation
    (d : (B ⊗[A] Dual A V) ≃ₗ[B] Dual B (B ⊗[A] V))
    (hd : IsDualScalarComparison d) (x : B ⊗[A] Dual A V) (y : B ⊗[A] V) :
    d x y = TensorProduct.AlgebraTensorModule.rid A B B
      ((TensorProduct.lift (LinearMap.id : Dual A V →ₗ[A] Dual A V)).baseChange B
        ((TensorProduct.AlgebraTensorModule.distribBaseChange A B (Dual A V) V).symm
          (x ⊗ₜ[B] y))) := sorry

/-- Scalar tensor distribution respects ordinary tensor symmetry.
Source: Stacks, Algebra, Tag 00DM, and Tag 0FJY.
(blueprint: lem-trf-projective-exterior-scalar-comparisons)

Proof: both sides send b tensor (v tensor w) to (1 tensor w) tensor (b tensor v),
where balancing identifies this with (b tensor w) tensor (1 tensor v).
Tensor generators span. These are the ordinary tensor constraints used in the evaluation
and determinant squares, and symmetry introduces no graded sign. -/
theorem scalarTensor_symmetry (x : B ⊗[A] (V ⊗[A] W)) :
    TensorProduct.comm B (B ⊗[A] V) (B ⊗[A] W)
      (TensorProduct.AlgebraTensorModule.distribBaseChange A B V W x) =
    TensorProduct.AlgebraTensorModule.distribBaseChange A B W V
      ((TensorProduct.comm A V W).toLinearMap.baseChange B x) := sorry

/-- Exterior multiplication is preserved, with the usual order of wedge factors.
Source: Stacks, Tags 0FJA and 0FJY.
(blueprint: lem-trf-projective-exterior-scalar-comparisons)

Proof: use the ambient inclusion formulas for the three comparisons. The scalar exterior
map is an algebra map, hence carries x*y to its two images in the same order; central
scalars multiply as bc. The socle inclusion uses this very calculation. -/
theorem scalarExterior_product (r s : ℕ)
    (cr : (B ⊗[A] (⋀[A]^r V)) ≃ₗ[B] (⋀[B]^r (B ⊗[A] V)))
    (cs : (B ⊗[A] (⋀[A]^s V)) ≃ₗ[B] (⋀[B]^s (B ⊗[A] V)))
    (ct : (B ⊗[A] (⋀[A]^(r + s) V)) ≃ₗ[B] (⋀[B]^(r + s) (B ⊗[A] V)))
    (hr : IsExteriorScalarComparison r cr) (hs : IsExteriorScalarComparison s cs)
    (ht : IsExteriorScalarComparison (r + s) ct)
    (b c : B) (x : ⋀[A]^r V) (y : ⋀[A]^s V) (z : ⋀[A]^(r + s) V)
    (hz : z.val = x.val * y.val) :
    (ct ((b * c) ⊗ₜ[A] z)).val = (cr (b ⊗ₜ[A] x)).val * (cs (c ⊗ₜ[A] y)).val := sorry

/-- Determinant naturality under isomorphisms, expressed after the injective socle
inclusions. The existential y is exactly det(f)(x), specified by its exterior image.
Source: Stacks, Tags 0FJ9, 0FJA and 0FJY.
(blueprint: lem-trf-projective-exterior-scalar-comparisons)

Proof: an isomorphism carries the socle to the socle, since every target vector is an
image of a source vector. This gives y uniquely by its inclusion. Functoriality of the
exterior scalar map, checked on degree-one generators, gives the displayed square after
inclusion. Injectivity of the socle inclusions gives naturality in determinant modules. -/
theorem scalarDeterminant_naturality (f : V ≃ₗ[A] W)
    (sV : (B ⊗[A] determinantModule A V) ≃ₗ[B] determinantModule B (B ⊗[A] V))
    (sW : (B ⊗[A] determinantModule A W) ≃ₗ[B] determinantModule B (B ⊗[A] W))
    (hsV : IsDeterminantScalarComparison sV) (hsW : IsDeterminantScalarComparison sW)
    (x : determinantModule A V) :
    ∃ y : determinantModule A W, y.val = ExteriorAlgebra.map f.toLinearMap x.val ∧
      ∀ b : B, (sW (b ⊗ₜ[A] y)).val =
        ExteriorAlgebra.map (f.toLinearMap.baseChange B) (sV (b ⊗ₜ[A] x)).val := sorry

end Comparisons

section Identity

variable {A : Type u} [CommRing A] {V : Type w} [AddCommGroup V] [Module A V]

/-- Compatibility with the identity scalar extension under the usual left unitor.
Source: Stacks, Tags 0FJ9 and 0FJY.
(blueprint: lem-trf-projective-exterior-scalar-comparisons)

Proof: on a tensor a tensor wedge v_j the exterior formula becomes a times wedge v_j
under the unitor. The dual formula evaluated at 1 tensor v becomes a*l(v). The socle
formula becomes a*x after the exterior map of the unitor. Extend from spanning tensors
and wedges, using the injective socle inclusion for determinants. -/
theorem scalarComparisons_identity (r : ℕ)
    (c : (A ⊗[A] (⋀[A]^r V)) ≃ₗ[A] (⋀[A]^r (A ⊗[A] V)))
    (hc : IsExteriorScalarComparison r c)
    (d : (A ⊗[A] Dual A V) ≃ₗ[A] Dual A (A ⊗[A] V))
    (hd : IsDualScalarComparison d)
    (s : (A ⊗[A] determinantModule A V) ≃ₗ[A] determinantModule A (A ⊗[A] V))
    (hs : IsDeterminantScalarComparison s) :
    (∀ (a : A) (x : ⋀[A]^r V),
      exteriorPower.map r (TensorProduct.lid A V).toLinearMap (c (a ⊗ₜ[A] x)) = a • x) ∧
    (∀ (a : A) (l : Dual A V) (v : V),
      d (a ⊗ₜ[A] l) ((TensorProduct.lid A V).symm v) = a * l v) ∧
    ∀ (a : A) (x : determinantModule A V),
      ExteriorAlgebra.map (TensorProduct.lid A V).toLinearMap (s (a ⊗ₜ[A] x)).val =
        a • x.val := sorry

end Identity

section Tower

variable {A : Type u} {B : Type v} {C : Type t}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable {V : Type w} [AddCommGroup V] [Module A V]

/-- Exterior comparison respects successive scalar extensions and the standard
c tensor (b tensor v) ↦ c*beta(b) tensor v identification.
Source: Stacks, Tags 0FJ9 and 0FJY.
(blueprint: lem-trf-projective-exterior-scalar-comparisons)

Proof: expand x in pure wedges. Both sides send c tensor (b tensor wedge v_j) to
c*beta(b) times wedge (1 tensor v_j). Tensor balancing and spanning give the full
associativity diagram; the cancellation equivalence displayed is the standard one. -/
theorem scalarExterior_tower (r : ℕ)
    (cAB : (B ⊗[A] (⋀[A]^r V)) ≃ₗ[B] (⋀[B]^r (B ⊗[A] V)))
    (cBC : (C ⊗[B] (⋀[B]^r (B ⊗[A] V))) ≃ₗ[C] (⋀[C]^r (C ⊗[B] (B ⊗[A] V))))
    (cAC : (C ⊗[A] (⋀[A]^r V)) ≃ₗ[C] (⋀[C]^r (C ⊗[A] V)))
    (hAB : IsExteriorScalarComparison r cAB) (hBC : IsExteriorScalarComparison r cBC)
    (hAC : IsExteriorScalarComparison r cAC) (b : B) (c : C) (x : ⋀[A]^r V) :
    exteriorPower.map r
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C V).toLinearMap
      (cBC (c ⊗ₜ[B] cAB (b ⊗ₜ[A] x))) =
        cAC ((c * algebraMap B C b) ⊗ₜ[A] x) := sorry

/-- The contravariant dual comparison respects the same scalar-tower identification.
Source: Stacks, Tag 0FJY.
(blueprint: lem-trf-projective-exterior-scalar-comparisons)

Proof: evaluate on t tensor v after the canonical cancellation equivalence. Both
expressions are c*t*beta(b)*beta(alpha(l(v))). The tower identity for algebra maps gives
equality; tensor spanning in both variables proves the full dual associativity square. -/
theorem scalarDual_tower
    (dAB : (B ⊗[A] Dual A V) ≃ₗ[B] Dual B (B ⊗[A] V))
    (dBC : (C ⊗[B] Dual B (B ⊗[A] V)) ≃ₗ[C] Dual C (C ⊗[B] (B ⊗[A] V)))
    (dAC : (C ⊗[A] Dual A V) ≃ₗ[C] Dual C (C ⊗[A] V))
    (hAB : IsDualScalarComparison dAB) (hBC : IsDualScalarComparison dBC)
    (hAC : IsDualScalarComparison dAC) (b : B) (c t : C) (l : Dual A V) (v : V) :
    dBC (c ⊗ₜ[B] dAB (b ⊗ₜ[A] l))
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C V).symm (t ⊗ₜ[A] v)) =
        dAC ((c * algebraMap B C b) ⊗ₜ[A] l) (t ⊗ₜ[A] v) := sorry

/-- The socle comparison respects successive scalar extensions, including variable rank.
Source: Stacks, Tags 0FJA and 0FJY.
(blueprint: lem-trf-projective-exterior-scalar-comparisons)

Proof: apply the two socle inclusion formulas. The exterior map of the cancellation
identification composes the two scalar exterior maps into the direct scalar exterior
map. This is checked on generators and hence on the entire exterior algebra. Scalars
become c*beta(b). Socle inclusions are injective, proving the determinant tower square. -/
theorem scalarDeterminant_tower
    (sAB : (B ⊗[A] determinantModule A V) ≃ₗ[B] determinantModule B (B ⊗[A] V))
    (sBC : (C ⊗[B] determinantModule B (B ⊗[A] V)) ≃ₗ[C]
      determinantModule C (C ⊗[B] (B ⊗[A] V)))
    (sAC : (C ⊗[A] determinantModule A V) ≃ₗ[C] determinantModule C (C ⊗[A] V))
    (hAB : IsDeterminantScalarComparison sAB) (hBC : IsDeterminantScalarComparison sBC)
    (hAC : IsDeterminantScalarComparison sAC) (b : B) (c : C) (x : determinantModule A V) :
    ExteriorAlgebra.map
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C V).toLinearMap
      (sBC (c ⊗ₜ[B] sAB (b ⊗ₜ[A] x))).val =
        (sAC ((c * algebraMap B C b) ⊗ₜ[A] x)).val := sorry

end Tower

section DeterminantSequence

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- Rank-zero determinants have the multiplication unit comparison, for every zero-module
model and its uniquely normalized ring identifications.
Source: Stacks, Tags 0FJ9, 0FJA and 0FJY.
(blueprint: lem-trf-projective-exterior-scalar-comparisons)

Proof: both inverses of the normalized zero determinant identifications are algebraMap,
by determinantModule_zero. The scalar exterior map preserves algebraMap, so the socle
comparison sends b tensor a to b*alpha(a). Every x is eA.symm(eA x), proving the formula.
This includes the zero ring, since neither normalization assumes nontriviality. -/
theorem scalarDeterminant_zero {V : Type w} [AddCommGroup V] [Module A V] [Subsingleton V]
    (s : (B ⊗[A] determinantModule A V) ≃ₗ[B] determinantModule B (B ⊗[A] V))
    (hs : IsDeterminantScalarComparison s)
    (eA : determinantModule A V ≃ₗ[A] A)
    (eB : determinantModule B (B ⊗[A] V) ≃ₗ[B] B)
    (hA : ∀ a : A, (eA.symm a).val = algebraMap A (ExteriorAlgebra A V) a)
    (hB : ∀ b : B, (eB.symm b).val =
      algebraMap B (ExteriorAlgebra B (B ⊗[A] V)) b)
    (b : B) (x : determinantModule A V) :
    eB (s (b ⊗ₜ[A] x)) = b * algebraMap A B (eA x) := sorry

/-- The scalar-extended sequence is short exact, and its canonical kernel-first wedge
map is the scalar extension of the original one via the canonical comparisons.
Source: Stacks, Tag 0FJB (both constructions), and Tag 0FJY.
(blueprint: lem-trf-projective-exterior-scalar-comparisons)

Proof: (1) split p by projectivity of W, giving V ≃ U direct-sum W. Tensoring the inverse
equations preserves this decomposition and proves exactness after arbitrary extension.
The three terms remain finite projective as scalar extensions of finite-free retracts.
(2) The determinant exact-sequence theorem supplies the unique extended kernel-first map.
(3) Choose simultaneous finite standard free charts for U and W. On a chart use bases u_j,
w_j and lifts t(w_j). Both composites send their top wedges to the wedge of 1 tensor i(u_j)
followed by the wedge of 1 tensor t(w_j), with the same scalar b. Independence of lifts is
part of IsDeterminantExactSequenceMap. (4) These wedge tensors span the chart source;
module-cover equality detection globalizes the square. The displayed equation is precisely
the square with distribBaseChange, which sends b tensor (x tensor y) to
(b tensor x) tensor (1 tensor y). Empty bases include either zero-rank factor. -/
theorem scalarDeterminant_exactSequence
    {U : Type w} [AddCommGroup U] [Module A U] [Module.Finite A U] [Module.Projective A U]
    {V : Type z} [AddCommGroup V] [Module A V] [Module.Finite A V] [Module.Projective A V]
    {W : Type t} [AddCommGroup W] [Module A W] [Module.Finite A W] [Module.Projective A W]
    (i : U →ₗ[A] V) (p : V →ₗ[A] W)
    (hi : Function.Injective i) (hp : Function.Surjective p) (hex : Function.Exact i p)
    (sU : (B ⊗[A] determinantModule A U) ≃ₗ[B] determinantModule B (B ⊗[A] U))
    (sV : (B ⊗[A] determinantModule A V) ≃ₗ[B] determinantModule B (B ⊗[A] V))
    (sW : (B ⊗[A] determinantModule A W) ≃ₗ[B] determinantModule B (B ⊗[A] W))
    (hU : IsDeterminantScalarComparison sU) (hV : IsDeterminantScalarComparison sV)
    (hW : IsDeterminantScalarComparison sW)
    (e : (determinantModule A U ⊗[A] determinantModule A W) ≃ₗ[A] determinantModule A V)
    (he : IsDeterminantExactSequenceMap i p e) :
    Function.Injective (i.baseChange B) ∧ Function.Surjective (p.baseChange B) ∧
      Function.Exact (i.baseChange B) (p.baseChange B) ∧
      ∃ eB : (determinantModule B (B ⊗[A] U) ⊗[B] determinantModule B (B ⊗[A] W)) ≃ₗ[B]
          determinantModule B (B ⊗[A] V),
        IsDeterminantExactSequenceMap (i.baseChange B) (p.baseChange B) eB ∧
        ∀ (b : B) (x : determinantModule A U) (y : determinantModule A W),
          sV (b ⊗ₜ[A] e (x ⊗ₜ[A] y)) =
            eB (sU (b ⊗ₜ[A] x) ⊗ₜ[B] sW ((1 : B) ⊗ₜ[A] y)) := sorry

end DeterminantSequence

end Module
