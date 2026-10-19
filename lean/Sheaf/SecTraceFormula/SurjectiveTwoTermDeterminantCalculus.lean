/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
import WeilConjectures.RingTheory.FiniteProjectiveStandardFreeCover
public import Sheaf.LinearAlgebra.ProjectiveDeterminantExactSequence
import Sheaf.TraceFormula.LocalCommonSummandSurjections
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Kernel-normalized determinant maps for surjective two-term quasi-isomorphisms

Source: Stacks Project, More on Algebra, Tag 0FJI, construction before Lemma 0FJJ;
Tags 0FJK and 0FJL (blueprint: lem-trf-surjective-two-term-determinant-calculus).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory
open scoped TensorProduct

namespace Module

/-- A two-term cochain complex of `R`-modules, with terms in degrees `-1` and `0`.
Source: Stacks Project, More on Algebra, Tag 0FJI (blueprint:
lem-trf-surjective-two-term-determinant-calculus). -/
structure TwoTermComplex (R : Type u) [CommRing R] where
  neg : ModuleCat.{v} R
  zero : ModuleCat.{v} R
  differential : neg ⟶ zero

/-- A map of two-term complexes.  The displayed equality is the chain-map equation.
Source: Stacks Project, More on Algebra, Tag 0FJI (blueprint:
lem-trf-surjective-two-term-determinant-calculus). -/
structure TwoTermMap {R : Type u} [CommRing R] (P Q : TwoTermComplex R) where
  neg : P.neg ⟶ Q.neg
  zero : P.zero ⟶ Q.zero
  commutes : ModuleCat.Hom.hom Q.differential ∘ₗ ModuleCat.Hom.hom neg =
    ModuleCat.Hom.hom zero ∘ₗ ModuleCat.Hom.hom P.differential

/-- Degreewise surjectivity of a map of two-term complexes.
Source: Stacks Project, More on Algebra, Tag 0FJI
(blueprint: lem-trf-surjective-two-term-determinant-calculus). -/
def TwoTermMap.DegreewiseSurjective {R : Type u} [CommRing R]
    {P Q : TwoTermComplex R} (a : TwoTermMap P Q) : Prop :=
  Function.Surjective (ModuleCat.Hom.hom a.neg) ∧
    Function.Surjective (ModuleCat.Hom.hom a.zero)

/-- The kernel map in degree `-1`, used to express the degree `-1` cohomology map.
Source: Stacks Project, More on Algebra, Tag 0FJI
(blueprint: lem-trf-surjective-two-term-determinant-calculus). -/
def TwoTermMap.kernelNeg {R : Type u} [CommRing R]
    {P Q : TwoTermComplex R} (a : TwoTermMap P Q) :
    LinearMap.ker (ModuleCat.Hom.hom P.differential) →ₗ[R]
      LinearMap.ker (ModuleCat.Hom.hom Q.differential) :=
  ((ModuleCat.Hom.hom a.neg).domRestrict _).codRestrict _ (by
      intro x
      change ModuleCat.Hom.hom Q.differential (ModuleCat.Hom.hom a.neg x) = 0
      have hx := LinearMap.congr_fun a.commutes (x : P.neg)
      simpa [LinearMap.comp_apply, x.property] using hx)

/-- The explicit two-term meaning of quasi-isomorphism: the induced maps on the
kernel in degree `-1` and the cokernel in degree `0` are bijective.
Source: Stacks Project, More on Algebra, Tag 0FJI
(blueprint: lem-trf-surjective-two-term-determinant-calculus). -/
def TwoTermMap.QuasiIso {R : Type u} [CommRing R]
    {P Q : TwoTermComplex R} (a : TwoTermMap P Q) : Prop :=
  Function.Bijective a.kernelNeg ∧
    (∀ x y : P.zero, ModuleCat.Hom.hom a.zero x - ModuleCat.Hom.hom a.zero y ∈
      LinearMap.range (ModuleCat.Hom.hom Q.differential) →
      x - y ∈ LinearMap.range (ModuleCat.Hom.hom P.differential)) ∧
    (∀ y : Q.zero, ∃ x : P.zero, y - ModuleCat.Hom.hom a.zero x ∈
      LinearMap.range (ModuleCat.Hom.hom Q.differential))

/-- The determinant module of a two-term complex, in degrees `0` and `-1`.
Source: Stacks Project, More on Algebra, Tag 0FJI
(blueprint: lem-trf-surjective-two-term-determinant-calculus). -/
abbrev twoTermDeterminant {R : Type u} [CommRing R] (P : TwoTermComplex R) : Type _ :=
  Module.determinantModule R (P.zero : Type v) ⊗[R]
    Module.Dual R (Module.determinantModule R (P.neg : Type v))

/-- The differential on the kernel complex.
Source: Stacks Project, More on Algebra, Tag 0FJI
(blueprint: lem-trf-surjective-two-term-determinant-calculus). -/
def TwoTermMap.kernelDifferential {R : Type u} [CommRing R]
    {P Q : TwoTermComplex R} (a : TwoTermMap P Q) :
    LinearMap.ker (ModuleCat.Hom.hom a.neg) →ₗ[R]
      LinearMap.ker (ModuleCat.Hom.hom a.zero) :=
  ((ModuleCat.Hom.hom P.differential).domRestrict _).codRestrict _ (by
      intro x
      change ModuleCat.Hom.hom a.zero (ModuleCat.Hom.hom P.differential x) = 0
      have hx := LinearMap.congr_fun a.commutes (x : P.neg)
      simpa [LinearMap.comp_apply, x.property] using hx.symm)

/-- The identity map of a two-term complex.
Source: Stacks Project, More on Algebra, Tag 0FJI
(blueprint: lem-trf-surjective-two-term-determinant-calculus). -/
def TwoTermMap.id {R : Type u} [CommRing R] (P : TwoTermComplex R) :
    TwoTermMap P P where
  neg := 𝟙 P.neg
  zero := 𝟙 P.zero
  commutes := by simp

/-- Composition of maps of two-term complexes.
Source: Stacks Project, More on Algebra, Tag 0FJI
(blueprint: lem-trf-surjective-two-term-determinant-calculus). -/
def TwoTermMap.comp {R : Type u} [CommRing R]
    {P Q S : TwoTermComplex R} (b : TwoTermMap Q S) (a : TwoTermMap P Q) :
    TwoTermMap P S where
  neg := a.neg ≫ b.neg
  zero := a.zero ≫ b.zero
  commutes := by
    change (ModuleCat.Hom.hom S.differential ∘ₗ ModuleCat.Hom.hom b.neg) ∘ₗ
      ModuleCat.Hom.hom a.neg =
      (ModuleCat.Hom.hom b.zero ∘ₗ ModuleCat.Hom.hom a.zero) ∘ₗ
        ModuleCat.Hom.hom P.differential
    simp only [LinearMap.comp_assoc, b.commutes, a.commutes]

/-- The kernel-normalized determinant map, specified by the contraction formula for the
commuting triangle in Stacks Project, Tag 0FJI. Both short-exact-sequence maps are
kernel-first. If `nzero = det(d_N)(nneg)`, the formula evaluates the inverse dual of
`γneg` by contraction with `nneg`. Thus it inserts precisely `δ_N = det(d_N)`, with
ordinary tensor symmetry and no graded sign. No assembly map or trivialization is free.
(blueprint: lem-trf-surjective-two-term-determinant-calculus) -/
def IsKernelNormalizedDeterminantMap {R : Type u} [CommRing R]
    {P Q : TwoTermComplex R} (a : TwoTermMap P Q)
    (T : twoTermDeterminant P ≃ₗ[R] twoTermDeterminant Q) : Prop :=
  ∃ (γneg :
      (Module.determinantModule R (LinearMap.ker (ModuleCat.Hom.hom a.neg)) ⊗[R]
        Module.determinantModule R (Q.neg : Type v)) ≃ₗ[R]
        Module.determinantModule R (P.neg : Type v))
    (γzero :
      (Module.determinantModule R (LinearMap.ker (ModuleCat.Hom.hom a.zero)) ⊗[R]
        Module.determinantModule R (Q.zero : Type v)) ≃ₗ[R]
        Module.determinantModule R (P.zero : Type v)),
    Module.IsDeterminantExactSequenceMap (Submodule.subtype _)
      (ModuleCat.Hom.hom a.neg) γneg ∧
    Module.IsDeterminantExactSequenceMap (Submodule.subtype _)
      (ModuleCat.Hom.hom a.zero) γzero ∧
    ∀ (nneg : Module.determinantModule R (LinearMap.ker (ModuleCat.Hom.hom a.neg)))
      (nzero : Module.determinantModule R (LinearMap.ker (ModuleCat.Hom.hom a.zero))),
      ExteriorAlgebra.map a.kernelDifferential nneg.val = nzero.val →
      ∀ (qzero : Module.determinantModule R (Q.zero : Type v))
        (φ : Module.Dual R (Module.determinantModule R (P.neg : Type v))),
        T (γzero (nzero ⊗ₜ[R] qzero) ⊗ₜ[R] φ) =
          qzero ⊗ₜ[R] ((φ.comp γneg.toLinearMap).comp (TensorProduct.mk R _ _ nneg))

/-- Existence and uniqueness of the kernel-normalized determinant map.
Source: Stacks Project, More on Algebra, Tag 0FJI, defining triangle.
(blueprint: lem-trf-surjective-two-term-determinant-calculus).

Proof: split each degreewise surjection using projectivity of the quotient. The kernel
is a direct summand of a finite projective module, hence finite projective. Injectivity
on degree -1 cycles makes its differential injective. If y is in the degree-zero kernel,
injectivity on cokernels gives y = d(x); surjectivity on degree -1 cycles supplies a cycle
z with a(z) = a(x). Thus x-z is in the kernel and d(x-z) = y.
Apply `existsUnique_determinantExactSequence` to both split sequences. The exterior map
of the kernel differential is an isomorphism of the determinant lines. Tensor γzero
with the inverse dual of γneg and reorder by ordinary symmetry. Inserting the element
corresponding to this exterior map gives an isomorphism D(Q) → D(P); take its inverse.
On local bases n of the negative kernel the inserted element is d(n) tensor n-dual.
Contracting the inverse dual of γneg yields exactly the displayed formula. Since n
and d(n) generate the local kernel lines and pure tensors span, the formula determines
the map uniquely on each finite free localization. Local equality detects global
equality, including nonconstant rank, and the zero-ring case is unique. -/
theorem existsUnique_kernelNormalizedDeterminantMap {R : Type u} [CommRing R]
    {P Q : TwoTermComplex R} (a : TwoTermMap P Q)
    [Module.Finite R P.neg] [Module.Projective R P.neg]
    [Module.Finite R P.zero] [Module.Projective R P.zero]
    [Module.Finite R Q.neg] [Module.Projective R Q.neg]
    [Module.Finite R Q.zero] [Module.Projective R Q.zero]
    (ha : a.DegreewiseSurjective) (hqa : a.QuasiIso) :
    ∃! T : twoTermDeterminant P ≃ₗ[R] twoTermDeterminant Q,
      IsKernelNormalizedDeterminantMap a T := by
  sorry

/-- The canonical determinant map attached to a degreewise-surjective quasi-isomorphism.
It is chosen from the unique map characterized by the two canonical short-exact-sequence
maps and contraction with the exterior map of the kernel differential.
Source: Stacks Project, More on Algebra, Tag 0FJI, defining triangle
(blueprint: lem-trf-surjective-two-term-determinant-calculus). -/
noncomputable def kernelNormalizedDeterminantMap {R : Type u} [CommRing R]
    {P Q : TwoTermComplex R} (a : TwoTermMap P Q)
    [Module.Finite R P.neg] [Module.Projective R P.neg]
    [Module.Finite R P.zero] [Module.Projective R P.zero]
    [Module.Finite R Q.neg] [Module.Projective R Q.neg]
    [Module.Finite R Q.zero] [Module.Projective R Q.zero]
    (ha : a.DegreewiseSurjective) (hqa : a.QuasiIso) :
    twoTermDeterminant P ≃ₗ[R] twoTermDeterminant Q :=
  Classical.choose (existsUnique_kernelNormalizedDeterminantMap a ha hqa)

/-- The identity map is degreewise surjective.
Source: Stacks Project, More on Algebra, Tag 0FJI, identity case.
(blueprint: lem-trf-surjective-two-term-determinant-calculus).
Proof: in each degree every element is its own preimage. -/
theorem TwoTermMap.id_degreewiseSurjective {R : Type u} [CommRing R]
    (P : TwoTermComplex R) : (TwoTermMap.id P).DegreewiseSurjective := by
  sorry

/-- The identity map is a two-term quasi-isomorphism.
Source: Stacks Project, More on Algebra, Tag 0FJI, identity case.
(blueprint: lem-trf-surjective-two-term-determinant-calculus).
Proof: the kernel map is the identity, and both cokernel conditions follow by taking
the same representative; the remaining difference is zero in the differential range. -/
theorem TwoTermMap.id_quasiIso {R : Type u} [CommRing R]
    (P : TwoTermComplex R) : (TwoTermMap.id P).QuasiIso := by
  sorry

/-- Composition preserves degreewise surjectivity.
Source: Stacks Project, More on Algebra, Tag 0FJL.
(blueprint: lem-trf-surjective-two-term-determinant-calculus).
Proof: lift a target element first through b and then through a, in each degree. -/
theorem TwoTermMap.comp_degreewiseSurjective {R : Type u} [CommRing R]
    {P Q S : TwoTermComplex R} (a : TwoTermMap P Q) (b : TwoTermMap Q S)
    (ha : a.DegreewiseSurjective) (hb : b.DegreewiseSurjective) :
    (TwoTermMap.comp b a).DegreewiseSurjective := by
  sorry

/-- Composition of two-term quasi-isomorphisms is a quasi-isomorphism.
Source: Stacks Project, More on Algebra, Tag 0FJL.
(blueprint: lem-trf-surjective-two-term-determinant-calculus).
Proof: the induced kernel map is the composite of the two bijections. For injectivity
on cokernels apply the condition for b, then for a. For surjectivity choose successive
representatives through b and a; their errors add after applying b. The chain-map
equation takes differential-range errors to differential-range errors. -/
theorem TwoTermMap.comp_quasiIso {R : Type u} [CommRing R]
    {P Q S : TwoTermComplex R} (a : TwoTermMap P Q) (b : TwoTermMap Q S)
    (hqa : a.QuasiIso) (hqb : b.QuasiIso) :
    (TwoTermMap.comp b a).QuasiIso := by
  sorry

/-- Kernel-normalized determinant calculus for surjective two-term quasi-isomorphisms.
Source: Stacks Project, More on Algebra, Tags 0FJI, 0FJK and 0FJL
(blueprint: lem-trf-surjective-two-term-determinant-calculus).

For every degreewise-surjective quasi-isomorphism `a`, the kernel terms are finite
projective and the kernel differential is an isomorphism.  The canonical map defined
above is the identity for the identity map, is unchanged by the displayed chain
homotopies, and is multiplicative under composition.

Proof (the node's eleven steps):
1. Split the degreewise surjections by `Module.projective_lifting_property`. Their
kernels are finite projective direct summands. Injectivity on cycles gives injectivity
of d_N. For y in N.zero, injectivity on cokernels gives y = d(x), and surjectivity on
cycles gives a cycle z with a(z) = a(x). Then d(x-z) = y with x-z in N.neg.
2. Use `Module.existsUnique_determinantExactSequence` for the kernel-first maps in
both degrees. Tensor the zero-degree map with the inverse dual of the negative-degree
map, using ordinary symmetry. The exterior map of d_N gives the kernel trivialization.
Inserting it and taking the inverse is precisely `kernelNormalizedDeterminantMap`.
3. For the identity, the kernels vanish and their determinant has empty wedge 1;
the wedge formulas give the identity.
4. The split sequences, exterior products, duals and evaluations localize, so do the
normalized maps. Use `Module.exists_standardFreeCover_of_finite_projective` to compute
in local bases. Equality after localizing at every prime detects global equality:
a nonzero difference has proper annihilator in a maximal ideal and cannot vanish there.
5. Over a local ring, `exists_common_summand_surjections` gives a common summand U
for a.neg and a'.neg. Lift h through the inverse of a.neg on U, obtaining t with a t = h.
6. Set k.neg = 1+t d and k.zero = 1+d t. The homotopy equations give a k = a'. In the
splitting ker(a.neg) plus U the negative map has triangular matrix with diagonal 1 and
(a|U) inverse times (a'|U), hence is invertible. If v is its inverse, 1-d v t is the
inverse in degree zero. The chain isomorphism k induces a kernel isomorphism c.
7. `Matrix.det_one_add_mul_comm` gives det(1+d t) = det(1+t d). Their ratio is one,
so the induced map on D(P) is the identity.
8. The kernel-first wedge formula intertwines γ for a and a' with c and k. The
exterior map of c takes the kernel differential trivialization to the other one.
Tensoring and inverse-dualizing gives equality of the normalized maps locally, hence globally.
9. For a followed by b, put N = ker a, M = ker b, L = ker(ba). In each degree the
sequence N → L → M is exact and split; lift an element of M through a to see surjectivity.
Its kernel-first determinant maps in both degrees give the corresponding map on D.
10. Choose local kernel bases n,m and lifts of m. Their images under the kernel
differentials are the corresponding zero-degree bases and lifts. The ordered wedge
formula shows the map D(M) tensor D(N) → D(L) takes δ_M tensor δ_N to δ_L.
11. In the filtration N ⊆ L ⊆ P both iterated determinant maps send local basis
wedges to n wedge lifted-m wedge lifted-s, in identical order. Tensor this equality
with its inverse dual in degree -1 and insert the trivializations from step 10.
The inverse maps compose, giving T_ba = T_b T_a. Localization detects the equality
globally. Empty wedges, characteristic two, and the zero ring require no extra sign. -/
theorem surjective_two_term_determinant_calculus {R : Type u} [CommRing R]
    {P Q : TwoTermComplex R} (a : TwoTermMap P Q)
    [Module.Finite R P.neg] [Module.Projective R P.neg]
    [Module.Finite R P.zero] [Module.Projective R P.zero]
    [Module.Finite R Q.neg] [Module.Projective R Q.neg]
    [Module.Finite R Q.zero] [Module.Projective R Q.zero]
    (ha : a.DegreewiseSurjective) (hqa : a.QuasiIso) :
    Module.Finite R (LinearMap.ker (ModuleCat.Hom.hom a.neg)) ∧
    Module.Projective R (LinearMap.ker (ModuleCat.Hom.hom a.neg)) ∧
    Module.Finite R (LinearMap.ker (ModuleCat.Hom.hom a.zero)) ∧
    Module.Projective R (LinearMap.ker (ModuleCat.Hom.hom a.zero)) ∧
    Function.Bijective a.kernelDifferential ∧
    kernelNormalizedDeterminantMap (TwoTermMap.id P)
        (TwoTermMap.id_degreewiseSurjective P) (TwoTermMap.id_quasiIso P) =
      LinearEquiv.refl (R := R) (twoTermDeterminant P) ∧
    (∀ (a' : TwoTermMap P Q) (ha' : a'.DegreewiseSurjective) (hqa' : a'.QuasiIso)
      (h : (P.zero : Type v) →ₗ[R] (Q.neg : Type v)),
      ModuleCat.Hom.hom a'.zero - ModuleCat.Hom.hom a.zero =
        ModuleCat.Hom.hom Q.differential ∘ₗ h →
      ModuleCat.Hom.hom a'.neg - ModuleCat.Hom.hom a.neg =
        h ∘ₗ ModuleCat.Hom.hom P.differential →
      kernelNormalizedDeterminantMap a ha hqa =
        kernelNormalizedDeterminantMap a' ha' hqa') ∧
    (∀ (S : TwoTermComplex R)
      [Module.Finite R S.neg] [Module.Projective R S.neg]
      [Module.Finite R S.zero] [Module.Projective R S.zero]
      (b : TwoTermMap Q S) (hb : b.DegreewiseSurjective) (hqb : b.QuasiIso),
      kernelNormalizedDeterminantMap (TwoTermMap.comp b a)
          (TwoTermMap.comp_degreewiseSurjective a b ha hb)
          (TwoTermMap.comp_quasiIso a b hqa hqb) =
        (kernelNormalizedDeterminantMap a ha hqa).trans
          (kernelNormalizedDeterminantMap b hb hqb)) := by
  sorry

end Module

end
