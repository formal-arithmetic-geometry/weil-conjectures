/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Sheaf.LinearAlgebra.ProjectiveDeterminantModule
public import WeilConjectures.RingTheory.FiniteProjectiveStandardFreeCover
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Sheaf.LinearAlgebra.GenericExteriorPowerLocalization
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.Topology.GlueSheavesOfModules
import Sheaf.AlgebraicGeometry.CoherentFiniteType
import Sheaf.RingTheory.FiniteProjectiveOfStandardCover
import WeilConjectures.LinearAlgebra.ExteriorTopDirectSum
import Mathlib.RingTheory.Localization.BaseChange
import Sheaf.RingTheory.CoverModuleExact

/-!
# Determinants of exact sequences of finite projective modules

Source: Stacks Project, More on Algebra, Tag 0FJB, both constructions, and the
preceding determinant definition and `remark-determinant-as-socle`.
(blueprint: lem-trf-projective-determinant-exact-sequence)

The determinant is the explicit exterior-algebra socle. The statements identify it with
local top wedges, assert invertibility and the zero-module normalization, and characterize
the unique exact-sequence isomorphism, its wedge formula and localization compatibility.
-/

@[expose] public section

set_option autoImplicit false
universe u v w z a b c d

open scoped TensorProduct

namespace Module

/-- The defining formula for the determinant isomorphism, using arbitrary exterior lifts.
It is the second construction of Stacks Project, Tag 0FJB; the first construction is its
pure-wedge formula. The predicate specifies the entire map, not just a generator.
(blueprint: lem-trf-projective-determinant-exact-sequence) -/
def IsDeterminantExactSequenceMap {R : Type u} [CommRing R]
    {U : Type v} [AddCommGroup U] [Module R U]
    {V : Type w} [AddCommGroup V] [Module R V]
    {W : Type z} [AddCommGroup W] [Module R W]
    (i : U →ₗ[R] V) (p : V →ₗ[R] W)
    (e : (determinantModule R U ⊗[R] determinantModule R W) ≃ₗ[R]
      determinantModule R V) : Prop :=
  ∀ (x : determinantModule R U) (y : determinantModule R W)
    (t : ExteriorAlgebra R V), ExteriorAlgebra.map p t = y.val →
    (e (x ⊗ₜ[R] y)).val = ExteriorAlgebra.map i x.val * t

/-- The socle determinant of a free module is its top exterior power, with the identity
as underlying map in the exterior algebra. Source: Stacks Project, determinant definition
and `remark-determinant-as-socle` preceding Tag 0FJB.
(blueprint: lem-trf-projective-determinant-exact-sequence)

Proof: expand an element in the exterior basis. Multiplication by every basis vector
kills precisely the coefficient terms already containing all basis vectors. Thus only
top degree remains, and every top wedge is annihilated. This identifies the submodules
by their common inclusion, giving the unique equivalence. For an empty basis the whole
exterior algebra is degree zero; for a zero ring all inclusions have zero source and target. -/
theorem determinantModule_topExterior {R : Type u} [CommRing R]
    {E : Type v} [AddCommGroup E] [Module R E] (n : ℕ) (_b : Module.Basis (Fin n) R E) :
    ∃! e : determinantModule R E ≃ₗ[R] (⋀[R]^n E),
      ∀ x : determinantModule R E, (e x).val = x.val := sorry

/-- The explicit socle is an invertible module: finite projective and free of rank one
on a finite standard cover. Source: Stacks Project, determinant definition before Tag 0FJB.
(blueprint: lem-trf-projective-determinant-exact-sequence)

Proof: use the finite standard free cover of E. Localization commutes with the socle
condition, because annihilation can be tested on finitely many generators and their
finitely many denominators can be cleared simultaneously. The preceding exterior-basis
calculation identifies each localized socle with the top wedge, free on the full basis
wedge. The standard-cover finite-projectivity criterion proves finite projectivity.
The localized inclusions identify overlap maps with top exterior powers of the identity,
hence with the usual change-of-basis maps. They satisfy the cocycle condition, so this is
exactly the determinant obtained by gluing, independently of the cover and its refinement. -/
theorem determinantModule_finite_projective {R : Type u} [CommRing R]
    {E : Type v} [AddCommGroup E] [Module R E] [Module.Finite R E]
    [Module.Projective R E] :
    Module.Finite R (determinantModule R E) ∧ Module.Projective R (determinantModule R E) ∧
      ∃ (k : ℕ) (f : Fin k → R), Ideal.span (Set.range f) = ⊤ ∧
        ∀ j : Fin k, Nonempty (LocalizedModule.Away (f j) (determinantModule R E) ≃ₗ[
          Localization.Away (f j)] Localization.Away (f j)) := sorry

/-- Localization of the determinant is induced by the canonical exterior-algebra map.
Its inclusion formula uniquely determines the localization map; this also specifies all
transition identifications on overlaps. Source: Stacks Project, determinant construction
before Tag 0FJB and its first proof; Algebra, Tag 0C6F.
(blueprint: lem-trf-projective-determinant-exact-sequence)

Proof: choose finitely many generators of E. A vector in the localized exterior socle
has a denominator, by exterior-algebra localization; its annihilation relations against
the chosen generators can be cleared with a common denominator. It therefore comes from
the original socle. The equality criterion is inherited from exterior-algebra localization.
The exterior-basis computation on a standard free cover gives the same assertion and
identifies it with localization of top wedges. Injectivity of the target inclusion gives
uniqueness. Applying the inclusion formula twice proves compatibility with further
localization and the overlap cocycle equations. -/
theorem determinantModule_localization {R : Type u} {A : Type a}
    [CommRing R] [CommRing A] [Algebra R A] (S : Submonoid R) [IsLocalization S A]
    {E : Type v} [AddCommGroup E] [Module R E] [Module.Finite R E]
    [Module.Projective R E] {F : Type b} [AddCommGroup F] [Module A F]
    [Module R F] [IsScalarTower R A F] (f : E →ₗ[R] F) [IsLocalizedModule S f] :
    ∃! q : determinantModule R E →ₗ[R] determinantModule A F,
      (∀ x : determinantModule R E,
        (q x).val = ExteriorAlgebra.scalarExtensionMap f x.val) ∧
      IsLocalizedModule S q := sorry

/-- The determinant of a zero module is R, with the usual degree-zero normalization.
Source: Stacks Project, determinant definition before Tag 0FJB, rank-zero factor.
(blueprint: lem-trf-projective-determinant-exact-sequence)

Proof: a zero module has the empty basis. Its exterior algebra is its degree-zero copy
of R, and its socle is all of that algebra. Restrict the degree-zero equivalence to the
socle. Its inverse is the structure map, which also determines it uniquely. This applies
to every subsingleton module, including modules over the zero ring. -/
theorem determinantModule_zero {R : Type u} [CommRing R]
    {E : Type v} [AddCommGroup E] [Module R E] [Subsingleton E] :
    ∃! e : determinantModule R E ≃ₗ[R] R,
      ∀ r : R, (e.symm r).val = algebraMap R (ExteriorAlgebra R E) r := sorry

/-- A finite-projective short exact sequence has the unique determinant isomorphism
specified by the exterior-lift formula. Source: Stacks Project, Tag 0FJB, both proofs.
(blueprint: lem-trf-projective-determinant-exact-sequence)

Proof, step 1: lift id_W through p by projectivity to obtain a section s. The map
U × W → V, (u,w) ↦ i(u)+s(w), is an isomorphism: v-s(p(v)) lies in the image of i and
injectivity gives a unique preimage. Its inverse formulas localize as well.
Step 2: refine finite standard free covers of U and W by pairwise products. The top
exterior powers of these charts glue, using exterior localization and the cocycle equations
of the induced exterior maps. The affine tilde/Gamma equivalence and sheaf gluing identify
them with an invertible module, which the socle calculation identifies with determinantModule.
On a zero overlap the identification is unique, so differing chart ranks cause no problem.
Step 3: invert the top-exterior direct-sum isomorphism and apply the exterior power of the
split isomorphism. On wedges this concatenates the i(u)'s followed by the s(w)'s.
Step 4: any other lift differs by i(a). Expanding a changed wedge gives at least r+1 factors
from a free rank-r module, and is zero by alternation. Thus the map is independent of
lifts and the splitting, including in characteristic two. Multilinearity makes its formula
independent of bases, and the exterior and tensor localization formulas make the local
maps agree on overlaps and refinements.
Step 5: the standard-cover exactness theorem glues the local maps and their inverses.
Their composites are identities since they are so on every chart. The second construction
says exactly that the result multiplies i(x) by any exterior lift of y. Such lifts exist
since p is surjective. Pure tensors span, so this formula determines the map uniquely.
Step 6: empty wedges give the left and right unit formulas, and when both ranks vanish
the map is multiplication R ⊗ R → R. Over the zero ring it is the unique zero-module
isomorphism. Localization of the identical spanning formula proves the final compatibility. -/
theorem existsUnique_determinantExactSequence {R : Type u} [CommRing R]
    {U : Type v} [AddCommGroup U] [Module R U] [Module.Finite R U] [Module.Projective R U]
    {V : Type w} [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Projective R V]
    {W : Type z} [AddCommGroup W] [Module R W] [Module.Finite R W] [Module.Projective R W]
    (i : U →ₗ[R] V) (p : V →ₗ[R] W) (hi : Function.Injective i)
    (hp : Function.Surjective p) (hex : Function.Exact i p) :
    ∃! e : (determinantModule R U ⊗[R] determinantModule R W) ≃ₗ[R]
      determinantModule R V, IsDeterminantExactSequenceMap i p e := sorry

/-- The first construction's formula for arbitrary tuples and arbitrary lifts. In particular
it holds for every choice of the displayed bases and includes both empty-tuple cases.
Source: Stacks Project, Tag 0FJB, first proof.
(blueprint: lem-trf-projective-determinant-exact-sequence)

Proof: the top-exterior identification puts the two pure wedges in the determinant socles.
The wedge of the lifts in the full exterior algebra maps under p to the quotient wedge,
so the second-construction formula applies. Multiplicativity of the exterior map and
concatenation of wedge products give the displayed result. Expanding changes of lifts
kills all extra terms by rank and alternation; expanding changes of bases gives the same
coefficients on both sides. The argument includes degree zero and characteristic two. -/
theorem determinantExactSequence_wedge {R : Type u} [CommRing R]
    {U : Type v} [AddCommGroup U] [Module R U]
    {V : Type w} [AddCommGroup V] [Module R V]
    {W : Type z} [AddCommGroup W] [Module R W]
    (i : U →ₗ[R] V) (p : V →ₗ[R] W) (hex : Function.Exact i p)
    (e : (determinantModule R U ⊗[R] determinantModule R W) ≃ₗ[R]
      determinantModule R V) (he : IsDeterminantExactSequenceMap i p e)
    (r s : ℕ) (_bU : Module.Basis (Fin r) R U) (_bW : Module.Basis (Fin s) R W)
    (u : Fin r → U) (w : Fin s → W) (t : Fin s → V) (ht : ∀ j, p (t j) = w j)
    (x : determinantModule R U) (hx : x.val = ExteriorAlgebra.ιMulti R r u)
    (y : determinantModule R W) (hy : y.val = ExteriorAlgebra.ιMulti R s w) :
    (e (x ⊗ₜ[R] y)).val =
      ExteriorAlgebra.ιMulti R (r + s) (Fin.append (fun j ↦ i (u j)) t) := sorry

/-- The canonical determinant isomorphism commutes with every further localization, using
any localized models of the modules. The q maps are precisely the canonical maps of
`determinantModule_localization`, specified by their exterior inclusion formulas; e and e'
are precisely the uniquely characterized maps above, rather than arbitrary isomorphisms.
Source: Stacks Project, Tag 0FJB, first and second constructions on localization charts.
(blueprint: lem-trf-projective-determinant-exact-sequence)

Proof: exterior-algebra localization preserves multiplication and commutes with the
exterior maps induced by i and p. For x and y choose an exterior lift t of y through p.
Its localized image lifts the localized y through p'. Applying the two defining formulas
therefore gives equal exterior-algebra elements. The determinant inclusion is injective,
so the outputs agree. The equality on pure tensors is the tensor localization square,
since pure tensors span and localization extends their maps uniquely. Iterating this
square proves compatibility with further localization, hence with all chart refinements. -/
theorem determinantExactSequence_localization {R : Type u} {A : Type a}
    [CommRing R] [CommRing A] [Algebra R A] (S : Submonoid R) [IsLocalization S A]
    {U : Type v} [AddCommGroup U] [Module R U]
    {V : Type w} [AddCommGroup V] [Module R V]
    {W : Type z} [AddCommGroup W] [Module R W]
    {U' : Type b} [AddCommGroup U'] [Module A U'] [Module R U'] [IsScalarTower R A U']
    {V' : Type c} [AddCommGroup V'] [Module A V'] [Module R V'] [IsScalarTower R A V']
    {W' : Type d} [AddCommGroup W'] [Module A W'] [Module R W'] [IsScalarTower R A W']
    (fU : U →ₗ[R] U') [IsLocalizedModule S fU]
    (fV : V →ₗ[R] V') [IsLocalizedModule S fV]
    (fW : W →ₗ[R] W') [IsLocalizedModule S fW]
    (i : U →ₗ[R] V) (p : V →ₗ[R] W) (hp : Function.Surjective p)
    (i' : U' →ₗ[A] V') (p' : V' →ₗ[A] W')
    (hi' : ∀ x : U, i' (fU x) = fV (i x))
    (hp' : ∀ y : V, p' (fV y) = fW (p y))
    (e : (determinantModule R U ⊗[R] determinantModule R W) ≃ₗ[R]
      determinantModule R V) (he : IsDeterminantExactSequenceMap i p e)
    (e' : (determinantModule A U' ⊗[A] determinantModule A W') ≃ₗ[A]
      determinantModule A V') (he' : IsDeterminantExactSequenceMap i' p' e')
    (qU : determinantModule R U →ₗ[R] determinantModule A U')
    (qV : determinantModule R V →ₗ[R] determinantModule A V')
    (qW : determinantModule R W →ₗ[R] determinantModule A W')
    (hqU : ∀ x, (qU x).val = ExteriorAlgebra.scalarExtensionMap fU x.val)
    (hqV : ∀ x, (qV x).val = ExteriorAlgebra.scalarExtensionMap fV x.val)
    (hqW : ∀ x, (qW x).val = ExteriorAlgebra.scalarExtensionMap fW x.val) :
    ∀ (x : determinantModule R U) (y : determinantModule R W),
      qV (e (x ⊗ₜ[R] y)) = e' (qU x ⊗ₜ[A] qW y) := sorry

end Module
