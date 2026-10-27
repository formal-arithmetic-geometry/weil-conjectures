## Worker report

The module `Sheaf.LinearAlgebra.SimpleRootReflectionGeneration` states
`RootPairing.simple_root_reflection_generation`, with its proof left `sorry`.
The module and declaration docstrings cite Milne, Algebraic Groups, Appendix C.11
(first assertion), printed p.610, and C.21--C.22, printed p.612. I read those
passages in the local PDF. C.11 asserts simple-reflection generation; C.21 defines
a base by its basis and integral same-sign coordinate properties; C.22 applies
the chamber results to these root systems. The docstring supplies all six steps
of the node's elementary height-descent proof. No statement correction, new node,
additional theorem, definition, or dependency repair is needed.

Hypotheses, matched individually to the node:

- A finite-dimensional real vector space is `(V : Type u) [AddCommGroup V]
  [Module ℝ V] [FiniteDimensional ℝ V]`; `u` is explicit and unrestricted.
- The bilinear form is `(B : LinearMap.BilinForm ℝ V)`; symmetry is
  `hBsymm : B.IsSymm`; positive definiteness is
  `hBpos : ∀ x : V, x ≠ 0 → 0 < B x x`. This adds no norm or topology on V.
- The root subset is `(R : Set V)`. Finiteness is `hRfinite : R.Finite`;
  exclusion of zero is `hRzero : (0 : V) ∉ R`; spanning is
  `hRspan : Submodule.span ℝ R = ⊤`.
- Reducedness is `hRline : ∀ a ∈ R,
  R ∩ {x : V | ∃ t : ℝ, t • a = x} = {a, -a}`. The displayed set is
  precisely the real line through a, with no restriction on the real scalar.
- The formula for a reflection is used literally throughout:
  `x - (2 * B x a * (B a a)⁻¹) • a`.
  The permutation condition is `hRreflect`, using `Set.BijOn` of this function
  from R to R. It asserts both preservation and bijectivity, as the node says.
- Crystallographic integrality is `hRint : ∀ a ∈ R, ∀ b ∈ R,
  ∃ n : ℤ, 2 * B b a * (B a a)⁻¹ = (n : ℝ)`.
- The simple-root subset and inclusion are `(D : Set V) (hDR : D ⊆ R)`.
- D being a real basis is encoded by `(e : Module.Basis D ℝ V)` and
  `he : ∀ a : D, e a = (a : V)`. The latter ensures that the basis vectors
  are the elements of D themselves; it is not a choice of unrelated vectors.
  Choosing this basis data adds no mathematical hypothesis to D being a basis.
- The integral and same-sign coordinate properties are `hDcoords`: for each
  `b ∈ R` it supplies `n : D → ℤ`, equality `(n a : ℝ) = e.repr b a` for
  every a, and the disjunction that every coefficient is nonnegative or every
  coefficient is nonpositive. The coefficients are the actual basis coordinates.

Conclusions, matched individually:

- For every `b ∈ R`, the first conjunct supplies `w : List (V ≃ₗ[ℝ] V)`.
  For every factor `g ∈ w`, there exists `a ∈ D` such that, for every x,
  `g x = x - (2 * B x a * (B a a)⁻¹) • a`.
  It then asserts at every vector that `w.prod` is the reflection with root b.
  Thus w is exactly a finite product of simple-root reflections in the real
  general linear group; it is not merely a word in permutations of R.
- The second conjunct equates `Subgroup.closure` of the root reflections and
  `Subgroup.closure` of the simple-root reflections, both subgroups of
  `V ≃ₗ[ℝ] V`. Each generating set is specified directly by the reflection
  formula at every vector and the appropriate membership in R or D.
  Pointwise equality uniquely determines a linear equivalence. No unspecified
  reflection map, auxiliary action, arbitrary family of automorphisms, or
  stronger existence assumption is introduced. The raw formula is linear and
  involutive for each root because B(a,a) is positive, so these generating sets
  include the reflection for every indicated root. The graph description
  avoids adding another definition of Mathlib's reflection notion.
- Empty products are allowed because lists include `[]`, whose product is 1.
  Neither the space, the root set, the base, nor the word has a nonemptiness
  hypothesis. The empty root system is therefore included.

Dependency declarations and other Mathlib interfaces:

- The sole statement dependency, `def-weil-vector-space-dimension`, records
  `Module.finrank` in `Mathlib.LinearAlgebra.Dimension.Finrank`. I read its full
  signature and docstring: for finite-dimensional vector spaces it is the
  dimension, while its general infinite-rank convention is immaterial here.
  The recorded module is imported publicly. No numerical dimension occurs in
  this node; finite dimension itself is Mathlib's `FiniteDimensional`, imported
  from `Mathlib.LinearAlgebra.FiniteDimensional.Defs` (the `Module.Finite`
  abbreviation). The finite-dimension binder is retained even though the finite
  spanning hypothesis also implies it.
- `LinearMap.BilinForm` and `LinearMap.BilinForm.IsSymm` are the Mathlib bilinear
  and symmetric-form interfaces; the latter is available from
  `Mathlib.LinearAlgebra.BilinearForm.Properties`.
- `Module.Basis` and its `repr` give the actual basis and finite-support real
  coordinates. `Set.BijOn`, `Submodule.span`, `Subgroup.closure`, `LinearEquiv`,
  and `List.prod` retain their standard Mathlib meanings. Subgroup closure is
  imported from `Mathlib.Algebra.Group.Subgroup.Lattice`; list products are
  exposed through `Mathlib.Algebra.BigOperators.Group.List.Defs`.
- There are no proof dependencies in the node and hence no proof-only imports.

Edge cases checked before writing and again against the compiled signature:

- If R is empty, `hRspan` makes V zero, and `hDR` makes D empty. The word
  assertion has no root to quantify over; both closure generator sets are empty,
  and both subgroups are the identity. A basis indexed by the empty set is
  admitted on the zero space, with no `Nontrivial V` requirement.
- In rank one, for R = {a,-a} and D = {a}, the two root reflections coincide;
  the positive and negative coordinates satisfy the two branches of hDcoords.
- The empty word is available and means the identity; no positive length is
  required. Equality is on all of V, so the identity and every product are
  compared as linear automorphisms, including when V is zero.
- Positivity is imposed only for nonzero vectors, hence is valid in the zero
  space. Every denominator B(a,a) used for a root is nonzero by hRzero/hBpos.
- D need not be separately assumed finite: it is a subset of finite R and its
  basis property already includes finite supports. Coordinate sign disjunctions
  therefore have their usual meaning, including the empty indexing set.
- There is no unit-statement issue, counterexample, or STATEMENT-DISPUTED flag.

Searches for an existing statement or notion:

- `msearch.py` / LeanFinder, query: "A finite reduced crystallographic root
  system in a real vector space with a positive definite symmetric bilinear
  form has its reflection group generated by reflections in a sign coherent
  basis". Eight hits included `RootPairing.Base.induction_reflect`,
  `RootPairing.Base.IsPos.induction_on_reflect`, `RootPairing.nonempty_base`,
  and `RootPairing.reflection_mem_weylGroup`. I read the relevant source
  signatures in RootSystem/Base.lean and RootSystem/WeylGroup.lean. These
  require root/coroot pairing data and do not state the raw bilinear-form result.
- `msearch.py` / Loogle, `Module.reflection, LinearMap.BilinForm.PosDef`:
  zero hits, with the diagnostic that the second identifier is unknown.
  A follow-up `Module.reflection` returned twelve hits; I read the definition
  and docstring in Mathlib/LinearAlgebra/Reflection.lean. Its normalized linear
  functional interface is not an existing statement of simple-root generation.
- `msearch.py` / grep, `def reflection|theorem.*reflection|def.*PosDef`,
  restricted to LinearAlgebra: 25 hits, including `Module.reflection` and
  `RootPairing.reflection`; no matching raw-form generation theorem.
- Direct `rg` over Mathlib searched reflection definitions and
  `simple.*reflection|reflection.*simple` in the root-system modules.
  The closest induction and Weyl-group definitions have the additional
  root/coroot-pairing interface just described.
- Direct `rg` over `lean/WeilConjectures` and `lean/Sheaf` searched
  `simple.*reflection|reflection.*simple`, `bilinForm.*[Rr]eflection`,
  `[Rr]eflection.*[Bb]ilin`, and the item's id. The nearby
  `RootPairing.exists_simple_base_reflection_orbits` in
  `Sheaf.LinearAlgebra.RationalReflectionSimpleBaseOrbits` was read in full:
  it concerns rational reflection data, constructs a base, and expresses root
  orbits. It does not state this fixed-real-base reflection-product theorem.
  Existing group-scheme consumers only mention this node in proof docstrings.
- `tools/blueprint_refs.py search reflection` and `rg` of DAG statements for
  bilinear-form reflections found no separate canonical raw-form construction
  that needs to be imported or duplicated. The full prospective declaration
  name was also checked against Mathlib, WeilConjectures, Sheaf, and the
  recorded upstream-name index, with no clash.

Validation: `scompile.py Q38 lem-sfb-simple-root-reflection-generation` compiled
this delivered module both as its sandbox probe and with its actual library
module name. Both passed with no errors or warnings. Every universe and variable
is explicit; `set_option autoImplicit false` is also in the source. The only
postponed proof is the named theorem for this DAG node. Only the node's `lean`
field is changed, with the statement copied verbatim from the theorem signature.

## Second reading by Q38

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
