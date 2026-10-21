## Worker report

The node is exactly the existing theorem `LinearMap.trace_eq_add_of_exact` in
`WeilConjectures.RingTheory.TateResidue.FinitePotent` (source lines 38–66).
I read its complete signature, docstring and proof, and read the current live
source through `scompile.py --source WeilConjectures.RingTheory.TateResidue.FinitePotent`.
The delivery changes only the item's `lean` field, setting `existing: true`;
there is no new module, definition, postponed theorem, or statement correction.
The recorded signature is copied verbatim from `theorem` through `:=`, including
the source's `open LinearMap` spelling of ordinary trace.

Hypothesis and conclusion correspondence (A=M₁, B=M₂, C=M₃):

- The ground field k is `{k : Type*} [Field k]`.
- Each vector space is a type M₁, M₂, M₃ with `[AddCommGroup Mᵢ] [Module k Mᵢ]`.
- Finite dimension of each of A, B, C is `[FiniteDimensional k Mᵢ]` for all three i.
- The two linear arrows are `(i : M₁ →ₗ[k] M₂)` and `(q : M₂ →ₗ[k] M₃)`.
- Injectivity is `(hi : Function.Injective i)`.
- Surjectivity is `(hq : Function.Surjective q)`.
- Image equals kernel is `(hex : Function.Exact i q)`: for every b this says
  `q b = 0 ↔ b ∈ Set.range i`, precisely membership equivalence for im(i)=ker(q).
  I read the definition and its linear-map interpretation in
  `Mathlib/Algebra/Exact/Basic.lean`.
- The three endomorphisms are `(g₁ : Module.End k M₁)`, `(g₂ : Module.End k M₂)`,
  `(g₃ : Module.End k M₃)`.
- The first commutation identity is `(h₁ : g₂ ∘ₗ i = i ∘ₗ g₁)`.
- The second is `(h₃ : q ∘ₗ g₂ = g₃ ∘ₗ q)`.
- The conclusion is `trace k M₂ g₂ = trace k M₁ g₁ + trace k M₃ g₃`.
  Here `trace` is Mathlib's `LinearMap.trace`, the ordinary finite-basis trace.

Dependency declarations read and used:

- `def-weil-finite-dimensional-subspace` has Mathlib match `FiniteDimensional`
  in `Mathlib.LinearAlgebra.FiniteDimensional.Defs`, lines 73–76. It abbreviates
  `Module.Finite K V`, exactly existence of a finite spanning family over a field.
- `def-weil-endomorphism-trace` has match `LinearMap.trace` in
  `Mathlib.LinearAlgebra.Trace`, lines 75–77. The declaration's basis-independent
  trace and `LinearMap.trace_eq_matrix_trace` (lines 91–95) are the node's ordinary
  matrix trace; all three spaces here are finite free, so its otherwise-zero
  convention outside that domain is irrelevant.
- The recorded proof plan's `lem-pc-finite-dimensional-trace-cyclic` has Mathlib
  match `LinearMap.trace_comp_comm'`, `Mathlib.LinearAlgebra.Trace`, lines 265–269.
  I read the surrounding finite/free assumptions and the entire signature.
- `lem-weil-pbc-vector-space-projective` uses `Module.Free.of_divisionRing`
  (`Mathlib.LinearAlgebra.Basis.VectorSpace`, lines 155–157) and
  `Module.Projective.of_free` (`Mathlib.Algebra.Module.Projective`, lines 161–162).
- `def-weil-pbc-projective-module` records `Module.Projective` in
  `Mathlib.Algebra.Module.Projective`. I read its docstring and signature at
  lines 66–74 and the lifting property `Module.projective_lifting_property`
  at lines 90–92.

No private copy of these notions is introduced. The reused theorem already
imports Mathlib and proves the same splitting/cyclic-trace argument as the node:
choose a section s and a preliminary retraction r₀, correct the latter to
r=r₀(1−sq), obtain ri=1 and ir+sq=1, expand the middle trace, cycle both
summands, then apply the intertwining identities. The section need not commute
with the endomorphisms.

Source checked: the locally supplied Tate PDF, §1, pp. 149–150, (T1) and (T2).
(T1) identifies finite-dimensional trace with ordinary trace; (T2) is additivity
for an invariant subspace and quotient. Injectivity and exactness identify A
with im(i), and surjectivity identifies C with B/im(i); the commutation identities
identify their induced endomorphisms. Thus the node is precisely this
finite-dimensional exact-sequence formulation, with no omitted source assumption.

Edge cases checked mathematically before recording:

- A=0: q is an isomorphism and the conclusion is trace invariance under that
  isomorphism, plus zero trace on the zero space.
- C=0: i is an isomorphism, giving the analogous formula.
- All three spaces zero: both sides vanish.
- No characteristic restriction: finite-dimensional ordinary trace and cyclicity
  work over every field, including positive characteristic.
- A nonzero nilpotent 2×2 Jordan block preserving the first coordinate has no
  invariant complement. The theorem still applies (both diagonal traces and the
  middle trace vanish); it imposes no invariant-splitting hypothesis.
- The source's independent `Type*` binders permit distinct universe levels for
  k, A, B, C; no equality of universes or nonzero-space assumption was added.

Searches made with `msearch.py NN lem-pc-finite-dimensional-trace-exact`:

- `leanfinder`, query “Trace is additive on a short exact sequence of finite
  dimensional vector spaces with compatible endomorphisms”: eight results,
  including `LinearMap.trace_comp_comm'`, cycle lemmas and direct-sum formulas;
  no exact-sequence theorem returned by the Mathlib service.
- `leansearch`, same query: eight results, including `Matrix.trace_add`,
  `LinearMap.trace_prodMap'` and sums of invariant-subspace traces; no full match.
- `loogle`, query `LinearMap.trace, Function.Exact`: zero results.
- `grep`, query `trace.*(exact|quotient)|trace_comp_comm|trace_add` restricted to
  `LinearAlgebra`: nine hits, cyclic-trace and matrix-additivity declarations.
- `rg` over project `lean/WeilConjectures` with
  `trace_eq_add_of_exact|trace.*(exact|quotient)` located the exact theorem at
  `RingTheory/TateResidue/FinitePotent.lean:39` and its uses. It also located the
  more general finite-free-ring theorem `LinearMap.trace_eq_trace_add_trace_of_exact`
  in `WeilConjectures.Mathlib.LinearAlgebra.Trace`; the field theorem is the
  exact match and is the node's already-listed candidate.
- `rg` over `lean/WeilConjectures` for the item id returned no hits.
- `rg` over `lean/Sheaf` with the trace/exact-sequence pattern found references
  in `RingTheory/TateResidue/FinitePotentTraceCalculus.lean` and unrelated trace
  modules, with no replacement for the exact upstream declaration.

No STATEMENT-DISPUTED flag or dependency fault. The example
`Sheaf/CategoryTheory/CompactObject.lean` is currently a withdrawn, empty module;
this existing-declaration delivery does not need a new module header.

Validation: the scratch-only server probe imports the recorded module, checks
`@LinearMap.trace_eq_add_of_exact` with printed universes, and prints its axioms.
The probe passed without warnings and printed independent universes for all
four types. Its axiom output is exactly `[propext, Classical.choice, Quot.sound]`,
with no `sorryAx`. The prescribed dry run also checks the existing declaration
on the server and runs the maintainer preflight. No scratch module is delivered.

## Second reading by NN

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
