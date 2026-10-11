## Worker report

The module `Sheaf.FieldTheory.GeometricallyReducedExtensionSeparable` states
`Algebra.isSeparableExtension_of_forall_isReduced_tensorProduct` with a `sorry` proof.
No definitions, dependency modules, new nodes, or statement corrections are needed.
The item's node copy changes only `lean`.

Hypothesis and conclusion correspondence:

- A prime number p: `(p : ℕ) [Fact p.Prime]`.
- A field k of characteristic p: `(k : Type u) [Field k] [CharP k p]`.
- A field extension K/k: `(K : Type v) [Field K] [Algebra k K]`. This uses the
  `Algebra` match of `def-pc-field-extension`, with its map `algebraMap k K`.
- Every field extension L/k: `∀ (L : Type (max u v w)) [Field L] [Algebra k L]`
  in `hred`. All field and algebra instances are universally quantified; no
  finiteness, algebraicity, perfectness, or characteristic restriction on L is added.
  Universes u, v, w are explicitly bound. The test universe dominates that of k
  and K, so it includes lifted copies of k and its algebraic closure and the
  p-th-root subfield used in the proof. It is not an independent smaller universe
  that can make the hypothesis vacuous. As usual, w is arbitrary; smaller
  carriers can be lifted into this test universe.
- The ring K tensor L: `K ⊗[k] L`, Mathlib's `TensorProduct` used by
  `def-weil-vector-space-scalar-extension`, in the exact order in this item.
  `Mathlib.RingTheory.TensorProduct.Basic` supplies the canonical commutative
  ring structure, not extra data. Its `Algebra.TensorProduct.tmul_mul_tmul`
  states the stipulated multiplication and `Algebra.TensorProduct.one_def`
  gives the stipulated unit `1 ⊗ 1`.
- Reducedness, meaning no nonzero nilpotents: `IsReduced (K ⊗[k] L)` in `hred`.
- Conclusion (2), every finitely generated subextension is separably generated:
  `Algebra.IsSeparableExtension k K`, imported from
  `Sheaf.FieldTheory.SeparableExtension` (dependency
  `def-weil-pbc-separable-field-extension`). The definition, read in full, is
  `∀ F : IntermediateField k K, F.FG → IsSeparablyGenerated k F`.
  `Algebra.IsSeparablyGenerated` in that same module asks for a set-indexed
  transcendence basis and `Algebra.IsSeparable (IntermediateField.adjoin k s) K`.
  This is the general, potentially transcendental notion, rather than merely
  Mathlib's algebraic separability predicate on K/k.

Dependency signatures and docstrings were read: `Algebra` in
`Mathlib.Algebra.Algebra.Defs`; `TensorProduct` in
`Mathlib.LinearAlgebra.TensorProduct.Defs` (re-exported through the dependency's
recorded `Mathlib.LinearAlgebra.TensorProduct.Basic`); and both predicates in
`Sheaf.FieldTheory.SeparableExtension`. Mathlib's tensor ring operations were
also read in `Mathlib.RingTheory.TensorProduct.Basic`.

Edge cases checked before writing: p = 0 or 1 is excluded by primality as the
node requires; p = 2 is admitted. K = k and L = k are admitted. The base
intermediate field with an empty finite generating set is included by `F.FG`;
empty transcendence bases for algebraic extensions are allowed. No finite degree
or finite generation condition is imposed on K. Infinite and transcendental
extensions and arbitrary-sized bases remain included. Nontriviality follows
from `Field`, so no unintended zero-field cases arise. The test universe includes
an algebraic closure and k^{1/p}, as required by the source proof.

Sources checked: the local `literature/stacks-project/algebra.tex` was absent,
so the source was read on the official Stacks website:
https://stacks.math.columbia.edu/tag/030W (Lemma 10.44.2, (4) => (3) => (2) => (1))
and https://stacks.math.columbia.edu/tag/030S (Definition 10.43.1).
The declaration docstring carries all five steps of the node's proof and names
the dependencies used at each step. No mathematical statement fault was found.

Searches for existing declarations (all msearch calls used group M1 and this item):

- LeanFinder query: `A field extension in characteristic p whose tensor product
  with every field extension is reduced is separable: every finitely generated
  intermediate field is separably generated`. Eight hits, including geometric
  reducedness, tensor reducedness after algebraic field extensions, and
  formally unramified algebraic separability. None states this implication to
  the recorded general separability predicate.
- Loogle query: `Algebra.IsGeometricallyReduced, IsTranscendenceBasis`.
  Zero hits.
- LeanSearch query: `geometrically reduced field extension implies every
  finitely generated intermediate field is separably generated`.
  Service unavailable (Internal Server Error); recorded without a verdict.
- Mathlib grep through msearch:
  `geometricallyReduced|isGeometricallyReduced|IsSeparableExtension|030W`.
  Twenty hits. The 030W theorem in `FieldTheory.SeparablyGenerated` proves
  (2) => (1) in the finitely generated case, not this implication.
  The pinned `IsGeometricallyReduced` definition uses algebraic-closure
  residue-field base changes and its module lists arbitrary field base change
  as a TODO; it is not substituted for the node's written universal hypothesis.
- Project and source `rg -n 'geometrically.*reduced|IsSeparableExtension'`
  over `lean/Sheaf/FieldTheory` and the source `WeilConjectures` found the
  existing separability predicates and related finite-extension lemmas, plus
  scheme geometry results. None duplicates this statement.
- Source `grep -rn 'lem-weil-pbc-geometrically-reduced-extension-separable'`
  over `WeilConjectures` returned no hits.
- Proposed full name `isSeparableExtension_of_forall_isReduced_tensorProduct`
  was searched with rg in `dag/lean_names_upstream.json`, `lean/Sheaf`,
  Mathlib and `WeilConjectures`: no hits.

Server validation: `scompile.py` compiled the 58-line module successfully in
1.4 seconds, exit code 0, with no compiler warnings or errors.

## Second reading by M1

I independently read the item node, its delivered module, all three statement
dependency nodes and their recorded declarations, and the source definitions.
The local Stacks checkout is absent. I read the actual `algebra.tex` source at
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex,
labels `lemma-characterize-separable-field-extensions`,
`definition-geometrically-reduced`, and `definition-separable-field-extension`,
as well as the official rendered tags
https://stacks.math.columbia.edu/tag/030W,
https://stacks.math.columbia.edu/tag/030S, and
https://stacks.math.columbia.edu/tag/030O.
The source assumes only a field extension in positive characteristic here.
There are no standing finite generation, algebraicity, or perfectness assumptions.

Object, hypothesis and conclusion checklist (all PASS):

- Prime p: `(p : ℕ) [Fact p.Prime]`. This says exactly that p is prime;
  the positive characteristic in 030W is automatically prime for fields.
- Base field k, characteristic p: `(k : Type u) [Field k] [CharP k p]`.
  These supply exactly the base and characteristic in the node.
- Extension K/k: `(K : Type v) [Field K] [Algebra k K]`. I opened
  `Mathlib.Algebra.Algebra.Defs`, `class Algebra`: its data includes the
  unital ring map `algebraMap k K`. Between fields this map is injective.
  This is the recorded `def-pc-field-extension` match, with arbitrary u and v.
- All test extensions L/k: `hred : ∀ (L : Type (max u v w)) [Field L]
  [Algebra k L], ...`. Both structures are universally bound inside hred;
  the theorem requires no special choice of L or compatibility beyond its
  k-algebra structure. The test universe dominates u and v. Lifted copies
  of k, an algebraic closure of k and its p-root subfield are included even
  at w = 0; the hypothesis is never vacuous from a smaller test universe.
  The statement is polymorphic in w. Testing in this dominating universe
  suffices for the source's condition: a nilpotent in a tensor product with
  any larger extension uses finitely many coefficients, contained in a
  finitely generated subfield admitting a carrier in that universe; inclusion
  of that subfield induces an injective tensor map over the field k.
- Tensor ring: `K ⊗[k] L`, in the node's factor order. I opened
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, the recorded TensorProduct's
  defining quotient, and `Mathlib.RingTheory.TensorProduct.Basic`.
  `Algebra.TensorProduct.tmul_mul_tmul` gives exactly the displayed
  multiplication, and `one_def` gives `1 ⊗ 1`. The scalar-extension
  dependency records the opposite order using tensor commutativity, so this
  use is the same tensor product, not a new construction. Tag 030S also uses
  the opposite order, which is equivalent by that commutativity isomorphism.
- Reducedness: `IsReduced (K ⊗[k] L)`. I read its class in
  `Mathlib.Algebra.GroupWithZero.Basic`: every nilpotent is zero, precisely
  the node's parenthetical definition. The tensor ring structure is canonical,
  not an additional hypothesis or supplied parameter.
- Conclusion, every finitely generated subextension is separably generated:
  `Algebra.IsSeparableExtension k K`. I opened
  `Sheaf.FieldTheory.SeparableExtension` and read both definitions:
  `∀ F : IntermediateField k K, F.FG → IsSeparablyGenerated k F`, and
  `∃ s : Set F, IsTranscendenceBasis k ((↑) : s → F) ∧
  Algebra.IsSeparable (IntermediateField.adjoin k s) F`.
  `IntermediateField.FG`, read in its Adjoin.Defs module, means generated by
  a finite set as a field, not finitely generated as a ring or finite degree.
  Set-indexed transcendence bases represent any independent family by its
  image. Mathlib's `Algebra.IsSeparable`, read in FieldTheory.Separable,
  requires every minimal polynomial to be separable and implies algebraicity.
  These definitions implement both clauses of 030O and the dependency node;
  no restriction to algebraic K/k has been silently imposed.

Edge cases: the empty finite generating set includes the base intermediate
field; an empty transcendence basis includes algebraic extensions. K = k,
L = k (after a universe lift if needed), characteristic 2, infinite extensions,
and unequal universes u and v are covered. p = 0 and p = 1 are correctly
excluded by primality. The zero ring is excluded exactly because the objects
are fields; there is no scheme, scheme emptiness, or independent n parameter.
No finiteness assumption is made on K or the test extensions.

Independent searches, using different wording from the worker:

- LeanFinder through msearch: `Reduced scalar extension of a field forces a
  separating transcendence basis for each finite type intermediate field`.
  Eight hits, principally separating-basis existence from p-power linear
  independence or perfectness. Their signatures do not state this implication.
- Loogle through msearch: `IsReduced, Algebra.IsSeparable`: zero hits.
- LeanSearch through msearch: `Reduced tensor products detect separability of
  non algebraic extensions of fields`: service Internal Server Error;
  unavailable, so no mathematical verdict assigned to that search.
- Mathlib grep through msearch:
  `isReduced.*isSeparable|isSeparable.*isReduced|IsSeparableExtension|030W`:
  one hit, the 030W (2) => (1) finite-generation theorem, not (4) => (1).
- Direct rg over the project Lean, source WeilConjectures, and upstream name
  index for `IsSeparableExtension|IsSeparablyGenerated|forall_isReduced|030W|
  030S|reduced.*separab|separab.*reduced`. I opened the closest project result,
  `Algebra.finiteExtension_tensor_algebraicClosure_reduced_isSeparable`:
  it requires `FiniteDimensional k K`, so it cannot replace this general item.
  The source module WeilConjectures.Mathlib.RingTheory.Nilpotent.GeometricallyReduced
  proves reduced tensor products over perfect fields and related forward
  implications; I read it and found no duplicate of this converse. Mathlib's
  SeparablyGenerated and GeometricallyReduced modules were also opened:
  the former provides p-power independence => separating basis, the latter
  defines geometric reducedness via algebraic closures and lists arbitrary
  field base change as a TODO. No exact existing declaration was found.

No mismatch found; no Lean, dependency record, or node content was changed.
There are no new nodes, dependency modules, or statement corrections to audit.
The source module has one named theorem with proof `sorry`, no definitions,
no proved lemmas, no private notions, and no unbound universes or variables.
Its module/declaration docstrings cite the source and exact blueprint id, and
its five numbered proof steps follow all five node steps and name their
supporting nodes. Imports are used and lines meet the 100-character convention.
The node's lean.statement is verbatim the file's signature before `:=`.

Validation: scompile.py with the absolute sandbox module path compiled the
58-line delivery on the server in 1.3 seconds, exit code 0, no warnings or
errors. An initial call with a relative repository path failed before compilation
because that file exists only in the sandbox; the absolute-path call above fixed
that invocation. Only this second-reading report was appended.

## Reviewer fix (R-grs1051)

The test-field universe of `hred` is `Type (max u v)` (STATE/brief universe rule, as M1 c8ddf5893); the extra free universe `w`, occurring only in the hypothesis, is removed. Statements above mentioning `w` refer to the delivered form.
