## Worker report

The module `Sheaf.SecTraceFormula.FlatMittagLefflerCriterion` states
`Module.flat_mittag_leffler_criterion`, with proof `sorry`. It follows Stacks
Project, Algebra, Tag 059S, `lemma-flat-ML-criterion`, read in
`literature/stacks-project/algebra.tex` at lines 21881 onward. The node's statement
and dependencies are unchanged. There are no new definitions or dependency repairs.
The theorem docstring includes the node's six-step natural-language proof.

Clause-by-clause correspondence:

- A commutative ring is `(R : Type u) [CommRing R]`.
- An R-module M is `(M : Type v) [AddCommGroup M] [Module R M]`.
- Its flatness is `[Module.Flat R M]`.
- “M is Mittag-Leffler if and only if” is
  `Module.IsMittagLeffler.{u, v, max u w, t} R M ↔ ...`, using the dependency's
  tensor-product definition. Its index universe admits all submodules of a finite
  free module over R; its coefficient universe is `max u v t`.
- “Every R-module F isomorphic to R^n for some finite integer n ≥ 0” is
  `∀ (F : Type (max u z)) [AddCommGroup F] [Module R F],
  (∃ n : ℕ, Nonempty (F ≃ₗ[R] (Fin n → R))) → ...`.
  No basis is selected, and n = 0 is permitted. The carrier universe is at least
  that of R, so the finite-free hypothesis is not vacuous; z is arbitrary.
  Finite free modules in larger universes have the same submodule lattice and
  tensor-support property via the stated linear equivalence. Their submodule
  and quotient tests can equally be represented in R's universe.
- “Every x in F tensor M” is `∀ x : F ⊗[R] M`.
- The set in question is represented by the predicate
  `x ∈ Set.range (LinearMap.rTensor M G.subtype)` on `G : Submodule R F`.
- Its least element is `∃ G₀ : Submodule R F` with the conjunction that G₀ satisfies
  this predicate and every G satisfying it obeys `G₀ ≤ G`. This is leastness,
  not just minimality, and G ranges over all submodules without finite-generation
  assumptions. There is no extra conclusion asserting finite generation of G₀.
- The displayed map is exactly `LinearMap.rTensor M G.subtype`, defined by
  `TensorProduct.map G.subtype LinearMap.id`; on pure tensors it sends
  `g ⊗ m` to `(g : F) ⊗ m`.

Dependency declarations read and used:

- `def-weil-pbc-flat-ring-map`: `Module.Flat` from
  `Mathlib.RingTheory.Flat.Basic`, imported through the recorded module
  `Mathlib.RingTheory.RingHom.Flat`. Its defining condition is equivalent to
  preserving injections of all modules; the dependency's recorded `RingHom.Flat`
  is the ring-map specialization and is not imposed on M.
- `def-trf-mittag-leffler-module`: `Module.IsMittagLeffler` from
  `Sheaf.RingTheory.IsMittagLeffler`. Read its full dependent-family definition
  and canonical map `TensorProduct.piRightHom`.
- `def-weil-pbc-module-tensor-product`: the Mathlib match `TensorProduct` from
  `Mathlib.LinearAlgebra.TensorProduct.Defs` and `LinearMap.rTensor` from
  `Mathlib.LinearAlgebra.TensorProduct.Map` (the latter is publicly imported).

Proof-dependency imports include `Sheaf.RingTheory.Flat.LazardPresentation`
(`Module.exists_directed_finite_free_presentation`), Mathlib's categorical
colimit interface, concrete filtered-colimit interface, module filtered colimits,
and monoidal closed-module tensor preservation interface. Flat tensor exactness
is already available through the flatness import. The two proof nodes
`lem-trf-flat-ml-minimal-support` and `lem-trf-flat-ml-dual-criterion` have no
recorded Lean module in the supplied DAG, so they cannot yet be imported; they
are named, with their roles, in the theorem's proof docstring. They are not
statement dependencies, and their notions are not needed to type this theorem.

Edge cases checked before writing: n = 0 gives a zero free module and its zero
submodule as least support; x = 0 is supported by the zero submodule for every
F; M = 0 similarly gives only zero tensors; the zero ring forces all modules to
be zero and satisfies the same statement. No nonzero-ring, positive-rank,
Noetherian, countability, or characteristic restriction appears. Flatness is
retained exactly as in Tag 059S. An arbitrary minimal submodule is not substituted
for the required least submodule. No statement fault or dispute was found.

Searches for an existing declaration (all performed for this item):

- `msearch.py ... leanfinder` with query “A flat module is Mittag Leffler if and
  only if every tensor with a finite free module has a least supporting
  submodule”: eight hits, including `Module.flat_iff`, `Module.Flat.out`, and
  the equational and injection criteria for flatness; none states this criterion.
- `msearch.py ... loogle` with query `"Mittag"`: nine hits; the mathematical
  hits define Mittag-Leffler systems of sets in `CategoryTheory.CofilteredSystem`,
  not the criterion for flat modules.
- `msearch.py ... grep` with expression
  `Mittag|least.*submodule|smallest.*submodule`, subdirectory `RingTheory`: three
  hits, two about ideal products and one adic-completion comment; no match.
- `msearch.py ... leansearch` with query “flat Mittag Leffler module least
  supporting submodule finite free tensor”: eight flatness/factorization hits,
  no exact match.
- `rg` in the upstream `WeilConjectures` source for Mittag-Leffler terminology,
  least/smallest submodules, and this node id: no exact statement or definition.
- `rg` in `lean/Sheaf` for the same terms found the recorded definition and
  related theorems (product of Noetherian copies, completion, Hom systems,
  descent, projectivity). Read the pertinent modules: none states this iff.
  Searching `dag/lean_names_upstream.json` found no matching declaration.

Validation: `scompile.py Q148 lem-trf-flat-mittag-leffler-criterion` compiled the
sandbox file and its intended library module separately, both cleanly with no
warnings. All universes and variables in the signature are explicitly bound.
Only the node's `lean` field is changed, recording the signature verbatim.

## Second reading by Q148

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
