## Worker report

This delivery binds the existing declaration
`Representation.exists_compositionSeries` in
`WeilConjectures.RepresentationTheory.CompositionSeries` (branch `slopmaster2`).
No module, definition, proof, or natural-language statement is changed. The source
module explicitly identifies this theorem with
`lem-mg-composition-series-exists` in both its blueprint list and theorem docstring.
It was read using `scompile.py --source` because the older local source checkout
does not contain that module. The current main-20261015 statement agrees with the
node and the older blueprint source.

Clause and hypothesis correspondence:

- Every Weil representation is an instance of `(ρ : Representation k W V)`,
  taking `W` to be the actual Weil group. Its invariant subspaces are exactly
  `Subrepresentation ρ`; the existing theorem quantifies over arbitrary groups,
  fields, and vector spaces with independent universes, so it applies without
  changing the action or requiring any extra hypothesis on that Weil group.
- Finite-dimensional means `[FiniteDimensional k V]`. The surrounding binders
  supply `[Field k]`, `[Group W]`, `[AddCommGroup V]`, and `[Module k V]`.
- Nonzero means `Nontrivial V`. The existing theorem needs no such assumption;
  its application in this node is restricted to the specified nonzero
  representation. This is an explicit specialization of the already proved
  library result, not a change to the node. A duplicate theorem with an unused
  nonzero binder would restate this very same existence result.
- Has a composition series means `Nonempty ρ.CompositionSeries`.
  `Representation.CompositionSeries.series` is a finite `CovBy` chain in the
  lattice `Subrepresentation ρ`, and `head_eq` and `last_eq` identify its
  endpoints with zero and the full representation. Covering implies strict
  inclusion. `CompositionSeries.isIrreducible_factor` and
  `Subrepresentation.isIrreducible_subquotient_iff` identify these covering
  steps with simple successive quotients. `Representation.isIrreducible_iff`
  explicitly says that such a quotient is nonzero and has no invariant
  subspaces other than zero and itself. The finite index set retains repeated
  factors; no semisimplicity or splitting of the representation is imposed.

Dependency declarations read: the node has no statement dependencies. Its proof
names `def-mg-weil-composition-series`; that node's upstream audit identifies
`Representation.CompositionSeries` and `Representation.CompositionSeries.factor`
in the same existing module. Their full definitions and docstrings were read.
The irreducibility characterizations above are in
`WeilConjectures.Mathlib.RepresentationTheory.Irreducible`, also read in the live
source. No dependency repair is necessary: there is no copied notion or new
module requiring an import. The proof plan in the node is dimension induction,
splicing a series of a proper invariant subspace with the inverse images of a
series of its quotient. The existing proved theorem instead uses the equivalent
well-founded induction on invariant subspaces and appends irreducible quotients.

Edge cases checked: a simple nonzero representation has the two-endpoint chain
of length one; reducible representations need not split as a direct sum; a
nonzero representation cannot have a chain of length zero
(`CompositionSeries.length_pos`). The zero representation, outside the node's
hypothesis, is harmless in the general library theorem: it has the singleton
chain with zero equal to top. Neither characteristic zero, algebraic closure,
a finite Weil group, nor an assumption on Frobenius eigenvalues is needed.

Searches made:

- `msearch.py leanfinder`, query "Every nonzero finite dimensional representation
  of a group over a field has a composition series": eight hits on finite group
  representations, FDRep and irreducibility, none an exact existence theorem.
- `msearch.py loogle`, query "CompositionSeries, Representation": zero hits.
- `msearch.py grep`, query "exists_compositionSeries|CompositionSeries" in
  `RepresentationTheory`: zero Mathlib hits.
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for
  `compositionSeries|CompositionSeries|composition.series`: no duplicate
  representation theorem in the older checkout; related subquotient and
  module-filtration results only. Searching the node id in upstream source
  also found none in that older checkout.
- The node's upstream audit names the exact candidate. `scompile.py --source
  WeilConjectures.RepresentationTheory.CompositionSeries` retrieves its live
  source, including the theorem, its binders, the chain structure, quotient
  factors, irreducibility theorem, and the explicit blueprint association.

No statement correction, new node, or disputed statement. The existing binding
is validated by a scratch file using `scompile.py`, with explicit independent
universes, applications both with and without `Nontrivial V`, and an axiom check.
The delivery tool additionally checks the recorded existing declaration.

Validation: the scratch check passed without warnings in both the local overlay
and server confirmation (2.0 s and 1.7 s). `#print axioms` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`.

## Second reading by Q37

Independent maintainer reading of immutable delivery
ff996d8710cc283d90692c7ee9b603b294bc75c6, performed on 2026-10-17.
This section replaces the worker's placeholder; the reviewer did not write the delivery.

Read the item node and report in the immutable snapshot. Read the source lemma at
literature/blueprint/master/blueprint/sec-algebraic-groups-lie-algebras/
sk-r-linear-library/lem-mg-composition-series-exists.md (order 2541), and the definition at
sk-d-weights/def-mg-weil-composition-series.md (order 2536), in the read-only Q37 clone.
Read the complete upstream CompositionSeries module in that clone, its module docstring,
and the relevant Irreducible and Subrepresentation declarations.

Clause-by-clause reading:

- The object is the given Weil representation on V. Take W to be its Weil group in
  Representation k W V. Subrepresentation means a k-linear invariant subspace for this
  same action, so neither the group nor the representation has been replaced.
- The field, group, additive group and module structures are the surrounding explicit
  binders. Finite dimensionality is exactly [FiniteDimensional k V]. There is no finite
  group, semisimplicity, characteristic-zero or algebraic-closure hypothesis.
- Nonzero is [Nontrivial V]. The existing theorem applies without this hypothesis,
  hence specializes directly to the nonzero case. This use of a proved general theorem
  is legitimate and does not change the node or require a duplicate statement.
- Existence is Nonempty ρ.CompositionSeries. The structure contains a finite chain of
  subrepresentations with head_eq = bottom and last_eq = top. Its steps are covers,
  hence strict inclusions. The factor at i is the quotient of term i+1 by term i.
  isIrreducible_factor and Subrepresentation.isIrreducible_subquotient_iff identify
  the covering condition with irreducibility; Representation.isIrreducible_iff means
  nonzero with no nonzero proper invariant subspace. Thus every conclusion clause
  agrees with the source definition, including retention of repetitions.
- The recorded lean.statement is verbatim the declaration signature before :=.
  The compiler prints independent universes for k, W and V, with all binders bound.

The item has no statement dependencies. Its proof dependency
 def-mg-weil-composition-series was read, including its audited declarations
Representation.CompositionSeries and Representation.CompositionSeries.factor. Those are
exactly the notions used here. No private copy or missing helper is present. The node's
proof proceeds by dimension induction, joining a series in U to inverse images of a
series in V/U. The existing proof instead inducts on subrepresentations and appends
irreducible quotients; it establishes the same assertion without assuming a splitting.
No statement correction or citer audit is required.

Edge cases: a simple nonzero representation has a one-step series; a nonzero
representation has positive series length (length_pos); the zero representation has
an allowed length-zero series and is outside the node's nonzero hypothesis. Infinite
Weil groups, arbitrary field characteristic, nonsplit extensions and independent
universes are all covered. No Frobenius eigenvalue assumption is used.

Independent searches with rg for CompositionSeries, composition.series and
exists_compositionSeries in the old upstream WeilConjectures tree and Q37 lean/Sheaf
found related lattice/filtration results but no competing representation definition.
The exact Q37 upstream module is already the audited binding. Mathlib JordanHolder
and RelSeries were inspected for the finite-chain meaning. The worker's semantic,
type-pattern and textual search records remain above; they are not claimed as newly
executed searches by this reviewer.

Reproduced validation with scompile.py Q37 lem-mg-composition-series-exists /dev/stdin,
using an import-only/check-only input, autoImplicit false, three explicit universes,
applications with and without Nontrivial V, factor irreducibility, positive length,
and #print axioms. Both wrapper phases passed without warnings: sandbox overlay
1.8 s, library confirmation 1.7 s; exit code 0. The theorem uses exactly propext,
Classical.choice and Quot.sound. There are no delivered Lean files to compile.
The installed wrapper now runs its overlay and library checks on the server; these
are fresh reproduction timings, not independent confirmation of the worker's
historical 2.0 s timing.

Findings: H11, the original second-reading section contained only a placeholder.
Replaced it with this substantive independent reading. No mathematical or Lean-record
correction was necessary. The existing upstream module's blueprint associations and
its theorem docstring were checked; their older formatting and short proof commentary
are not newly delivered Lean subject to stage-2 module-writing gates. No new proof,
hollow definition, live Lean write, global build or pro-etale substitute was introduced.
