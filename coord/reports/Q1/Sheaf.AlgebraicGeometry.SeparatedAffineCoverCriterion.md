## What changed

Proved `AlgebraicGeometry.separated_of_affine_open_cover` without changing its signature.
Added the proof-only import `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated`.
Tensor induction shows that every overlap is a separating pair, using the assumed surjective
ring map. The source library's proved `Scheme.isSeparated_of_isSeparatingPair` proves
absolute separatedness of V, and Mathlib supplies separatedness of f.
Updated the item's node to this route and attached the previously unrecorded proved source
criterion to a new node. No definitions or statement interfaces changed.

## Proved and sorry left

Proved `AlgebraicGeometry.separated_of_affine_open_cover` (1 of 1 original sorries).
No sorry remains in the module, and none is added elsewhere. Nothing is split off.
Local compilation succeeds without warnings. Explicit `#print axioms` checks of the item,
`Scheme.isSeparated_of_isSeparatingPair`, and `Scheme.homOfLE_appTop_topIso_inv` each report
only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

No original import was removed: both public Mathlib imports support the existing statement.
The item no longer directly needs `lem-weil-pbc-open-fibre-product`,
`lem-weil-pbc-fibre-product-affine-spectra`, or
`lem-weil-pbc-closed-immersion-affine-cover-criterion`; the source criterion already proves
that geometric argument. These nodes remain recorded below the new criterion as the
literature's mathematical dependencies; all are Mathlib leaves and require no proof work.
`def-pc-fibre-product`, `def-weil-affine-spectrum`, and `def-weil-closed-immersion` are no
longer direct proof dependencies (statement dependencies are retained unchanged).
No Sheaf proof-dependency module needed an import, and no unproved module is added to
this item's closure. No global unreachability claim is made for nodes used elsewhere.

## Where the brief, the DAG or earlier work was wrong

The old search missed the exact source-library affine-cover criterion in terms of
`IsSeparatingPair`; a direct Mathlib match is unnecessary. The hypothesis `[IsAffine S]`
is stronger than this proof needs: the tensor-over-ℤ condition already proves V itself
separated. Its signature is retained unchanged. Empty overlaps and an empty source are
handled by subring/tensor induction and the source covering criterion without extra
nonemptiness assumptions. An empty index type can cover only an empty source.
The item does not realize a unit statement or unit proof step in `sk-thm-p1.realized`,
and this substitution below the unit changes no fixed unit route.
LeanSearch returned a service error; LeanFinder, Loogle, source searches and Mathlib grep
were available. The cited Stacks proof was also read in the available local copy of
`schemes.tex` (Tag 01KP, lines 4157–4215).

## New nodes

`lem-weil-pbc-separated-separating-pair-cover` attaches the already proved source declaration
`AlgebraicGeometry.Scheme.isSeparated_of_isSeparatingPair`. It states the ring-generation
version of the absolute affine-cover criterion, records its complete geometric proof,
and requires no new Lean module or sorry. Its standard-axiom closure was checked locally.
No change record is required because no statement or definition changed.

## Second reading by Q1

1. Compared the delivered Lean module with the repository using `diff`, and separately
   compared the complete theorem signature byte for byte. Verdict: unchanged signature;
   only the proof, its explanatory docstring, and one plain proof-only import differ.
   There are no definitions, adapted modules, or statement changes.
2. Compiled the module and its scratch copy with explicit `#print axioms` commands through
   `lcompile.py`. Verdict: no errors or warnings, no sorry or forbidden declaration forms;
   the item, `Scheme.isSeparated_of_isSeparatingPair`, and
   `Scheme.homOfLE_appTop_topIso_inv` use only `propext`, `Classical.choice`, and `Quot.sound`.
   Read the upstream separating-pair definition and the proofs of its cover criterion and
   affine overlap equivalence. Tensor induction transports the actual restriction maps,
   and surjectivity supplies every overlap section; the final instance proves the stated f.
3. No statement was split off and no new Lean declaration was added. The new node attaches
   an existing fully proved upstream theorem, with genuinely different ring-generation
   hypotheses; the item supplies a real tensor-induction reduction. Independent LeanFinder
   search for affine charts and generated overlap rings, Loogle search for separatedness
   and tensor products, and local source/DAG searches found no shorter direct theorem or
   duplicate node. Verdict: its statement agrees with the source theorem and its geometric
   proof is sound. Empty overlaps have the zero ring, and an empty cover can cover only
   an empty scheme; neither case requires an extra hypothesis.
4. Checked the proof from the conclusion downward and all seven original proof dependencies.
   Verdict: the existing upstream criterion is the shortest available route; the plain
   upstream import is used, and the public Mathlib imports provide the statement's interface.
   All six removed direct dependencies are listed under `No longer needed`.
   Neither node realizes a statement or step in `dag/units/sk-thm-p1.json`, so this change
   below the unit preserves its realized route.
5. Compared node changes with the Lean proof and checked the new attachment's required
   fields. Verdict: the existing node changes only `proof`, `proof_deps`, and `proof_origin`;
   its three steps match the Lean proof and their uses have exactly the recorded union.
   The new node records the correct upstream module, declaration, signature, source,
   searches, and proof. Repaired its blueprint `via` chain to include the item's inherited
   intermediate nodes, as required by the new-node ancestry convention.

Second reading changed only the new node's blueprint ancestry and appended this review.
The Lean proof needed no repair. No additional sorry, statement change, or import was added.
