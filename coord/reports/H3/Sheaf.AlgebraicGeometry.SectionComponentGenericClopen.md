## What changed

Replaced the whole-proof sorry of
`AlgebraicGeometry.exists_open_section_component_clopen` in
`lean/Sheaf/AlgebraicGeometry/SectionComponentGenericClopen.lean` by a complete Lean
proof from two strictly proper geometric steps of Stacks Tag 055N. Its signature,
visibility, existing docstring, and public imports stay identical.

Added two new modules, imported privately by the item's proof:

- `Sheaf.AlgebraicGeometry.GenericFibreComponentSpread` spreads a chosen component of
  the fibre at y to a clopen piece, without making any assertion about its other fibres.
  Its statement needs no section.
- `Sheaf.AlgebraicGeometry.GenericPointedClopenFibres` starts with an already clopen
  piece, a preconnected generic trace, and the rational section point in that trace.
  It supplies preconnected fibre traces on a smaller open, without identifying any
  section components and without asserting that the section lands in the piece there.

The original proof now supplies the missing combination itself: it deduces the generic
preconnectedness and section-point membership; pulls the clopen piece back along the
restricted section and expresses that open as an ambient open; shrinks the two base
opens together; transports clopenness to the smaller total-space subtype; and proves
both inclusions identifying every fibre trace with the section's connected component.
The second inclusion uses `IsPreconnected.subset_isClopen` on the fibre subtype and
`connectedComponentIn_eq_image`, while the first uses
`IsPreconnected.subset_connectedComponentIn`. This is a reduction, not an application
of a renamed copy of the original statement.

Updated the original node's proof, proof_deps, and proof_origin to match that argument.
Added nodes and complete source-based proof docstrings for the two geometric holes.
No definitions, existing interfaces, target signatures, or other existing modules changed.
No forced adaptations or change records are needed.

Validation: compiled the three-module sandbox in dependency order, then checked the
item again after removing an unused trial import of `Mathlib.Topology.Connected.Clopen`.
The latter module is already available through the existing imports. Compilation is
clean; the delivery tool additionally performs its declaration/axiom probes and preflight.

## Proved and sorry left

Closed one original direct hole:
`AlgebraicGeometry.exists_open_section_component_clopen`
(node `lem-sbc-section-component-generic-clopen`). There are no sorries left in the
item's module.

Added exactly two direct holes, each the entire proof of a public named theorem:

- `AlgebraicGeometry.exists_open_generic_fibre_component_spread`
  (node `lem-sbc-generic-fibre-component-spread`, module
  `Sheaf.AlgebraicGeometry.GenericFibreComponentSpread`).
- `AlgebraicGeometry.exists_open_preconnected_fibres_of_pointed_clopen`
  (node `lem-sbc-generic-pointed-clopen-fibres`, module
  `Sheaf.AlgebraicGeometry.GenericPointedClopenFibres`).

This is a decomposition: one upper hole closed and two lower geometric holes added,
not a completed axiom-free proof or positive net hole reduction. The topological
combination contains no sorry, and no definition contains a sorry.

## No longer needed

No original import, proof-dependency node, or module was pruned: the original node had
an empty proof_deps list and its module had only the two statement imports.
The unused trial proof import `Mathlib.Topology.Connected.Clopen` was removed before
delivery. Neither new module imports an unrelated geometric theorem.

The affine noetherian-base route through
`WeilConjectures.RingTheory.RelativeComponentConstructible` and the smooth-only
section-component results were considered but not imported: their additional hypotheses
would not prove this finite-type statement. The arbitrary-base-change section-locus
lemma Tag 055M is not needed in the parent's Lean combination: the two geometric
statements already use the correct ambient subspace formulation. Their own proof plans
use the homeomorphism of a closed immersion and its base change, not a replacement
section-locus theorem. No unit's statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The initial node had no stated proof-dependency declarations and recorded all the
geometric steps of Tags 055N, 054Y, 054W, 04KV, and 055G in a single non-elementary
paragraph. Thus the brief's general assertion that the proof plan's dependencies were
already declared did not apply to this particular item. The two new theorems make
proper groups of those steps into independent future proof items.

Sources read: Stacks Tags 055N, 054Y, 054W, 04KV, and 055G. The original arbitrary
finite-type hypotheses are retained, including the absence of noetherianity,
quasi-separatedness, flatness, or smoothness assumptions. No false statement or source
error was found. The unit `sk-prop-normal-form` and its unchanged realization record
were read.

Edge cases checked for the new statements: the first lemma cannot be invoked over an
empty fibre because it requires an actual point x in that fibre. An empty complementary
component is allowed. A connected generic fibre may give the entire clopen piece.
The second lemma's generic trace cannot be empty because it contains sigma(y).
Preconnectedness alone would not imply geometric connectedness; the section supplies
the necessary rational point, and its section identity is retained explicitly.
A is allowed to contain arbitrary points outside the restricted total space; both
conclusions only inspect fibres over V intersect closure {y}, so those points have no
effect. There is no asserted equality with the relative component in either new lemma.
Over a single-point base the statements reduce to the corresponding generic-fibre
claims. Disconnected or nonreduced original bases are handled by reduced base change
to the closure of y in the two geometric proof plans.

Searched the library, upstream affine results, DAG tags, and whole blueprint for the
new lemmas. Blueprint searches for 054Y, 054W, and 055G returned no matching blueprint
nodes. For each new statement, LeanSearch returned HTTP Internal Server Error and is
recorded as unavailable; LeanFinder and local Mathlib grep returned no exact match.
The actual queries are in searches.jsonl. The original declaration docstring was kept.

## New nodes

`lem-sbc-generic-fibre-component-spread`, in
`dag/nodes/sec-smooth-base-change/`, corresponds to
`Sheaf.AlgebraicGeometry.GenericFibreComponentSpread`. It groups the first geometric
part of Tag 055N: noetherian generic fibre, closure of a component and its complement,
spreading the covering and eliminating their intersection, and the closed-base-change
homeomorphism. It does not identify components away from y and requires no section.

`lem-sbc-generic-pointed-clopen-fibres`, in the same chapter, corresponds to
`Sheaf.AlgebraicGeometry.GenericPointedClopenFibres`. It groups the next geometric
part of Tag 055N: a finite-type clopen piece, its connected generic fibre with a rational
point, Tag 04KV, and persistence by Tag 055G. The parent proof provides section landing
on the resulting open and the connected-component identification independently.

Both nodes inherit the original chapter, unit, and nearest blueprint ancestor
`sbc-lem-slicing`. Each has its own statement, source, complete proof in words,
three logged search kinds, and Lean record. No change record was added.

## Second reading by H3

1. Compared the delivered item with the repository version. The existing theorem signature and docstring are byte-for-byte unchanged; only its proof and two private proof imports changed. The two added declarations are new split statements with matching DAG records.

2. Compiled all three delivered modules with `lcompile.py --all`; compilation is clean. The only remaining `sorry`s are the two named split theorem proofs, and there are no sorries in definitions or forbidden declarations.

3. Checked the two split statements against Tags 055N, 04KV, 054Y, 054W, and 055G and tested the stated edge cases in the original report. They are strictly smaller than the parent and do not restate it; no existing declaration matching either statement was found by local search.

4. Read the proof top-down. The parent proof uses the two split lemmas, then the stated connected-component and clopen-subspace lemmas. The two new imports are proof-only and private; no old import or proof dependency is unused. The unit record and route remain unchanged.

5. Checked the DAG proof, proof dependencies, source, Lean declarations, and split-node metadata against the delivered code. They agree. No repair was needed after this reading.
