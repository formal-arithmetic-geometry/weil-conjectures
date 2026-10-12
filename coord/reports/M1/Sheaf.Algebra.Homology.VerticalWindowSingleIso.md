## What changed
The existing target `HomologicalComplex₂.verticalWindow_single_iso` now assembles
explicit canonical components with `CategoryTheory.NatIso.ofComponents`.
Its signature and public imports are unchanged. Its added proof-only import is
`Sheaf.Algebra.Homology.VerticalWindowComponentNaturality`.

The new `VerticalWindowDegreeIso` module constructs the surviving-degree
isomorphism from Mathlib's boundary-cycles comparison, cycles-to-homology map,
inverse of the lower-truncation homology map, and extension homology comparison.
The new `VerticalWindowComponentIso` module constructs the complex isomorphism,
proving the vanishing terms and inverse equations degreewise. Neither definition
uses an unproved existence theorem or any sorry.
The new `VerticalWindowComponentNaturality` module states naturality for those
specific constructed components; this is the one remaining hole.

## Proved and sorry left
Closed the original hole in `HomologicalComplex₂.verticalWindow_single_iso` by
assembling components; added one hole:
`HomologicalComplex₂.verticalWindow_component_naturality`, node
`lem-sp-vertical-window-component-naturality`.
This is a decomposition, not a complete proof: one old hole closed, one new hole
added, net zero. The target still depends on sorryAx through this naturality hole.

The constructions `HomologicalComplex₂.verticalWindowDegreeIso` and
`HomologicalComplex₂.verticalWindowComponentIso` are fully proved; their axiom
checks show only propext, Classical.choice and Quot.sound.
The first worker's two-hole split has been replaced: its holed objectwise
existence result is replaced by a fully constructed objectwise isomorphism, and
its false naturality theorem is removed rather than counted as a hole closed.

## No longer needed
No repository module or public import is pruned.
The old direct proof dependency `def-sp-double-complex-vertical-window` is now
used through the canonical-component construction, not as a sufficient proof of
the target. It remains a statement dependency and remains in the import closure.
The target's direct proof dependencies are now
`lem-sp-vertical-window-component-iso` and
`lem-sp-vertical-window-component-naturality`.

## Where the brief, the DAG or earlier work was wrong
The first worker's `verticalWindow_component_naturality` quantified over arbitrary
isomorphisms eK and eL. It is false: in rational vector spaces take K = L to be
a one-dimensional single complex and f to be its identity. If e is any window
comparison, take eK = e and eL = e followed by multiplication by 2. The claimed
square would equate these distinct isomorphisms. Its docstring referred to
canonical maps, but the statement imposed no canonical normalization.
The first worker also selected arbitrary components using `.some` from an
unproved mere existence theorem. This violated the rule on unproved choices.
Both defects are repaired by explicit canonical constructions.

The inherited unit `sk-prop-av-pqf-finite` concerns proper quasi-finite morphisms
and its `realized` arrays are empty; it contains no spectral-sequence step
realized by this node. This inherited filing mismatch is reported, not changed.
The node's actual cited spectral-sequence argument (single-layer identification)
is preserved, and no unit or chapter route is bypassed.

## New nodes
`lem-sp-vertical-window-degree-iso` records the canonical surviving-term
construction, in `VerticalWindowDegreeIso`.
`lem-sp-vertical-window-component-iso` records the fully constructed complex
comparison, in `VerticalWindowComponentIso`.
`lem-sp-vertical-window-component-naturality` records the one strictly smaller
remaining task, in `VerticalWindowComponentNaturality`. Its docstring gives the
complete four-square proof and explicitly concerns the constructed components.
All three use actual logged LeanSearch, LeanFinder, Loogle and grep searches.
LeanSearch was unavailable (Internal Server Error), recorded without a verdict. Searches of
Mathlib and the upstream and Sheaf libraries found the constituent constructors
and naturality APIs, but no exact single-window comparison already available.
No existing definition or statement changes, so no change record is needed.

## Second reading by M1
1. Compared the target module with the repository using diff. Its existing
   theorem signature is byte-for-byte unchanged; only its proof and one plain
   import change. All other delivered modules are new. No target or existing
   definition was changed.
2. Compiled all four modules in import order using lcompile.py; no errors or
   warnings. Checked every declaration with #print axioms in scratch copies.
   Both constructions use only the three allowed axioms. The naturality theorem
   and target additionally use sorryAx, from the listed named theorem only.
   No axiom, unsafe, opaque, implemented_by, extern or holed definition occurs.
3. Rejected the false arbitrary-isomorphism naturality statement and the
   undetermined existence choice. The replacement naturality statement is true
   for the explicit components and strictly a part of the argument: the
   component isomorphisms, vanishing terms and inverse laws are already proved.
   Checked q = 0, zero complexes and identity maps: integer extension supplies
   the zero incoming term at q = 0; the constructions have the same formulas.
   Repeated searches using alternative queries and inspected the relevant APIs.
4. Followed the canonical shortest route through existing Mathlib truncation,
   homology and single-complex APIs. Imports match the statements or definition
   bodies they expose; the target's new import is proof-only. The old dependency
   and the inherited unit filing mismatch are accounted for above. No module is
   pruned and no realized unit step is bypassed.
5. Updated the target node's proof, proof_deps and proof_origin to the assembly;
   updated the two first-worker nodes to the actual definitions and restricted
   naturality statement; added the surviving-degree node. New node signatures
   are copied verbatim from Lean and searches have real logged provenance.

Second reading changed the invalid existence-based split into explicit,
sorry-free canonical degree and complex comparisons; restricted and separated
the remaining naturality task, repaired the target assembly, and corrected the
DAG and progress accounting. The result is a valid decomposition with one hole.
