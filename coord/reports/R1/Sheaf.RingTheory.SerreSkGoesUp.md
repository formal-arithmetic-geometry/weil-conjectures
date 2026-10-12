## What changed

Proved `RingHom.isSerreS_of_flat` with its signature unchanged. The proof chooses
its fibre prime with `PrimeSpectrum.preimageEquivFiber`, applies the depth and
height formulas, and proves the extended-natural minimum inequality.

Added two modules with complete proof bodies: `Sheaf.RingTheory.FlatFiberLocalDepth` and
`Sheaf.RingTheory.FlatFiberPrimeHeight`. The former applies the existing flat
local depth formula after identifying the closed fibre; its private helpers
prove depth invariance by transporting regular sequences across ring isomorphisms.
The latter applies Mathlib's going-down height formula to the localized map.
Both proofs use `Ideal.Fiber.algEquivAux₂` and quotient equivalences for equal ideals.
Updated the existing node's proof route and added nodes for these two proved formulas.
All three modules compile locally, with no warnings.

## Proved and sorry left

Proved `RingHom.isSerreS_of_flat` (lem-weil-pbc-serre-sk-goes-up),
`RingHom.depth_eq_add_of_flat_fiber` (lem-weil-pbc-flat-fiber-local-depth), and
`RingHom.height_eq_add_of_flat_fiber` (lem-weil-pbc-flat-fiber-prime-height).
Closed the sole original hole, `RingHom.isSerreS_of_flat`.
No sorry remains in any delivered module and no new hole was added.
The height formula has only the three permitted axioms; the ascent and fibre
depth formula retain `sorryAx` through the existing flat local depth formula,
so they are not yet axiom-closed proofs of the target closure.
The proof still depends on the existing unfinished theorem
`IsLocalRing.depth_eq_add_of_flat_local`
(lem-weil-pbc-flat-local-depth-formula), imported in FlatFiberLocalDepth.
The private arithmetic and depth-invariance helpers are also completely proved.

## No longer needed

Removed direct imports `Sheaf.RingTheory.Depth`,
`Sheaf.RingTheory.FibreRingNoetherian`, and
`Sheaf.RingTheory.FlatLocalDepthFormula` from the item.
Depth remains a definition dependency through SerreConditions; FlatLocalDepthFormula
remains a proof dependency through FlatFiberLocalDepth.
The node `lem-weil-pbc-fibre-ring-noetherian` and module
`Sheaf.RingTheory.FibreRingNoetherian` are unnecessary on this proof branch:
the original hfibres hypothesis already supplies exactly that Noetherian witness.
The old direct proof dependencies `lem-weil-pbc-flat-local-ring-maps`,
`lem-weil-pbc-flat-local-depth-formula`, `lem-weil-pbc-flat-height-formula`,
`lem-weil-pbc-fibre-ring-local-ring-iso`, and `def-weil-pbc-depth` are now used
through the two formula nodes; they are not pruned from this branch. No unit statement or realized unit step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The plan needlessly derived Noetherianity of the fibre separately despite its
presence in hfibres. No statement correction was needed.
The pinned Mathlib height formula is phrased using the height of a quotient
prime, whereas SerreConditions uses heights of fibre primes. Applying it to the
localized map and transporting Krull dimension through the fibre isomorphism
closes this conversion.

Local literature/stacks-project/algebra.tex is absent on this machine. Read the
Stacks web pages for Tags 0339, 0337 and 00ON and the pinned Mathlib implementation
of the fibre isomorphism instead. LeanSearch returned Internal Server Error;
Loogle, LeanFinder and local grep were available. Searches found no pre-existing
ascent proof, explicit fibre-prime formulas, or pinned depth-invariance theorem.

Edge cases: k=0 is covered by the minimum proof; infinity is handled without
subtraction or any finiteness assumption in the arithmetic. A zero target or
empty fibre has no prime at which a bound must be checked. Identity maps have
zero-dimensional field closed fibres. Both formulas keep all Noetherian and
flatness hypotheses used by their source theorems.

## New nodes

`lem-weil-pbc-flat-fiber-local-depth`: module
`Sheaf.RingTheory.FlatFiberLocalDepth`, fully proved from the existing flat local
depth formula, the fibre-local-ring isomorphism, and regular-sequence transport.
Its assertion contains neither k nor either Serre hypothesis.

`lem-weil-pbc-flat-fiber-prime-height`: module
`Sheaf.RingTheory.FlatFiberPrimeHeight`, fully proved from Mathlib's going-down
height formula and the fibre-local-ring isomorphism. It contains no depth or
Serre assertion. No change records are needed: no existing statement,
definition, or public import changed.


## Second reading by R1

1. PASS: diff against the repository shows that the existing declaration's
   signature and docstring are byte-for-byte unchanged. Only its proof, a private
   arithmetic helper, and proof-only imports changed. No definition was changed;
   no change record is required. Both other modules and their nodes are new.
2. PASS: all three files compile locally without errors or warnings. Text checks
   find no sorry or forbidden declaration mechanism. A scratch axiom check gives
   only propext, Classical.choice, Quot.sound for the height formula, and those
   plus sorryAx for the ascent and depth formula. The latter comes from the
   existing IsLocalRing.depth_eq_add_of_flat_local, not a new hole or definition.
   The delivery closes one original hole and adds zero holes.
3. PASS: no unfinished statement was split off. The two new formula statements
   are separate, necessary parts of the argument, with source, proof docstrings,
   and complete nodes. Neither contains k or Serre assumptions. Reviewed the
   localization, ideal-map composition, quotient equivalences, and regular-sequence
   transport against the definitions and Mathlib. Identity maps give the expected
   zero height/depth field fibre; zero rings and empty fibres admit no Q; k = 0
   and infinite heights are covered by the arithmetic proof without subtraction.
   Independent LeanFinder, Loogle, msearch grep, and rg searches with different
   wording found no existing ascent or explicit fibre depth/height formula in
   the pinned library; the existing dimension and fibre isomorphism tools are used.
4. PASS: the proof starts at the Serre condition at q, chooses its fibre prime,
   applies the separate depth and height formulas, and closes the minimum bound.
   The source depth formula remains imported. The fibre Noetherianity node is
   genuinely unnecessary because hfibres supplies the witness. Listed all old
   proof_deps removed from the direct list and distinguished their transitive use
   from pruning. Read sk-thm-p1.realized: no realized unit statement or step is
   removed or bypassed. Public imports supply statement vocabulary; proof imports
   are private to each module.
5. PASS: compared each Lean signature with its node's lean.statement, checked
   proof_deps equals the union of proof-step uses, and checked the route and
   proof_origin against the actual proof. Existing node changes are limited to
   proof, proof_deps, proof_origin. New nodes contain the required source, searches,
   creation, blueprint, chapter, unit, and lean fields.

Second reading changed: removed redundant proof-only imports
Mathlib.RingTheory.LocalRing.ResidueField.Basic from FlatFiberPrimeHeight and
Mathlib.RingTheory.LocalRing.RingHom.Basic from FlatFiberLocalDepth; the necessary
facts are already imported transitively. Recompiled the full delivered set after
these removals. Clarified the axiom-closure limitation and the full list of old
direct dependencies now used transitively in this report. No proof or signature
needed repair.
