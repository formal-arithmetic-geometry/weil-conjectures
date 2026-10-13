## What changed

The existing declaration `completedRingMap_surjective` keeps its signature and
visibility byte for byte. Its proof now constructs the C-linear comparison,
proves its target finite over the completion C directly from `s.finite_appTop`
and the affine counit, and applies Mathlib's
`LinearMap.surjective_of_surjective_comp_mkQ` (Nakayama).
The sole new intermediate theorem `completedRingMap_residue_lift` asserts
lifting only modulo the extended maximal ideal. It is in the new module
`Sheaf.AlgebraicGeometry.Morphisms.CompletedMatchingRingMapResidueLift`.
The target imports it and `Mathlib.RingTheory.Nakayama` privately. The residue
module publicly imports the comparison definition and completion local-ring
API, both needed by its statement. No existing definition changed.

## Proved and sorry left

Closed existing hole: `AlgebraicGeometry.Scheme.CompletionGluingData.completedRingMap_surjective`.
Added hole: `AlgebraicGeometry.Scheme.CompletionGluingData.completedRingMap_residue_lift`,
node `lem-sbc-completed-matching-ring-map-residue-lift`.
This is a decomposition, not a completed proof of the mathematical result:
one old hole closed and one new hole added, net zero. Finiteness and the
Nakayama upgrade are proved in Lean; residue lifting remains open. There are
no other delivered sorries. The first worker's `completedRingMap_finite` hole
was closed using Mathlib before its unnecessary wrapper was removed; its
`completedRingMap_epi` hole was discarded rather than counted as proved.

## No longer needed

The unlanded proposed modules `CompletedMatchingRingMapSurjectiveEpi` and
`CompletedMatchingRingMapSurjectiveFinite`, and their proposed epi and finite
nodes, are removed from the delivery. The categorical epimorphism route is
replaced by residue approximation and Nakayama. No repository import was
removed and no existing module is pruned.

Of the original direct proof dependencies,
`def-sbc-punctured-completion-matching-sections` and
`def-weil-pbc-noetherian-ring` no longer occur as direct steps in the parent's
proof; they remain statement dependencies and are used by the residue step.
`def-sbc-completed-matching-ring-map` and
`def-weil-finite-integral-morphism` remain direct proof dependencies.
Identical copies of the matching-sections and comparison-definition modules
were removed from the sandbox delivery after byte comparisons confirmed they
were unchanged; their library modules remain imported.

## Where the brief, the DAG or earlier work was wrong

The initial epi/finite split added two holes, left a trivially available
finiteness fact open, and put almost all of the original argument in the epi
hole. Its new-node records also copied unrelated review metadata and did not
contain verbatim Lean statements. The second reader replaces that split.
The new residue statement leaves the genuinely geometric approximation step
open and formalizes the independent finite-module upgrade. The parent DAG now
records the implemented route rather than the original narrative proof.
The original target docstring and signature are preserved.

## New nodes

`lem-sbc-completed-matching-ring-map-residue-lift` is the residue-class lifting
step, with the same geometric data as the parent and conclusion only modulo
m_C Γ(E). Its source is Stacks 0BLH and the canonical H0 comparison of 05ER,
reduced modulo the maximal ideal. Its docstring explains the finite chart
gluing, the sheaf equalizer identification, the comparison, and passage to the
quotient. The node includes a self-contained statement, the verbatim Lean
signature, proof steps and searches. No change record is needed: every
existing interface is unchanged.

## Second reading by Q2

1. PASS. Compared every original sandbox module with its repository version.
   The two dependency copies were identical. The target diff consists only of
   private imports and replacement of its proof body; its existing signature,
   docstring, definitions and visibility are unchanged.
2. PASS. Compiled the delivered modules individually in import order using
   lcompile.py. The only sorry is the named residue-lifting theorem. No axiom,
   unsafe, opaque, extern, implemented_by, or data chosen from an unproved
   existence statement occurs. Scratch axiom checks and delivery probes check
   the target and residue theorem; sorryAx is expected solely through the
   declared remaining hole, alongside the allowed foundational axioms.
3. PASS as decomposition. Residue lifting is true by the canonical comparison
   in Stacks 05ER and its quotient, with the affine construction in 0BLH. It
   asks only for a representative of a residue class, not an exact preimage.
   The target supplies the nontrivial Nakayama upgrade. Empty U (Artinian A)
   gives the identity comparison, and zero completed algebras lift zero.
   For a field A, U is empty and the same identity check applies. LeanFinder,
   Loogle and grep searches, plus rg on both library roots, found no existing
   matching residue lift; the generic finite and Nakayama lemmas are used.
   LeanSearch was also attempted and returned Internal Server Error; its
   unavailability is recorded without a mathematical verdict.
4. PASS. Proved finiteness directly and replaced the weak epi decomposition.
   The imports are needed for the statement or the implemented proof. The
   original definition import remains public; the new proof imports are
   private. No original library module is pruned. Inspected
   dag/units/sk-prop-input-spreading.json: its statement and all seven realized
   step lists are unchanged; this local finite-gluing reduction bypasses no
   unit step or chapter route.
5. PASS. The parent proof/proof_deps/proof_origin now describe C-linearity,
   finite global sections and Nakayama using the residue node. The new node
   has its own blueprint tag, exact Lean signature, complete source argument,
   search records, Q2 creation record, and the parent's chapter and unit.
   Removed the two superseded new nodes instead of delivering fabricated
   inherited review records. No existing node interface was edited.

Changes by this reader: proved and inlined finiteness, replaced epimorphism by
residue lifting plus Nakayama, removed the two old proposed split modules and
nodes, repaired dependency metadata and the report, and removed identical
compile scaffolding copies. This delivery claims decomposition only.
