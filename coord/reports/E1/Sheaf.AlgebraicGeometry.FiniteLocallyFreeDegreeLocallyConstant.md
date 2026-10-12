## What changed

Repaired the returned import-cycle failure by removing the proof import
`WeilConjectures.AlgebraicGeometry.Hilbert.Curve`. The rank/fibre comparison is now proved locally inside the existing theorem,
using only the original public import of FiberDegree. The affine computation
follows the existing Hilbert.Curve argument, reducing to spectra and
Module.rankAtStalk_eq, and the comparison for general schemes follows by
pullback to an affine chart. No library module or public interface is
changed. The item retains its original signature and docstring. Updated the
node's proof and proof_origin to match the repaired proof.

## Proved and sorry left

`AlgebraicGeometry.finiteLocallyFree_fiberDimension_isLocallyConstant` is proved.
No sorry remains in the item and no sorry is added.
No statement or definition changes. Empty sources and zero-degree fibres require
no additional hypothesis: the rank comparison and level-set construction apply directly.

## No longer needed

Removed the cyclic proof import `WeilConjectures.AlgebraicGeometry.Hilbert.Curve`.
Its Hilbert-scheme and curve theory are not needed for this proof. The required
rank comparison is proved from FiberDegree and Mathlib, already publicly imported.
No DAG proof dependency is pruned: the Mathlib rank node
`lem-weil-pbc-finite-flat-rank-iso` is still used. No new nodes or split-offs.
The unit sk-thm-p1 statement and recorded proof steps are retained.

## Where the brief, the DAG or earlier work was wrong

The prior compile loaded existing compiled artifacts and did not expose the
source cycle caused by importing Hilbert.Curve. The landing checker correctly
rejected it. A shared-module relocation compiled successfully but the dry run
required claims on the two adapted modules; this worker's brief prohibits running
the claim tool by hand. Instead, the repair proves the comparison locally inside the existing theorem
from lower-level declarations, and removes the offending import completely.
No other modules need adaptation and no interface change record is needed.

## Second reading by E1

1. PASS: diffed the only delivered Lean module against the repository. The existing
   theorem signature is byte-for-byte identical, as is its docstring; no definition
   or public import changes. No change record is required. The scoped elaboration
   option affects the proof only.
2. PASS: compiled the module with lcompile.py without errors or warnings (2.3 s).
   Replaced the stale scratch axioms copy with the current repaired source and
   compiled it (2.1 s): #print axioms reports exactly propext, Classical.choice,
   Quot.sound. No sorry or forbidden declaration mechanism occurs in the delivery.
   Read the affine Spec.map computation, the finite/flat base-change instances,
   and the finite global-sections argument. The rank comparison uses precisely
   finite and flat; local constancy additionally uses the given lfp instance.
3. PASS: no statements were split off, no helper declarations or nodes added.
   Empty source gives rank zero; empty base makes the pointwise clauses vacuous;
   unused degrees yield empty opens and valid restrictions. No positivity or
   nonemptiness assumption is smuggled into the proof.
4. PASS: searched Sheaf, WeilConjectures and Mathlib AlgebraicGeometry for
   rank/fibre-degree and locally-constant fibre combinations. The existing
   Hilbert.Curve comparison is the same affine argument, but its import creates
   the already-returned source cycle; the local proof correctly avoids that edge.
   FiberDegree is the sole import and is needed by the public signature. The old
   proof_deps has only lem-weil-pbc-finite-flat-rank-iso, still used through its
   Mathlib rank declarations: no DAG node or module is pruned from the original
   plan. Read sk-thm-p1.json including realized: this item is below the unit's
   realized steps, and no unit statement, step, or route is bypassed or changed.
5. PASS after wording repair: the node retains its statement and proof_deps.
   Read its Mathlib rank dependency, FlatRank's rank and pullback/local-constancy
   declarations, Module.rankAtStalk_eq, FiberDegree's degree definitions and
   restriction theorem, and Hilbert.Curve's existing comparison proof. The two
   node proof steps now correctly refer to the local hEq rather than a private
   declaration or an imported finrank_eq_fiberDegree theorem. proof_origin agrees.

The local literature files are absent on this read-only machine, so I read the
primary Stacks pages [02KA](https://stacks.math.columbia.edu/tag/02KA),
[02KB](https://stacks.math.columbia.edu/tag/02KB), and
[04MH](https://stacks.math.columbia.edu/tag/04MH): the finite/flat/lfp hypotheses
are exactly the finite locally free condition, and the clopen constant-degree
restrictions match the source.

Changed only the two DAG proof-description phrases and refreshed the scratch
axiom check; the Lean proof needed no repair.
