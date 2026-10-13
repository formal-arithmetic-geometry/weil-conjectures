## What changed

Proved `AlgebraicGeometry.Scheme.Modules.scalarExtCup_inverseImage_first` in
`Sheaf.AlgebraicGeometry.ScalarExtCupInverseImageFirst`, with its signature unchanged.
Added the proof-only import `Sheaf.CategoryTheory.ExtExactFunctorIdentityComparison`.
The existing public import is retained. Two proved private helpers reduce tensoring
with the unit to postcomposition by the inverse right unitor and identify
`scalarInverseUnitIso.hom` with the canonical adjunction oplax unit.

The latter helper expands the uniqueness comparison of constant-sheaf adjunctions,
then uses the already proved pushforward unit formula on underlying presheaves.
The final proof is Ext composition algebra and oplax right-unitor coherence.
Scoped heartbeat limits accommodate elaboration of the composite adjunctions;
the complete module compiled cleanly in approximately 27 seconds, below the 60-second limit.
Updated the existing node's proof, proof dependencies, and proof origin to match this route.
No statement, definition, visibility, or other module was changed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.scalarExtCup_inverseImage_first`
(node `lem-sc-scalar-ext-cup-inverse-image-first`).
Both private helpers `rightUnitTransport` and `unitComparison` are fully proved.
No sorry remains in the item; no hole was added and no statement was split off.
The argument applies in every degree, including degree zero, to zero coefficient maps,
zero sheaves and empty schemes. It imposes no extra hypotheses.

## No longer needed

No imports were removed and no existing node or module was pruned.
The planned general natural transformation from tensorRight-unit followed by inverse
image to inverse image followed by tensorRight-unit, and its localization/shift
naturality proof, are unnecessary: the proved right-unitor Ext identity comparison
handles both tensor transports independently. No new module for general Ext
naturality or exact-functor composition comparison is needed for this item.
The unit record `sk-prop-av-cube` has empty realized lists, and this simplification
changes no unit statement or realized step.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically valid but longer than necessary. Its proof search
predates the available proved declaration `Abelian.Ext.exactFunctorIdentityComparison`.
The original declaration docstring is preserved; the node now records the actual proof.
The imported comparison belongs to another unit but is already proved and is used only
as a general categorical tool; it bypasses no geometric unit route.

Searches: msearch LeanFinder found Ext.Map transport APIs, Loogle found
`rightUnitor_naturality`, and msearch grep returned no exact scalar comparison.
Direct rg searches in both library roots found the proved identity comparison and its
use in ScalarExtCupDegreeZero. The needed pushforward unit component formula was found
in WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal. No new nodes were needed.

## Second reading by U4

1. PASS: Compared the entire delivered module with the repository version. The sole
   existing theorem signature is byte-for-byte identical, as is its docstring. Changes
   are the proof-only import, two proved private helpers, scoped heartbeat settings,
   and the target proof. No definition, public signature, or visibility changed;
   no change record is needed.
2. PASS: Locally compiled the delivered file without errors or warnings (37 seconds).
   Compiled a scratch copy with explicit `#print axioms` for the target and both
   helpers (31 seconds): each uses exactly `propext`, `Classical.choice`, and
   `Quot.sound`. There is no sorry, forbidden declaration, or new data construction.
   Read the Ext composition cancellations, composite-adjunction comparison, and
   final oplax right-unitor calculation; these prove the original equality.
3. PASS: No statement was split off and no hole was added. Both private helpers
   are proved, strictly smaller calculations. The identities work for degree zero,
   zero morphisms and zero objects, and empty schemes: the proof neither cancels
   an arbitrary coefficient map nor assumes a nonzero section or inhabited space.
4. PASS: Checked the existing identity-comparison theorem and the related
   ScalarExtCupDegreeZero proof, and searched the library for alternative unit
   comparisons and right-unitor transport declarations. The existing general Ext
   identity theorem is used directly; no shorter existing scalar-unit comparison
   was found. Both imports are needed, with the new one correctly proof-only.
   The original proof dependency is retained, so the list of pruned old nodes is
   empty. Read sk-prop-av-cube's realized lists (all empty); no realized step or
   geometric unit route is bypassed.
5. PASS: Compared both node JSON files. Only `proof`, `proof_deps`, and
   `proof_origin` differ. Their three steps match the two helpers and final Ext
   calculation. The dependency union is exactly the coefficient-operations node
   and the existing Ext identity-comparison node. No new node is needed.

Second reading changed only this report to record the independent checks; the
Lean proof and node needed no repair. Holes closed: one; holes added: zero.
