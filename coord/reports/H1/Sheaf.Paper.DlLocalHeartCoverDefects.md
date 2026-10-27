## What changed

Replaced the hole in WeilConjectures.dlLocalHeartCoverDefects by an explicit assembly
from two strictly smaller statements. DlLocalHeartAbelianEvaluation supplies only
abelianity and additive exact evaluations (original Steps 1--7).
DlLocalHeartCoverBasisZero supplies only the pointwise implication from cover vanishing
to vanishing on each basis open (the geometric portion of original Step 8).

The main proof derives the canonical kernel and cokernel comparison instances,
preservation of homology and exactness, and the literal middle-defect comparison
using Mathlib leftHomologyIsoCokernelLift and mapLeftHomologyIso. It proves global zero
detection by extensionality of identity arrows and derives all three cover-defect
iff statements by transporting IsZero through these comparisons. Every existing
signature, universe, public import and definition is preserved. Two private proof
imports replace the original proof imports. The original DAG proof now records this
assembly and each remaining construction has its own node and module.

Validation: both new modules compiled in the delivery check (41.7 and 41.5 seconds).
The final assembly compiled without warnings in 10.9 seconds using lcompile.py
(result c86032b7f5366a72c505b1e8). A static interface comparison confirms no existing
signature or public-import change; only the item theorem body changes. The initial
remote temporary-directory disk error cleared on the required delivery attempt.

## Proved and sorry left

The sole original hole is WeilConjectures.dlLocalHeartCoverDefects
(lem-dl-a1-local-heart-cover-defects). Its replacement proof compiles without warnings. This is a decomposition,
not a net proof or a claim of zero reachable sorry axioms.

Two new holes are left as whole named public theorem proofs:

- WeilConjectures.dlLocalHeartAbelianEvaluation
  (lem-dl-a1-local-heart-abelian-evaluation), in DlLocalHeartAbelianEvaluation.
- WeilConjectures.dlLocalHeartCoverBasisZero
  (lem-dl-a1-local-heart-cover-basis-zero), in DlLocalHeartCoverBasisZero.

No other holes are added. Closed original holes: 1, by a compiling reduction; new holes: 2. Textual item holes:
1 before, 0 after; packet holes: 2 after. This is a decomposition, with net hole
change +1 until the two construction lemmas are proved.

## No longer needed

Removed direct proof imports Sheaf.Paper.AdicStratifiedPullbackInterface and
Sheaf.CategoryTheory.Triangulated.TStructure.HeartAbelianKernelSplitting from the
assembly module. Their mathematical input remains needed in the new componentwise
construction node: neither declaration nor module is withdrawn or claimed pruned
from the target closure. The original direct proof dependencies
lem-per-adic-heart-pullback-fibres, prop-weil-heart-abelian,
lem-per-adic-stratified-pullback-texact and def-sp-abelian now occur in the
construction nodes instead. Their old top-level direct tool_uses entries are removed;
lem-sp-exact-functor-preserves-homology and def-weil-pbc-exact-sequence stay.
No DAG node or module is unnecessary in the overall mathematical route. No public
imports are removed, no source-library declaration is edited, and no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement is changed or disputed. The current typed interfaces do
not supply the whole componentwise compatible-family construction in a single
existing declaration; raw PBC hearts and the literal sf heart also require their
recorded coefficient-presentation transport. The construction lemma states this
missing portion without asserting cover detection. The second lemma isolates only
basis-open vanishing; global zero detection and defect detection are proved in the
assembly. Edge cases checked in the statements: empty T and cover, repeated opens,
infinite indexing types, zero maps, identity maps, and unrelated finite coefficient
fields on different basis opens. No compactness assumption on T is introduced.

An initial remote temporary-directory disk failure cleared during delivery. No launcher
tool or shared-repository file was modified.

## New nodes

lem-dl-a1-local-heart-abelian-evaluation: the componentwise abelian construction and
exact evaluation, strictly the algebraic portion of the original proof. Its module
contains the explicit interface structure and one named theorem hole with a complete
proof in words. The remaining cover clauses are absent.

lem-dl-a1-local-heart-cover-basis-zero: only the forward cover-to-every-component
vanishing implication, proved in words by geometric fibres and basis neighbourhoods.
It requires no global abelian structure and states none of the three defects.
The final theorem proves the global zero iff and transfers it to all defects.

No existing public interface changes, hence no change record or consumer adaptation
is required. New modules are imported only for proofs.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
