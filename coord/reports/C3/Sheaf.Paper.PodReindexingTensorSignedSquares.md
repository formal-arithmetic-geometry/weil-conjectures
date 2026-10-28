## What changed

Repaired WeilConjectures.podReindexingTensorSignedShifts_tensorSquares in
Sheaf.Paper.PodReindexingTensorSignedSquares: require SY/SX.Generators and
SY/SX.Model for the specified source/target Roos shifts. Arbitrary shift data
cannot satisfy the old assertion. The two square conclusions are unchanged.
The only caller, Sheaf.Paper.PodReindexingTensorSignedShifts, passes its existing
h₅, h₆, h₇ and h₈. Its signature, visibility and remaining proof stay identical.
Change record: coord/changes/pod-tensor-signed-square-normalization-c3.md.

The item chooses good representatives using the existing localization, constructs
the shifted presentations from Q.commShiftIso and a.inv/b.inv, proves both
presentation compatibilities, obtains the four normalized paths and the two
strict tower equalities, then cancels the reindexed tensor presentation.
Proof imports are private. Public imports are unchanged.
The new statements preserve sharing in their dependent path formulas with
cleanup.letToHave disabled. Local transparency attributes keep the large tensor
and Roos constructions folded, while both respectTransparency options remain
true in the changed item and new modules. The 60-second limit is unchanged.

Validation by lcompile.py: PodTensorShiftRoosPathNormalization compiled in 47.1 s;
PodTensorShiftStrictTowerSquares in 27.6 s; the final item, with profiling removed,
in 54.8 s; its adapted direct importer PodReindexingTensorSignedShifts in 5.9 s.
All four have passed their single-file checks within 60 s. The only remaining source holes are the two declared split obligations.

## Proved and sorry left

This is a statement repair and decomposition, not a completed proof of the
original (unnormalized) claim. The original module had one hole. Its corrected
WeilConjectures.podReindexingTensorSignedShifts_tensorSquares now has a complete
proof from two strictly lower named statements. The private goodRepresentative
helper is proved from integralOperationsGoodLocalization_isLocalization and
Localization.essSurj. The adapted caller retains its existing complete proof.

Holes removed from the item: podReindexingTensorSignedShifts_tensorSquares
(node lem-pod-reindexing-tensor-signed-shift-squares-r3). Its old signature was
false and was corrected; do not count the old claim as proved unchanged.
Holes added and remaining in this packet (two):

- WeilConjectures.podTensorShift_strictTowerSquares in
  Sheaf.Paper.PodTensorShiftStrictTowerSquares, node
  lem-pod-tensor-shift-strict-tower-squares-c3.
- WeilConjectures.podTensorShift_roosPathNormalization in
  Sheaf.Paper.PodTensorShiftRoosPathNormalization, node
  lem-pod-tensor-shift-roos-path-normalization-c3.

Each has proof exactly := by sorry, its source and full proof in words in its
docstring, and a matching DAG node. Neither is the original theorem under
another name: the first compares entire strict chain towers without localization;
the second computes each derived path separately without assuming or concluding
equality of the strict paths. The real proof combining them is in the item.
Net source-hole change: one hole removed, two added (decomposition; net -1).
No definition contains sorry. No axioms or arbitrary data choices were added.

## No longer needed

No existing public import, declaration or module is removed or withdrawn.
The item does not directly use lem-pur-kflat-total-tensor-model
(Sheaf.Algebra.Homology.KFlatTotalTensorModel): its inputs already carry the good
representative property, so tensor K-flat closure is not needed in this step.
It does not directly use lem-pod-reindexing-signed-roos-shift
(Sheaf.Paper.PodReindexingSignedRoosShift): D already specifies both signed Roos
shifts and their laws, so this step does not construct new shifts. These two old
proof-dependency edges are replaced by the two explicit chain/model steps.
No global pruning claim is made; other consumers may still need these modules.
The integral-operations-well-defined dependency remains, for good localization.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (old signature): PodTensorSignedShift stores arbitrary tower
and derived isomorphisms. Its Generators and Model laws are separate predicates.
The old tensorSquares theorem assumed neither. A sign twist of only SX.left
changes one path, including at g=id and r=0 on a nonzero tensor object. The parent
core theorem already supplies the four necessary laws, so the repair adds no
assumption to the parent or to a target. The node's old prose also had the
malformed binder D : PodCompletionReindex l E g D; this is corrected.
The old docstring blueprint id omitted the node's actual -r3 suffix.
The unit sk-def-weil has no realized proof step bypassed by this reduction.

## Statement corrected

lem-pod-reindexing-tensor-signed-shift-squares-r3 now restricts SY and SX to
signed generator/model normalized data. The sole DAG citer,
lem-pod-reindexing-tensor-signed-shifts, still holds: its core construction gives
the four laws and its Lean proof now supplies them. The statement_change record
contains the old statement, changed proof/dependencies, source and complete
citer list. Its by field uses the legacy schema's required "C3 stage 2" spelling;
this packet is stage 3.

## Forced adaptations

Sheaf.Paper.PodReindexingTensorSignedShifts is the only direct importer/caller.
The added arguments are supplied on the existing tensorSquares application line
using h₅ h₆ h₇ h₈ from the immediately preceding core destructuring. The theorem
signature and every other line are preserved. The original application otherwise
leaves hs a function awaiting these four proofs, so hs.1 and hs.2 are ill-typed.
The original source was compiled against the final corrected item. It failed
in 5.4 s at line 77, columns 9 and 31, with the following compiler error:

```text
Invalid projection: Projections cannot be used on functions, and
  hs
has function type
  PodTensorSignedShift.Generators l E SY →
    PodTensorSignedShift.Generators l E SX →
      PodTensorSignedShift.Model l E SY D.shiftSource →
        PodTensorSignedShift.Model l E SX D.shiftTarget → ...
```

Only line 74 changes: append h₅ h₆ h₇ h₈ to the existing application. The adapted
text was restored byte-for-byte to the version that compiled in 5.9 s above.

## New nodes

lem-pod-tensor-shift-strict-tower-squares-c3 states the two strict chain-tower
squares on good complexes. It isolates the homogeneous generator and Koszul-sign
calculation before Roos realization; its source is blueprint dual-Tate
compatibility Steps 1 and 5, with the tensor generator conventions of Stacks
011G and 07A4. Searches found generic graded tensor and CommShift declarations,
not this normalized project-specific square.

lem-pod-tensor-shift-roos-path-normalization-c3 states four separate path formulas
on good presentations. It isolates functoriality, representative comparison,
Roos naturality and shift descent; it asserts no equality between the two strict
paths. Its source is the same blueprint Steps 1 and 5 and Stacks 07A4/0941.
LeanSearch, Loogle/LeanFinder and Mathlib/project source searches are recorded.
Edge cases checked in the formulas and proofs in words: negative and zero
shifts, zero complexes, empty sites and arbitrary shifted presentation isomorphisms.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.PodReindexingTensorSignedShifts": "6b991a123c3a7eb8a3bdd6fd3932b97cc7dc92e5", "Sheaf.Paper.PodReindexingTensorSignedSquares": "29e079d03685bfbe82c1a68c3e3da5af95a54de6", "Sheaf.Paper.PodTensorShiftRoosPathNormalization": "13ec6b3db89807d5d05a058e1bfa6e4241937e36", "Sheaf.Paper.PodTensorShiftStrictTowerSquares": "14056489320ff2d886ebee9bee1262cd53acb8ef"}, "results": {}, "time": "2026-10-28T08:22:43+0800", "transitive": 0, "version": 1}
```

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
