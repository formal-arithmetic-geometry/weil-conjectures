## What changed

The unchanged existence theorem now combines a Tate chosen-lift construction with a
proved normalization reduction. New modules are
`Sheaf.RingTheory.SelfTorConormalComparisonTateConstruction`,
`Sheaf.RingTheory.KoszulAugmentationLiftHomotopy`, and
`Sheaf.RingTheory.SelfTorConormalComparisonHomotopyNormalization`.
The existence module adds only a proof import of the normalization module.

The first worker's three `True` certificate fields were removed. The replacement
`AlgebraicGeometry.TateComparisonCertificate` states that for each tuple and
projective resolution there exists an actual augmentation lift satisfying the
specified wedge formula. The full normalization for arbitrary lifts is derived
from chain homotopy, with a real inductive proof using projectivity of Koszul
exterior powers and exactness of the target. The definition contains no chosen
data and no proof holes. No existing statement or definition was changed.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.selfTorConormalComparison_exists`
(node `new-r4-self-tor-conormal-comparison-existence`). Its proof depends on the
remaining Tate construction hole.

New hole added, and the only delivered `sorry`:
`AlgebraicGeometry.tate_selfTor_conormal_map`
(node `new-r4-self-tor-conormal-comparison-tate-construction`). The docstring
contains the complete Tate/product/chosen-lift argument and its sources.

New auxiliary theorems proved without `sorryAx`:
`AlgebraicGeometry.koszul_augmentation_lifts_homotopic`
(node `new-r4-koszul-augmentation-lift-homotopy`) and
`AlgebraicGeometry.tate_comparison_homotopy_normalization`
(node `new-r4-self-tor-conormal-comparison-homotopy-normalization`).
The second reading closed the first worker's normalization hole and replaced its
vacuous construction statement with a substantive one. Compared with the
repository, one hole is closed and one is added: net zero, a decomposition, not a
complete proof of comparison existence. No whole-library progress is claimed.

All four delivered modules compile locally in import order with no warnings.
Scratch `#print axioms` checks show only `propext`, `Classical.choice`, `Quot.sound`
for the certificate definition and both proved auxiliary theorems. The original
existence theorem and the Tate construction additionally depend on `sorryAx`.
The delivery preflight also checks every delivered declaration.

## No longer needed

None of the original imports, proof dependencies or prerequisite modules was
pruned; the original existence node had empty `proof_deps`. The first worker's
redundant direct Tate construction import was removed from the existence module;
it is reached through the normalization module. Byte-identical copies of
`Sheaf.Paper.KoszulComplex`, `Sheaf.RingTheory.ConormalExteriorModule`, and
`Sheaf.RingTheory.SelfTorConormalComparisonPredicate` were removed from the delivery
set, and are still imported from the library. No existing DAG node was bypassed.

## Where the brief, the DAG or earlier work was wrong

The first worker's certificate did not assert any property of c: each of its
fields was `True`. Its normalization theorem consequently asserted the predicate
for every linear map. This is false: for A = integers, I = 0 and n = 0, the zero
map fails the quotient-unit formula for the empty wedge. The original split is
refused and replaced, including both deficient node records. The discarded
scratch witness likewise merely contained the entire normalization as a field;
it is not delivered or used.

The original existence node names the Tate and homotopy steps but had no
`proof_deps`. The delivered node records now name the actual construction and
proved normalization reduction, with a separate node for its inductive homotopy
lemma. The new normalization lemma is a reduction, not an assumption of the
conclusion. The construction only establishes the chosen-lift formula;
independence from other Koszul lifts is fully proved.

## New nodes

`new-r4-self-tor-conormal-comparison-tate-construction`: the comparison map with
actual chosen augmentation lifts and the wedge formula; its named construction
hole remains. Its source is Stacks Tags 09PQ and 00LS(1).

`new-r4-koszul-augmentation-lift-homotopy`: any two maps from the Koszul complex to
the same projective resolution with equal degree-zero augmentations are
homotopic. This is proved by inductively lifting residual cycles, following
Stacks Tag 00LS(2) and Mathlib's resolution comparison proof, without assuming
that the source Koszul complex is a resolution.

`new-r4-self-tor-conormal-comparison-homotopy-normalization`: the certificate's
chosen-lift formula holds for arbitrary augmentation lifts. This is proved using
the preceding theorem, `Functor.mapHomotopy`, and `Homotopy.homologyMap_eq`.

Each new node records its actual Lean signature, source, three search kinds,
proof steps, dependencies, origin, chapter and unit. Searches were rerun through
msearch.py and recorded in searches.jsonl. LeanSearch returned Internal Server
Error; semantic/type searches and source searches were read. No change records
are needed: all replaced auxiliary statements and the certificate were new,
unlanded work, and existing signatures are unchanged.

## Second reading by V2

1. Compared each existing sandbox module with the repository using diff. The
   existence theorem signature is byte for byte unchanged; its sole changes are
   the proof and a plain proof import. The three dependency copies were byte
   identical and removed from the delivered set. There are no interface changes
   or forced adaptations. Verdict: pass after repair.
2. Compiled all four delivered modules with lcompile.py, and checked scratch
   copies with `#print axioms`. Only the single named Tate construction theorem
   contains `sorry`; there are no forbidden declarations or holes in data.
   Both homotopy theorems use only standard axioms. Verdict: pass, with the
   explicitly reported construction hole.
3. Rejected the vacuous `True` certificate and false normalization implication.
   Checked the genuine replacement statements on n = 0, r = 0, I = 0, I = A,
   the zero ring, and characteristic two. The chosen-lift construction uses the
   empty product in degree zero and strict odd-square-zero commutativity;
   the homotopy proof requires no source exactness or regular sequence. Searched
   Mathlib, library and upstream sources independently. Mathlib's liftHomotopy
   requires a source resolution and cannot directly apply here; its induction
   was adapted to the free Koszul complex. The general homology-map invariance
   already exists and is used rather than re-stated. Verdict: true, substantive
   split; one Tate hole remains, and the other first-worker hole was closed.
4. Read the top theorem and its entire import route. The reduction consists of
   chosen-lift existence, a proved lift homotopy, and a proved normalization
   transport. Pruned the redundant new import, kept all original imports, and
   used plain imports for proof-only dependencies. The unit
   `dag/units/sk-thm-picard-duality.json` was read; its realized statement and
   step lists are empty, and no unit-level route or record is changed. This is
   a split below the unit level. Verdict: pass as a decomposition, net zero.
5. Matched every node's Lean signature and proof to the delivered files.
   Corrected the nonexistent predicate dependency ID, bogus construction proof
   for the normalization node, missing searches, and nonverbatim signatures.
   The original node changes only proof, proof_deps and proof_origin.
   Verdict: pass after repair.

Second reading changed the certificate to actual chosen-lift normalization,
proved the inductive Koszul homotopy and its normalization transport, repaired
all new nodes, minimized imports, removed unchanged delivery copies, and
corrected the report's accounting. The original existence signature and
existing definitions are unchanged.
