## What changed

Proved `CategoryTheory.InjectivelyExactSquare.boundary_square_naturality` in
`Sheaf.CategoryTheory.Abelian.RightDerived.InjectivelyExactSquareBoundarySquareNaturality`.
Added the proof-only import `Mathlib.Algebra.Homology.HomologySequenceLemmas`.
The middle vertex transformation is the explicit product of the two middle components.
Together with the outer components mapped onto the fixed injective resolution, it gives
an actual morphism of resolution short complexes. Its commutation proofs use the four
edge relations of the square morphism. Applying `HomologicalComplex.HomologySequence.δ_naturality`
and `InjectiveResolution.rightDerived_app_eq`, then cancelling comparison isomorphisms,
proves the stated equality.

The statement, universes, visibility, and existing public import are unchanged.
The existing DAG proof and its two dependencies describe precisely this argument,
so no node change is needed. The unit has no realized proof steps bypassed here.
Local single-file compilation passed without warnings. The delivery dry run checks
axioms and the remaining static requirements.

## Proved and sorry left

Closed the sole hole in `CategoryTheory.InjectivelyExactSquare.boundary_square_naturality`
(node `lem-sc-injectively-exact-square-boundary-square-naturality`).
Holes closed: 1. Holes added: 0. No `sorry` remains in the delivered module.
No new intermediate theorem or module was needed.

## No longer needed

None. No imports were removed, and both existing proof-dependency nodes remain used:
`lem-sc-injectively-exact-square-resolution-short-exact` supplies the resolution sequence
and its short exactness; `lem-weil-pbc-complex-ses-long-exact-naturality` is the Mathlib
connecting-map naturality theorem. No nodes or modules were bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The Mathlib computation lemma's actual name is
`InjectiveResolution.rightDerived_app_eq`, as the module docstring correctly records;
the node proof text informally calls it `NatTrans.rightDerived_app_eq`.
The resolution-sequence morphism commutation fields have the reverse orientation
from the square morphism fields; the proof explicitly reverses the equalities.
Searches through LeanFinder and Loogle found the existing Mathlib connecting-map
naturality theorem, and grep confirmed the resolution computation lemma.

## Second reading by R3

1. **Interface and accidental changes.** Compared the delivered module with the repository
version. The theorem statement, universes, visibility, and existing public import are byte-for-byte
unchanged; the only module change is the proof-only `HomologySequenceLemmas` import and proof.
Verdict: pass.

2. **Compilation and axioms.** Compiled the module with `lcompile.py` without errors or warnings.
The file has no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or
`debug.skipKernelTC`; `#print axioms` reports only `propext`, `Classical.choice`, and
`Quot.sound`. Verdict: pass.

3. **Statements and split-offs.** No statement was added or changed and no split-off theorem is
present. The existing target theorem is proved directly from the two recorded dependencies, so
there are no new nodes or hollow definitions to assess. Verdict: pass.

4. **Shortest route and pruning.** The proof uses the existing short-exact resolution theorem and
the Mathlib connecting-map naturality theorem, then the right-derived computation lemma. The
proof-only import is minimal for the naturality lemma; no old proof dependency or realized unit
step is bypassed. Verdict: pass.

5. **DAG agreement.** The existing node's `proof`, `proof_deps`, and `proof_origin` match the
resolution-sequence morphism, `δ_naturality`, and derived-functor transport written in the proof.
The unit's `realized` route is preserved. Verdict: pass.

Changed after reading: appended this review record only; no Lean code or DAG metadata required
repair.
