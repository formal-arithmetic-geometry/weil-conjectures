## What changed

Replaced the invalid earlier homology-map restatement with an explicit reduction to finite rows.
`Sheaf.Algebra.Homology.FirstQuadrantTotalComparison` constructs the finite complex shape
0,...,N, its predecessor-closed embedding, and the columnwise stupid truncation projection.
It proves that the projection preserves total homology below N, that the truncation retains
the horizontal quasi-isomorphisms, and that naturality transfers the finite-row comparison.
For homology degree n it uses N=n+1. All these private helpers are fully proved.

The proof imports `Sheaf.Algebra.Homology.FirstQuadrantTotalComparisonFinite` and
`WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns`; the latter supplies the
existing coproduct isomorphism criterion and stupid-truncation projection API.
Both original public imports and every existing signature are unchanged.
Local single-file compilation passes for both delivered modules, without warnings.

## Proved and sorry left

Closed the original hole in `HomologicalComplex₂.quasiIso_totalMap_of_columns`
(node `lem-sc-first-quadrant-total-column-comparison`). Added one strictly bounded subproblem:
`HomologicalComplex₂.quasiIso_totalMap_of_columns_of_finite_rows`
(node `lem-sc-finite-row-total-column-comparison`), the only remaining `sorry` in this delivery.
This is a decomposition: one upper hole closed and one lower hole added, net zero.
The finite-row theorem assumes an actual global vertical upper support bound; the original
has none. The construction, locality proof, and two-out-of-three transfer are real Lean proofs,
not a conversion of quasi-isomorphism into an equivalent homology-map statement.

## No longer needed

The earlier attempt's `FirstQuadrantTotalComparisonHomology` module and
`lem-sc-first-quadrant-total-homology-map` node were removed from the sandbox and are not delivered.
No original import was removed. The new proof no longer uses the original plan's integer
mapping-cone bicomplex, cone-total comparison, or spectral-sequence vanishing argument.
`thm-sp-double-complex-spectral-sequences` is removed from this node's direct proof dependencies;
its module is still the existing public import providing nonnegative total complexes, so no
claim is made that the entire module leaves the targets' import closure.
The total-complex definition dependency remains, and the finite-row comparison is now needed.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox proposed only an equivalent homology-map formulation of the whole theorem,
and incorrectly called this a strictly lower component. It also wrote the second reader's section.
Both are replaced here. The new route uses finite support before comparison; it needs no
functorial spectral-sequence comparison, which the existing existential spectral-sequence API
would not supply. The original statement is unchanged and no statement is disputed.

Edge cases checked: degree zero uses prev(0)=0; the choice N=n+1 retains the outgoing differential
needed for homology in degree n. At an omitted row both horizontal complexes are zero, so the
map is invertible. N=0 in the new lemma has one graded quotient. The finite cutoff definitions
choose no data from unproved existence theorems. The unit record has empty realized lists;
no unit-level step or statement was bypassed.

## New nodes

`lem-sc-finite-row-total-column-comparison`, in
`Sheaf.Algebra.Homology.FirstQuadrantTotalComparisonFinite`, isolates comparison for double
complexes with a uniform finite vertical support bound. Its docstring and node give the
finite filtration, quotient identification, and descending five-lemma induction. Searches
were run with msearch: LeanSearch was unavailable, LeanFinder found generic criteria, Loogle
had no matching identifier, and grep found no Mathlib total-comparison theorem. Searching
the imported blueprint for finite rows found no duplicate of this statement.
There are no interface changes or forced adaptations, and no change records.

## Second reading by E1

1. Compared both delivered modules against the repository with diff. The finite-row module
   is new. The existing theorem's complete signature, universes, surrounding variables and
   visibility are byte-for-byte unchanged. No existing definition is changed. Both added
   imports are private to proofs. Verdict: pass; no change record is needed.
2. Compiled both modules in import order with lcompile.py --all: no errors or warnings.
   Scanned all delivered Lean for forbidden declarations and sorry: the only sorry is the
   named finite-row theorem listed above. In a scratch copy, #print axioms shows only
   propext, Classical.choice, Quot.sound and sorryAx for the two public comparison theorems.
   The constructed rowCutMap and its total degree-locality theorem use only the three
   allowed axioms. The projection uses concrete restriction and extension functors, not
   an arbitrary witness chosen from an unproved existence theorem. Verdict: pass, with
   the documented finite-row hole; this remains a decomposition, net zero holes.
3. Read the finite-row statement, docstring and node against Stacks Section 12.25, including
   its second filtration and finite-diagonal convergence. The descending finite filtration
   has horizontal complexes as quotients; any conventional translation sign is removed
   by the degreewise sign isomorphism. Five-lemma comparison gives the claim. Checked
   N=0, zero rows, q>N, n=0 and the necessary outgoing term n+1. Repeated independent
   searches with “finite vertical strip”, Loogle “QuasiIso, HomologicalComplex₂”, and
   Mathlib grep “finite.*(row|column)|quasiIso.*(total|filtration)”, plus rg on the library.
   No duplicate natural-number finite-row theorem was found. The integer-indexed
   total.quasiIso_map_of_finitely_many_columns is relevant infrastructure, but requires
   extension, transposition and totalization identifications unavailable as a direct
   specialization here; closing that bridge is not a few-minute proof. The new lemma
   has a global finite vertical bound and is strictly smaller than the unbounded item.
   Verdict: pass; no additional split is introduced.
4. Read the proof top down: explicit truncation, preservation of horizontal comparison,
   finite-row comparison, three-term homology locality, and naturality/two-out-of-three.
   This is a real reduction. BicomplexColumns is needed for isIso_mapMap_apply and the
   truncation API; the original public imports supply the signature and natural-number
   HasTotal instance. No import is unused. The old direct spectral-sequence proof node
   is listed under No longer needed; no module is claimed pruned from the import closure.
   The unit sk-thm-picard-duality has empty realized lists, so this reduction bypasses
   no recorded unit statement or step. Verdict: pass.
5. Compared the existing node with its repository version and read the new node's fields.
   Existing proof/proof_deps/proof_origin record exactly the new reduction, and the new
   node records the finite filtration argument with source, searches, creation record,
   matching Lean signature, chapter, unit and blueprint provenance. No other existing
   node field is changed. Verdict: pass.

Changed the main theorem's stale cone-and-spectral-sequence docstring to describe the
actual finite-row reduction, and clarified its source citation. No mathematical proof,
statement, definition, import or node needed repair. Appended this independent review.
