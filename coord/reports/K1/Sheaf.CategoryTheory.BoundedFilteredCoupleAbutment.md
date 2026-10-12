## What changed

Reduced `CategoryTheory.boundedFilteredComplex_coupleAbutment` to one strictly smaller
finite-cocone exact-couple theorem, with its original signature and docstring preserved.
The main module constructs the cohomology colimits with explicit objects and maps, constructs
the shifted image filtration, proves its formula and finiteness, and proves separatedness,
exhaustiveness and the inverse-limit property. It uses the existing proved
`weakConvergence_comparison` and checks the final graded-piece reindexing.

Added `Sheaf.CategoryTheory.FilteredCohomologyDiagonalColimit`: the explicit diagonal map
and a fully proved cocone equation and colimit universal property. Its colimit object is
cohomology itself; no object is chosen from an unproved existence theorem.

Added `Sheaf.CategoryTheory.FiniteCoconeExactCouple`: a single remaining theorem about
stationary cycles/boundaries and the canonical weak convergence maps, for arbitrary exact
couples with isomorphic lower cocone tails and zero upper D tails. Its hypotheses are
verified in the main proof. Added proof-only imports of these two modules.

## Proved and sorry left

Closed the original hole in `CategoryTheory.boundedFilteredComplex_coupleAbutment`
(node `lem-sp-bounded-filtered-couple-abutment`). This is a decomposition, not a completed
sorry-free proof: one upper hole closed and one lower hole added, net zero holes.

Fully proved `CategoryTheory.filteredCohomologyDiagonal_isColimit`
(node `lem-sp-filtered-cohomology-diagonal-colimit`), including compatibility of all index
transports. All private helpers are proved. The explicit diagonal-map definition has no hole.

The only sorry added or left in the delivered modules is
`CategoryTheory.BigradedExactCouple.finiteCocone_weakConvergence`
(node `lem-sp-finite-cocone-exact-couple`). Its entire proof is `by sorry`; its docstring and
node contain the complete intended argument. No sorry remains in the item's module.

All three modules compiled locally in import order with `lcompile.py`, without warnings.
The retry on 2026-10-13 took 8.5, 5.9, and 39.3 seconds respectively, within the
60-second per-file limit; the earlier load-related timeout did not recur.
The delivery dry run printed OK (second reading pending; nothing pushed). This establishes
that the combination of the reduction steps proves every clause of the original statement.

## No longer needed

Removed redundant proof-only imports `Sheaf.CategoryTheory.ExactCouple` and
`Sheaf.CategoryTheory.Filtration`. Their definitions remain used through public statement
imports, so neither module nor its definition node leaves the targets' import closure.
No whole module or original proof-dependency node is claimed pruned.
The original `def-sp-exact-couple` dependency remains: the reduction uses its D terms
and the exact-couple structure; the direct imports are redundant, not the definitions.

The proof does not use the first-page identification, the page-couple identification, or
the gamma compatibility: the weak convergence is a generic finite-tail exact-couple fact.
All those hypothesis binders are preserved. The required public statement imports remain.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The previous plan's reliance on hGamma for the infinite-page
comparison is unnecessary: canonical weak convergence follows from the finite diagonal
cocone tails and exactness alone. The new route keeps the finite-tail convergence step.
The unit's `realized` fields contain no bound node for this auxiliary result and are unchanged.

Checked the source online at https://stacks.math.columbia.edu/tag/012W (Lemma 12.24.11),
and its TeX label `lemma-biregular-ss-converges` in the upstream `homology.tex`.
The node source paths to the Stacks tex and blueprint prose are absent on this machine;
the new nodes explicitly mark their detailed exact-couple specialization as agent-written.
LeanSearch returned an Internal Server Error; the actual unavailable searches are recorded.
LeanFinder and source grep searches ran for each new statement and found no matching lemma.

Edge cases checked: the zero category/zero complex, a filtration with equal whole and zero
steps, a filtration supported at arbitrary negative indices, and independently varying
bounds in different total degrees. No first-quadrant assumption is introduced. The generic
remaining theorem does not assert finiteness or inverse-limit completeness of its colimits;
those properties are proved for the actual cohomology filtration in the main module.

## New nodes

`lem-sp-filtered-cohomology-diagonal-colimit`, in
`dag/nodes/sec-abelian-varieties/lem-sp-filtered-cohomology-diagonal-colimit.json`, carries the
explicit inclusion maps and their fully proved diagonal colimit theorem. It isolates the
first part of the original node's first proof step.

`lem-sp-finite-cocone-exact-couple`, in
`dag/nodes/sec-abelian-varieties/lem-sp-finite-cocone-exact-couple.json`, carries the remaining
stationary exact-couple comparison. It neither constructs cohomology objects nor asserts
image-filtration finiteness, separation, exhaustiveness, inverse limits, or the final
cohomology graded-piece identification. These are genuine combining arguments in the item.

No existing statement, definition, signature, or visibility changed. No forced adaptations
or change record is needed.

## Earlier second reading (a previous round; superseded)

1. Signatures: pass. I compared the delivered main module against the repository version. The
existing target declaration and all binders are unchanged byte for byte; the two auxiliary modules
are new declarations only. No definition is hollow and no public interface was weakened.

2. Proof and trust: pass with the declared decomposition. All three modules compile with
`lcompile.py`; the only `sorry` is the named theorem
`CategoryTheory.BigradedExactCouple.finiteCocone_weakConvergence`, whose node and docstring
state the remaining argument. There are no forbidden declarations. The proved diagonal theorem
uses only the permitted foundational axioms; the target additionally depends on the declared
`sorry` theorem.

3. Statements: pass. The diagonal colimit theorem and finite-cocone exact-couple theorem are
strictly smaller than the target and preserve the needed hypotheses. The explicit colimit object
is cohomology itself, so no arbitrary witness is selected. Zero, constant, shifted, and
independently bounded filtration cases are consistent with the statements.

4. Route and pruning: pass. The proof uses the explicit diagonal cocone, finite filtration
properties, inverse-limit construction, and the existing convergence comparison. The removed
proof-only imports are unnecessary, while all public statement imports remain. The unit's
realized route is unchanged.

5. DAG consistency: pass. Node proof fields and dependencies match the Lean proof, including the
exact-couple definition dependency and both new nodes. No statement or definition change record
is required.

Changed only this report section; no Lean files or DAG records required repair.

## Second reading by K1

1. Unchanged interface: PASS. Compared the complete delivered main module with the
repository using diff, and separately compared the original theorem signature as bytes.
All original binders, hypotheses, conclusion, visibility and docstring are unchanged.
The auxiliary modules are absent in the repository. The existing node changes only
`proof`, `proof_deps` and `proof_origin`. No change record is needed.

2. Proof and trust: PASS as a decomposition. Recompiled all three modules in import
order through lcompile.py, without errors or warnings (7.3, 8.9 and 36.8 seconds).
Scanned every delivered Lean file for forbidden declarations and holes: the sole hole
is the reported named finiteCocone_weakConvergence theorem, with its proof docstring
and node. Printed axioms of the original theorem and all new public declarations
in a scratch module. The explicit diagonal map and colimit theorem use only
propext, Classical.choice and Quot.sound; the remaining theorem and the original
theorem additionally use sorryAx. No arbitrary data witness is selected: A has
cohomology as its explicit object, G is an explicit shifted image filtration, and
L's GLB/LUB conditions determine its subobjects uniquely.

3. Split statements: PASS. The remaining theorem removes the cohomology construction,
image-filtration formulas, finiteness, separation, exhaustiveness, inverse limits
and final reindexing from the original obligation. It is a strict subargument,
not a renamed target. Checked the exact-couple bidegrees: the incoming cycle bound
is on total degree p+q+1, and the outgoing boundary bound on p+q; bounds are allowed
to vary independently. Eventually cycles equal ker(initial f), boundaries equal
initial g applied to ker(cocone map), and both canonical quotient maps have kernel
image(incoming alpha)+ker(cocone map). Zero objects, a single filtration jump,
negative shifts, and degree-dependent tail bounds cause no extra assumptions.
The source's finite-tail argument was checked at Stacks tag 012W. Independent
LeanFinder searches used “bounded exact couple eventually constant cycles canonical
associated graded abutment” and “colimit integer sequence isomorphism constant left
tail compatible cocone”; Loogle searched IsColimit with CategoryTheory.IsIso.
Reviewed the eventually-constant candidates and searched the local Sheaf, upstream
and Mathlib spectral-sequence sources. No existing declaration closes the remaining
exact-couple theorem. The Mathlib colimit candidates require constructing an ordered
diagram and do not shorten the direct consecutive-arrow induction.

4. Route and pruning: PASS. Read the entire combining proof, including both integer
inductions, the zero/whole homology images, explicit cocone transports, and the final
graded reindexing. HalfPlaneWeakConvergence, HalfPlaneConvergence and
AbutmentImageFiltration require additional half-plane vanishing and cannot be used
here. The original four proof-dependency nodes remain used and none is pruned.
The two removed direct proof imports are redundant via ExactCoupleConvergence.
Tested removing the auxiliary module's direct public homology import: compilation
then failed in its signatures for homology and homologyMap, establishing that it is
a statement import; restored it. The unit sk-prop-av-pqf-finite has empty realized
statement/step lists, unchanged by this delivery; no realized route is bypassed.

5. DAG consistency: PASS. Checked all three nodes against their Lean declarations,
explicit constructions, proof steps and source attribution. Each proof_deps list
is exactly the union of its proof steps' uses. Both new nodes have source, complete
proof plan, searches, creation record, blueprint provenance, chapter, unit and
verbatim Lean statement records. The existing node retains all non-proof fields.

Changed only this report by adding the current second reading. The attempted import
removal was reverted; no delivered Lean or DAG repair was needed. One original hole
is closed by one strictly smaller new hole: net zero, a decomposition.
