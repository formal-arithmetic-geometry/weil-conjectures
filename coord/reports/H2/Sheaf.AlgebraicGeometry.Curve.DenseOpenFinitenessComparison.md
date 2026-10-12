## What changed

Proved AlgebraicGeometry.IsCurve.dense_open_finiteness_comparison without changing
its signature or existing docstring. All four implications are complete Lean proofs.
Proof imports are private to the module. The proof transports constructibility with
the existing Scheme.isConstructibleSheaf_integral_iff, constructs a monomorphism G -> F
from the open-closed counit, and transfers invertible and primary torsion by injectivity
on geometric stalks. The primary/invertible case is proved by an elementwise coprimality
argument followed by stalk conservativity; it gives zero cohomology and hence finiteness.

Added three modules, each with one public theorem and one node. IntegralOpenExtensionComparison
is proved using restriction, Functor.lanCompIsoOfPreserves and sheafComposeNatIso.
DenseOpenIntegralCohomologyFiniteness is proved from the open-closed short exact sequence,
finite boundary cohomology, two exact Ext segments and ShortComplex.Exact.ab_finite.
DenseOpenIntegralBoundaryFiniteness isolates the remaining geometric step.
The existing item's proof/proof_deps/proof_origin now follow these Lean proofs.

The mathematical source was read directly at Stacks Tags
[0GJA](https://stacks.math.columbia.edu/tag/0GJA),
[095L](https://stacks.math.columbia.edu/tag/095L) and
[03S5](https://stacks.math.columbia.edu/tag/03S5).
The local clone has the literature lists but not etale-cohomology.tex.
No chapter or unit statement or route has changed: the dense-open open-closed reduction
in sk-thm-p1 is still used. No definition, existing statement or target has changed.

## Proved and sorry left

Proved the original declaration AlgebraicGeometry.IsCurve.dense_open_finiteness_comparison
(node lem-pbc-j2-dense-open-finiteness-comparison): 1 of 1 original sorries removed.
Proved AlgebraicGeometry.Etale.integral_open_extension_comparison
(node lem-pbc-h2-integral-open-extension-comparison).
Proved AlgebraicGeometry.IsCurve.dense_open_integral_cohomology_finiteness
(node lem-pbc-h2-dense-open-integral-cohomology-finiteness).
All private helpers are proved, with no sorry in their definitions or proofs.

The sole sorry added and left in this delivery is
AlgebraicGeometry.IsCurve.dense_open_integral_boundary_finiteness
(node lem-pbc-h2-dense-open-integral-boundary-finiteness).
Its proof is exactly `by sorry`, with a complete natural-language proof and source.
This is strictly the finite-boundary step, not the original four conditional implications.
Previously landed dependencies can still contain sorry; this delivery does not change them.
In particular the proof uses the existing constructibility bridge, rather than restating it.

All four files compiled together through lcompile.py in import order, without warnings.
The deliver3.py no-push dry run printed OK after local compilation, axiom probes,
server compilation of independent new modules, and static preflight checks.
No full-library build or direct lake invocation was used.

## No longer needed

No original public statement import was removed. The original item's following
proof-only imports were removed:
- Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit
- Sheaf.AlgebraicGeometry.CurveCoefficientPair (already a public transitive dependency)
- Sheaf.AlgebraicGeometry.PullbackCohomologyLongExactLadder
- Sheaf.Paper.ZeroDimensionalCohomology (moved to the remaining boundary theorem)
- WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint (available transitively)
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriek (available through the boundary plan)
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs (available transitively)
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
- WeilConjectures.SixFunctors.Finite.Exact (moved to the remaining boundary theorem)
- WeilConjectures.SixFunctors.Finite.Stalk

The second reader also removed the redundant new import Mathlib.Data.Int.GCD from
the item, and redundant Mathlib.Algebra.Category.ModuleCat.Abelian and
Mathlib.Algebra.Category.Grp.Abelian imports from IntegralOpenExtensionComparison.
ConcreteCoefficients already supplies those coefficient instances; its public import
is needed to elaborate the statement's open extension functors.
The boundary theorem explicitly imports its remaining geometric proof-plan modules,
including ZeroDimensionalCohomology, ZeroDimensionalSectionsStalks,
EtaleSheafHExtDerivedComparison and Finite.Exact. These have not been globally pruned.

The finiteness argument no longer uses these old direct proof dependencies:
- def-weil-pbc-cohomology-pullback
- def-weil-pbc-extension-pullback
- lem-weil-pbc-cohomology-pullback-derived-unit
- lem-weil-pbc-pullback-cohomology-long-exact-ladder

In particular Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit and
Sheaf.AlgebraicGeometry.PullbackCohomologyLongExactLadder are not needed by this
finiteness argument. The code uses Mathlib exact Ext sequences directly; it does not
need naturality of a pullback ladder or any base-change cohomology map.
The remaining old direct edges removed from the item's proof_deps are:
- def-weil-geometric-point
- def-weil-pbc-constructible-torsion
- def-weil-pbc-curve-setting
- def-weil-pbc-direct-image
- def-weil-pbc-etale-cohomology
- def-weil-pbc-inverse-image
- def-weil-scheme-morphism-properties
- lem-weil-pbc-zero-dimensional-cohomology
- lemma-weil-pbc-finite-direct-image-exact
- lemma-weil-pbc-finite-stalk-formula

These definitions stay in the statement dependency closure where appropriate;
the geometric and cohomological results are recorded on the new boundary node as needed.
The finite stalk formula is not separately needed: the zero-dimensional sections/stalks
comparison supplies the product directly. This is pruning of direct proof edges only.

The recorded geometric-point convention does not need a separate proof edge:
stalk functors and conservativity already supply the points actually used.
The cohomology comparison, finite direct image and finite-boundary stalk calculation
are retained in the new boundary node, not claimed as globally pruned.
Definitions still used by the statements remain in stmt_deps even when they are no
longer separately listed in proof_deps.

The nearby DenseOpenCohomologyFiniteness and DenseOpenPrimaryFiniteness modules were
searched but are not imported: they require a finite coefficient ring (and reducedness),
whereas the coefficient ring here is ULift Z and the curve need not be reduced.
No separate DenseOpenHighCohomology/High theorem is needed: finite boundary cohomology
in all degrees already suffices for both finiteness transfers by exactness.
These nearby modules were not former direct dependencies and are not claimed as globally
unreached; the maintainer decides global reachability.

## Where the brief, the DAG or earlier work was wrong

The DAG's geometric argument is valid, but its pullback ladder and derived-unit proof
edges are unnecessary for finiteness alone. The exact Ext sequence suffices.
The existing finite-ring dense-open finiteness theorem does not directly fit the integral
coefficient encoding, so using it with ULift Z would introduce a false finite-ring instance.
The required constructibility bridge was initially absent from the local compiled snapshot;
I waited for the refresh, which supplied it, and imported its existing declaration.
LeanSearch requests returned Internal Server Error; these are recorded as unavailable,
not as evidence that no match exists. Loogle, LeanFinder, repository searches and Mathlib
source inspection were used. A preliminary source tag 03S0 was checked and corrected to
03S5 in the new coefficient-comparison file before delivery.

The boundary statement was checked on U=X, the empty curve, the zero sheaf, and
zero-dimensional curves (where a dense open is the whole curve). These produce zero
boundary cohomology. The general boundary may be treated after reduction: nilpotents
do not affect the etale topos. No properness or ambient reducedness is silently assumed.
The primary-zero helper uses both primality and CharP k p; characteristic zero therefore
never enters that branch. Invertible torsion transfers only from F to G; the reverse
conditional implication uses the actual torsion alternative rather than assuming its converse.

The first dry run rejected the node signatures because extraction stopped at the
first let-bound `:=`; the node records were repaired to contain the entire theorem
signature. It also required a Second reading by H2 section, which the dispatcher
brief explicitly reserves for the second worker and prohibits this worker from writing.
After correcting the signatures, deliver3.py printed OK. Its explicit no-push
exception accepts this sole preflight finding and reserves the section for the second
reader, as required by the brief. Nothing was pushed.

The closed source theorem lem-fin-extension-by-zero is used as the already-proved
constructibility tool; its use does not replace any unit-level step.

## New nodes

lem-pbc-h2-integral-open-extension-comparison, in
lean/Sheaf/AlgebraicGeometry/Curve/IntegralOpenExtensionComparison.lean, is proved.
Its statement compares the two actual coefficient encodings across an open immersion
without imposing density, torsion or constructibility.

lem-pbc-h2-dense-open-integral-cohomology-finiteness, in
lean/Sheaf/AlgebraicGeometry/Curve/DenseOpenIntegralCohomologyFiniteness.lean, is proved.
It makes the exact-sequence glue explicit, including the degree-zero injection and
successor-degree connecting segment.

lem-pbc-h2-dense-open-integral-boundary-finiteness, in
lean/Sheaf/AlgebraicGeometry/Curve/DenseOpenIntegralBoundaryFiniteness.lean, is the only
new remaining sorry. It states precisely the finite boundary term required by the
exact-sequence proof and keeps the finite direct image/zero-dimensional source route.

No change record is required: no existing signature or definition was changed.


## Second reading by H2

1. **Existing interface: pass.** Read all four delivered modules and diffed the item
   against the repository. The original theorem signature and its docstring are
   byte-for-byte unchanged. The same P, hP, dense open U and four conditional C4/C5
   implications remain. No definition or target changed. The existing node differs
   only in proof, proof_deps and proof_origin. New theorems have separate new modules.
2. **Lean proofs and trust: pass, with one explicitly open boundary theorem.** All four
   files compile together through lcompile.py. There is exactly one literal sorry,
   the named public dense_open_integral_boundary_finiteness; no forbidden declaration
   or hollow definition occurs. Scratch-copy #print axioms checks covered the original
   theorem, all three new public theorems, all three private torsion helpers and the
   private cohomology equivalence. The helpers and coefficient comparison use only
   propext, Classical.choice and Quot.sound. The original theorem, cohomology transfer
   and boundary additionally use sorryAx, as expected from the open boundary and
   existing dependencies. Thus this removes the original local sorry; it does not
   certify the original theorem free of transitive sorries.
3. **Split statements: pass.** Independently read Stacks Tags 0GJA, 095L and 03S5.
   The coefficient comparison is valid for every scheme and open: the coefficient
   equivalence commutes with restriction, Kan extension and sheafification. The
   cohomology equivalence follows from finite boundary cohomology and the exact Ext
   segments, including the separate degree-zero injection. The remaining theorem
   is strictly the boundary calculation, not the original comparison under another
   name: it has no open-extension finiteness assumption and says only that i_*i^*F
   has finite cohomology. Its natural-language proof and node explain the finite
   rational-point calculation. Checked U=X, empty X, zero F, and zero-dimensional
   curves (dense U=X); nonreduced X is allowed because the boundary may be reduced
   without altering its etale topos. Positive-characteristic primary/invertible
   stalks are zero by coprimality; p=0 is excluded by primality. Independent searches
   used LeanFinder "étale sheaf supported on finitely many closed points has finite
   cohomology", Loogle "Finite (CategoryTheory.Sheaf.H _ _)", and grep
   "boundary.*(finite|cohomology)|finite.*stalk|closedComplement", plus repository
   searches by cohomology, stalk and boundary. The first Loogle syntax was invalid
   and was retried with the valid query above. No matching ready-made theorem was
   found. Read DenseOpenBoundaryCohomology, DenseOpenCohomologyFiniteness,
   DenseOpenPrimaryFiniteness, ZeroDimensionalCohomology and
   ZeroDimensionalSectionsStalks: the finite-ring results do not apply to ULift Z.
   Closing the boundary still needs the geometric and direct-image comparisons,
   rather than a short application of a theorem already in the library.
4. **Shortest route and pruning: pass after import/report repairs.** The original
   proof genuinely combines constructibility, a mono on stalks, the unconditional
   finiteness transfer and the primary/invertible zero case. The cohomology argument
   uses exact Ext segments directly; a pullback ladder is unnecessary. Checked the
   complete fourteen-element old-minus-new proof_deps list against No longer needed.
   Corrected the false claim that the original module had no proof-only imports and
   listed all ten removals, distinguishing moved or transitive modules from pruning.
   Removed redundant Int.GCD, ModuleCat.Abelian and Grp.Abelian imports, recompiling
   after the removal. Retained the item's necessary IdealSheaf.Subscheme import:
   the new cohomology module's private boundary import does not re-export it.
   Public imports retained in the new coefficient comparison provide the functors
   and coefficient instances its statement needs. Read dag/units/sk-thm-p1.json,
   especially step (i) and realized: the dense-open open-closed reduction still
   realizes the same curve-calculation step, with no unit or chapter bypass.
5. **DAG and report: pass after restoring reachability.** Read all four node records.
   Every proof_deps set equals the union of its proof steps' uses; the statements,
   Lean declarations, sources and recorded argument agree. The new nodes contain
   the required creation, blueprint, search, chapter/unit and full Lean signature
   fields. The boundary proof-plan modules were missing from its imports, so the
   second reader restored private imports of AlgClosed.Basic, Noetherian,
   EtaleSheafHExtDerivedComparison, ZeroDimensionalSectionsStalks,
   ZeroDimensionalCohomology and Finite.Exact. These keep the stated geometric route
   reachable while its theorem remains open. No node or change record needed repair.

Second-reading changes: restored the boundary proof-plan imports; removed three
redundant imports; corrected and completed No longer needed; appended this review.
No mathematical proof body or statement was changed. Scratch axiom probes were
removed before delivery. The final deliver3.py dry run and delivery supply the
local/server compilation, all-declaration axiom scan and static preflight checks.
