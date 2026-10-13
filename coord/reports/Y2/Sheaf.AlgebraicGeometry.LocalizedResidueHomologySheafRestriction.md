## What changed

Proved `AlgebraicGeometry.nonempty_localizedResidueHomology_sheaf_restriction_iso`
without changing its statement. Six proved private categorical helpers handle right Kan
extension transport, pullback transport between localizations, exact functor source
transport, homology transport, exact pullback computation, and tensor pullback along
scheme isomorphisms. The main proof composes these with the existing derived pullback
composition theorem and the residue-square identity.

Replaced the proof-only import of `DerivedPullbackOpenRestrictionUniverses` with
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` and
`Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived`. Updated the item's
DAG proof and dependency list to match this argument. Elaboration options are
scoped to individual proofs; no file-level commands or public interfaces change.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.nonempty_localizedResidueHomology_sheaf_restriction_iso`
(node `lem-sc-localized-residue-homology-sheaf-restriction`).
No sorry remains in this module. No holes or new nodes were added. This is a proof
from the existing library declarations, including the derived pullback specification
and composition comparison; it does not claim their entire dependency closure is proved.

## No longer needed

Removed the proof-only import `Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses`
and the proof dependency `lem-pc-derived-pullback-open-restriction-universes`.
The proof does not use that module or its affine pullback comparison route: exact open
restriction computes derived open pullback by the derived universal property directly.
This is pruning of this item's dependency edge; other targets may still reach the module.
All four public imports are retained because they supply the original statement's API.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The original plan's independent-universe open restriction
comparison is unnecessary for this square. The useful shortest route is the exactness
of ordinary open restriction and uniqueness of a left derived functor.

The categories written as `Scheme.Modules` and as `SheafOfModules (moduleRings …)`
need explicit category and derived-category arguments in several functor comparisons;
the supplied localization universe must not be silently replaced by the standard one.
The proof transports those choices explicitly. All comparisons are natural isomorphisms,
so no arbitrary object is chosen from an unproved existence statement. Empty opens have
no point x; zero objects and unbounded complexes require no extra hypotheses.

Searches: LeanFinder on residue pullback versus open restriction found only underived
residue-square identities; Loogle found the exact residue-square identity used here;
project grep found no direct theorem for this comparison. The source statements at
https://stacks.math.columbia.edu/tag/08DW and
https://stacks.math.columbia.edu/tag/0D5S were read.


## Second reading by Y2

1. Interface: compared the complete module with the repository using `diff -u`,
   then compared the bytes from the public theorem keyword through its `:= by`.
   The sole existing declaration's signature and docstring are unchanged. All
   four public imports remain unchanged; the additional helpers are private
   theorems, and both new imports are proof-only. No definition or change record
   was added. Verdict: pass.
2. Proof: compiled the delivered module with `lcompile.py` without errors or
   warnings. Scanned it for sorry, axiom, unsafe, opaque, implemented_by, extern
   and skipKernelTC: none occurs. Read every helper and the main composition.
   The derived-pullback specifications fix the underived functors by their object
   and morphism equalities and the derived functors by their universal property;
   choices here supply comparisons, not arbitrary data definitions. Checked the
   target's axioms in a full scratch copy: exactly propext, Classical.choice
   and Quot.sound, with no sorryAx. The delivery tool also probes every
   declaration. Verdict: pass; this target proof has no inherited sorryAx.
3. Splits and alternatives: no new sorry statements or nodes were introduced.
   The six private helpers are proved reductions, not aliases of the target.
   Read the source for rightKanExtensionUniqueOfIso, the localization-based
   isLeftDerivedFunctor_of_inverts, and the upstream exact-functor comparison
   module. An independent Loogle query for rightKanExtensionUniqueOfIso found
   precisely the uniqueness tool already used. Project searches using Kan
   extension transport, exact left-derived equivalence and localization/homology
   terminology found no direct replacement for the independent-universe square.
   Empty U admits no x; U = S and isomorphic residue schemes reduce to equivalence
   and identity comparisons. Zero complexes need no boundedness assumption.
   Verdict: pass; no further split or proof repair is needed.
4. Route and pruning: the main proof first combines exact derived restriction,
   uses left-derived uniqueness for exact open pullback, then the existing
   exists_derivedPullbackComposition on the residue square, and finally exact
   residue pullback commutes with homology. Localization transports preserve
   the supplied universe w explicitly. The only removed old proof dependency is
   lem-pc-derived-pullback-open-restriction-universes, correctly listed above;
   its comparison is replaced by the exact universal-property calculation.
   The public imports supply the unchanged statement; the two added private
   imports supply mapDerivedCategoryCompIso/mapDerivedCategoryNatIso and
   isLeftDerivedFunctor_of_inverts. Read sk-prop-av-cube.json: this item and the
   removed dependency are not entries of its realized fields (those fields are
   already empty in the baseline). This local reduction does not replace its
   general-cube-theorem step or change any unit record. Verdict: pass for this
   delivery; it does not assert that the baseline realization metadata is complete.
5. DAG: compared the node JSON with the repository. Only proof, proof_deps and
   proof_origin change. The four steps match the exact restriction calculation,
   localization transport, derived composition and residue homology comparison.
   Their uses union is exactly the recorded proof_deps; statement, stmt_deps,
   lean signature, blueprint ancestry and unit are unchanged. No new node needs
   auditing. Verdict: pass.

Second reading changed only this report: added the independent checks and their
limits. The Lean proof and node edits were retained as written.
