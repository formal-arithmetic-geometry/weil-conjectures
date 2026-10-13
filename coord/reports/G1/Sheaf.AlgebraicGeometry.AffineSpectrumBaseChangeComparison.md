## What changed

Added Sheaf.AlgebraicGeometry.AffineSpectrumDirectImageCoordinates. Its four
explicit constructions are affineSpectrumInversePullbackEquivalence,
affineSpectrumDerivedDirectImageIso, affineSpectrumForwardPullbackIso and
affineSpectrumBaseChangeSourceIso. They use the selected universal-property
pullback comparisons and pinned derived adjunctions. No data is chosen from mere
existence of an arbitrary coordinate isomorphism. The only Mathlib proof import
is CategoryTheory.Adjunction.Mates.

Added Sheaf.AlgebraicGeometry.AffineSpectrumMateCompatibility to isolate the bare
mate equation for those fixed constructions, before any coefficient morphism is
supplied. The item's proof combines that equation with naturality of the
direct-image coordinate iso, Functor.map_comp and cancellation of the target iso.
The original theorem statement, universes and visibility are preserved. Updated
the parent node's proof route to match these imports and the Lean argument.

The full sandbox compiles cleanly in import order through lcompile.py --all.
The first dry run verified compilation and probes, then requested LeanSearch
records for both new nodes. Those searches were run and returned Internal Server
Error; the unavailable service is recorded without a match verdict. LeanFinder,
Loogle and source grep remain recorded. The independent second reading is for
the next worker, as specified in the brief. The second deliver3.py --no-push run
printed OK (commit 0be67783ba): compilation and preflight pass except for that
second reading. Nothing was pushed.

## Proved and sorry left

The draft replaces the single hole in
AlgebraicGeometry.affineSpectrumCoordinates_comparison by a complete proof from
AlgebraicGeometry.affineSpectrum_baseChange_mate_compatibility.

Exactly one new hole is left:
AlgebraicGeometry.affineSpectrum_baseChange_mate_compatibility
(lem-pc-affine-spectrum-mate-compatibility), in its own new module.
All four coordinate definitions have explicit constructions and no new holes.
This is a decomposition: one upper hole closed, one lower hole added, net zero.
The intermediate has no Kprime or phi; the naturality and composition argument
handling that second object and its morphism is supplied by the item's proof.
The compiler has verified the three delivered modules in import order, with no
errors or warnings (39.5 s, 2.7 s and 4.6 s including compiler-slot wait).

## No longer needed

Removed the earlier sandbox draft's public import of
Mathlib.CategoryTheory.Adjunction.Unique; the construction uses the proof-only
Mathlib.CategoryTheory.Adjunction.Mates import instead. This is a draft cleanup,
not pruning of an existing library module or node.

No existing imports or modules are pruned. The parent no longer lists
lem-pc-ringed-spaces-derived-pullback-composition and def-pc-derived-base-change-map
as direct proof dependencies; both remain used by the new construction and mate nodes. The selected pullback-composition and
adjunction route remains needed through the new construction module and bare
mate theorem. No unit statement or proof step is bypassed: the parent unit
sk-thm-picard-semicon has empty realized lists.

## Where the brief, the DAG or earlier work was wrong

An early scope mistake briefly placed scratch edits in the read-only clone and
compiled a temporary sandbox copy of the missing baseline dependency. The clone
edits were restored, and that source copy and its local compiled artifacts were
removed. The clean full compile and dry runs use the shared dependency. Only the
three listed sandbox modules and their node records are proposed for delivery.

The previous attempt was blocked by the absent compiled module
Sheaf.AlgebraicGeometry.AffineSpectrumDerivedCoordinates. That object file is now
present in the shared baseline; no baseline dependency is adapted or delivered.
The untyped local selections in the old draft were expensive to elaborate.
Explicit function types for the selected composition/identity comparisons and
adjunctions, together with explicit category and arrow types in the equivalence
construction, make its four constructions compile within the per-file limit.
The old target draft also rewrote associativity in the wrong direction and
attempted naturality rewriting before exposing the target iso component. The
revised proof explicitly identifies that component and reassociates after the
bare mate equation.

The existing base-coordinate and top-coordinate transport lemmas do not give
the exact four spectrum comparisons and the specified transported coefficient
morphism. The new definitions supply those fixed comparisons; the new theorem
carries the remaining coherence calculation. Source checked: Stacks Tags 08HY
(the counit definition), 0D5S (pullback composition) and 0DJ8 (affine reduction).

Edge checks: no inverse of a base-change map is used. Only the coordinate maps
are inverted, using affineness. The bare identity requires commutative squares,
not cartesian squares, flatness, boundedness or quasi-coherence. Empty schemes,
zero rings and zero coefficient objects require no separate assumption. The
identity would fail for arbitrary coordinate isomorphisms, so its statement
names the fixed constructions. No arbitrary witness is selected in a definition.

## New nodes

 def-pc-affine-spectrum-direct-image-coordinates records the real constructions
of the inverse-spectrum pullback equivalence, conjugate direct-image coordinate
isomorphism, forward pullback comparison and source comparison. Its module has
no sorry and creates no additional theorem hole.

 lem-pc-affine-spectrum-mate-compatibility records the bare mate equation for
these fixed constructions. It has only one coefficient object and no coefficient
morphism. Its docstring gives the transpose, conjugate-counit, pullback-coherence
and triangle-identity argument from Tags 08HY and 0D5S. The coefficient naturality
step remains in the parent module as a Lean proof, not in this new hole.

## Second reading by G1

1. Compared the delivered item module with the repository version. The theorem signature, hypotheses,
   universes, and conclusion are unchanged byte for byte; only the proof and its proof-only import changed.
   Verdict: passed.
2. Compiled all three delivered modules with `lcompile.py --all`. The files compile without errors or
   warnings. The only remaining `sorry` is the named theorem
   `affineSpectrum_baseChange_mate_compatibility`; it has a docstring and matching DAG node. No
   forbidden declarations or hollow definitions were found. Verdict: passed.
3. Checked the split-off statement against its use and searched the repository and available Mathlib
   declarations. It is the strictly smaller bare mate identity for the fixed coordinate constructions,
   with no coefficient morphism; it is not a restatement of the parent theorem. The construction node
   contains explicit data rather than an arbitrary existence witness. Verdict: passed.
4. Reviewed the proof route and imports. The parent proof uses the bare mate theorem, direct-image
   coordinate naturality, functoriality, and cancellation. The proof-only `Mathlib.CategoryTheory.Adjunction.Mates`
   import is minimal for the construction module; no existing target dependency or unit route is bypassed.
   Verdict: passed.
5. Checked the DAG records against the Lean declarations and proof. The parent node records the new
   dependency and the two new nodes carry their statements, sources, proof plans, and Lean records.
   The unit's realized route is unchanged. Verdict: passed.

Restored the original indentation of one conclusion line so that the existing signature is byte for byte identical. Added this report section; no mathematical content or DAG content changed during second reading.
