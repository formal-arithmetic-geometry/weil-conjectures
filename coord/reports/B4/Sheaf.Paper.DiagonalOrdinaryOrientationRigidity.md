## What changed

Proved `WeilConjectures.PurityFiniteSetting.diagonalOrdinaryOrientationRigidity`
in `Sheaf.Paper.DiagonalOrdinaryOrientationRigidity`, preserving its full signature.
Two proved private helpers establish the shifted finite Tate normal form and equality
of maps from an upper-bounded object to a lower-bounded object at their common degree
by restriction to a covering family of opens. The latter uses the adopted-source
homology comparison and exact pullback/cohomology naturality, followed by joint
faithfulness of sheaf inverse images. Its argument follows the existing proved private
helper in `BundleSectionOrientationMapExt`; no dependency on that bundle theorem is added.

The main proof constructs the smooth coordinate opens over the original Y, converts
affine d-space to the ordered affine tower, obtains non-vacuous coefficient and
compact-support normalization data, and cancels the common locality isomorphism.
The DAG proof and dependencies record this argument. Only proof imports are changed;
there is no statement, definition, visibility, target or consumer change.

Validation: the complete delivered Lean module compiled cleanly with lcompile.py
(exit 0, 28.1 seconds), with no warnings. The module has no `sorry` tokens and
all lines have at most 100 characters. The delivery tool performs its independent
compile with axiom probes and packet checks.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.PurityFiniteSetting.diagonalOrdinaryOrientationRigidity`
(node `lem-pur-diagonal-ordinary-orientation-rigidity`).
Added zero holes. Zero sorries remain in the delivered module. No split-off statements.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.EtaleSheafHomFamilyGluing` and the
corresponding direct proof dependency `lem-amb-etale-sheaf-hom-family-gluing`.
Only equality detection is needed: joint faithfulness of sheaf inverse images and
injectivity of cohomology on the relevant Hom set suffice. The more general
`Sheaf.Paper.DegreeZeroDerivedMapGluing` is also unnecessary for this proof and is not
imported. All other original direct DAG dependencies remain used. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The route is mathematically valid. Its sheaf-Hom gluing step can be replaced by the
shorter proved cohomology-and-conservativity argument. The affine coordinate space
and the ordered affine tower are not definitionally equal; the proof explicitly uses
`affineTraceAffineSpaceIso` and proves its compatibility with the projection.
Affine source charts provide separatedness of the coordinate map even when Y is
not absolutely separated. The cover is indexed by X itself, so the same proof
handles empty X and dimension zero.

Searches: LeanFinder on equality of derived maps over etale covers returned general
sheaf locality lemmas, not this statement; Loogle found `JointlyFaithful` and its
`map_injective` and reflection interfaces. The msearch grep query returned zero hits.
Local rg found the exact smooth local normal form and the reusable argument in
`BundleSectionOrientationMapExt`, supplying a complete route with no new statements.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
