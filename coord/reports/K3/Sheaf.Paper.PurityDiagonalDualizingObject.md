## What changed

Reduced WeilConjectures.PurityFiniteSetting.existsUnique_diagonalDualizingObject,
with its original signature, to compatible affine-target charts and three strict
substeps. The Lean assembly obtains the charts from diagonalOrientationRefinement,
uses their Agrees equations to glue an ordinary isomorphism, verifies its coordinate
normalization, transports it through diagonalDualizingComparison, and proves the
unique pro-etale presentation by ordinary rigidity. It uses no arbitrary witness
for a definition. The existing final definition still chooses the uniquely
specified isomorphism from exactly the original theorem.

Extracted the pre-existing definitions and diagonalUnitPlus verbatim into
Sheaf.Paper.PurityDiagonalDualizingData, publicly reexported by the item. This lets
the new supporting theorem modules import the predicates without a cycle. All
old public imports are retained through this module; no consumer adaptation or
meaning change is needed. The change record is
coord/changes/K3-diagonal-dualizing-data-extraction.md.

The new gluing statement requires a given normalized chart family and its Agrees
proofs, and prescribes affine restrictions only; it asserts no coordinate-counit
normalization or uniqueness. The normalization statement assumes that local
realization and proves the coordinate equations, with no existence clause. The
rigidity statement only tests equality of two already normalized ordinary
isomorphisms. None is the original theorem under another name. The main proof
combines these different conclusions and transports the result to the pro-etale
site in Lean.

## Proved and sorry left

Original hole eliminated from the item:
WeilConjectures.PurityFiniteSetting.existsUnique_diagonalDualizingObject
(blueprint thm-pur-diagonal-dualizing-object).

This is a decomposition, not a completed proof of smooth purity. Of the one
original sorry, one is reduced; three new named public sorry theorems remain:

- WeilConjectures.PurityFiniteSetting.diagonalOrdinaryOrientationGluing:
  lem-pur-diagonal-ordinary-orientation-gluing, in
  Sheaf.Paper.DiagonalOrdinaryOrientationGluing.
- WeilConjectures.PurityFiniteSetting.diagonalOrdinaryOrientationNormalization:
  lem-pur-diagonal-ordinary-orientation-normalization, in
  Sheaf.Paper.DiagonalOrdinaryOrientationNormalization.
- WeilConjectures.PurityFiniteSetting.diagonalOrdinaryOrientationRigidity:
  lem-pur-diagonal-ordinary-orientation-rigidity, in
  Sheaf.Paper.DiagonalOrdinaryOrientationRigidity.

There are zero sorry tokens in the item's final theorem proof and zero in the
extracted data module. The three holes have complete proof plans in their docstrings
and nodes, each occupying its own module. Existing dependencies' holes are
unchanged. This packet's direct count is one hole closed and three holes added
(net minus two); no claim of positive net sorry progress is made.

## No longer needed

No library declaration or module is withdrawn. The unit's diagonal, DNC and
vector-bundle route is preserved in the normalized charts and the gluing and
normalization substeps. The original affine-target and degree-zero gluing nodes
remain needed below the new gluing statement. The item uses
lem-pur-diagonal-orientation-refinement directly; its original other proof
prerequisites are used within the new substeps, not pruned out of the DAG.

The following original private imports no longer need to be direct imports of
the item or its extracted data; the new proof lemmas import their own actual
interfaces. This is direct-import pruning only, not a claim that these modules
are globally unused:

- Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing
- Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
- Sheaf.AlgebraicGeometry.DiagonalRegularPureCodimension
- Sheaf.CategoryTheory.LocalizedModuleExactForSystems
- Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
- Sheaf.Paper.CartesianCoefficientTwists
- Sheaf.Paper.CohomologicalSmoothnessTheorem
- Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
- Sheaf.Paper.DerivedPullbackTensorHom
- Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
- Sheaf.Paper.PurityDiagonalBaseChangeCompared
- Sheaf.Paper.PurityDncInvariance
- Sheaf.Paper.PurityFiniteSetting
- Sheaf.Paper.PurityNormalCone
- Sheaf.Paper.PuritySectionInvariantIntrinsic
- Sheaf.Paper.SfCommonStageWeilCohomology
- Sheaf.Paper.VectorBundlePurity

All seven original public imports are preserved verbatim in the reexported data
module. Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful remains a private
import of the extracted data because its definitions use the single-complex API.
The withdrawn empty module Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing
is replaced by the existing EtaleSheafHomFamilyGluing in the rigidity step's proof
context, not redeclared.

## Where the brief, the DAG or earlier work was wrong

The existing named proof dependencies do not directly conclude the predicate
DiagonalOrientationNormalization. The chart refinement theorem supplies normalized
beta and DNC factors and restriction equations on affine target opens, whereas the
item asks for an ordinary-etale realization, its universally quantified coordinate
counit equations, and uniqueness. The three new nodes expose precisely this
remaining glue. The original proof plan's degree-zero step cannot be applied to
unshifted arbitrary complexes; the new statements and proof plans explicitly
shift by -2d, and use degree-zero maps only.

The source-library smooth purity theorem
AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift was read. It
requires absolute separatedness of the base and gives an unnormalized Nonempty
iso, so it cannot establish this full-domain canonical statement. Descendant
chartOrdinaryOrientation in DiagonalDncChartNormalization is selected from this
very theorem and would be circular here. No such route is used.

Checked the empty source, empty affine cover, rank d=0, and overlaps of affine
opens in a nonseparated target. Gluing on an overlap is tested on its affine
refinements, never by assuming the overlap is affine. The standard coefficient
unit and even-shift maps fix the tensor-zero case. Ordinary rigidity uses the
canonical normalized t, D and N, which exist independently, to compare the two
universally quantified normalization equations on an etale coordinate cover.

Searches: leanfinder for smooth exceptional purity returned only ordinary scheme
pullback coherence; loogle Smooth with Iso and Mathlib grep for smooth purity
returned no match. LeanSearch for shifted sheaf gluing returned TopCat section
gluing; LeanFinder for shifted etale equality returned dense-subsite sheaf
comparisons. Exact query summaries are recorded on each new node. Existing
DegreeZeroDerivedMapGluing and EtaleSheafHomFamilyGluing are reused as lower tools.

## New nodes

def-pur-diagonal-dualizing-data records the existing data and predicates extracted
unchanged into Sheaf.Paper.PurityDiagonalDualizingData; no new object is chosen.

lem-pur-diagonal-ordinary-orientation-gluing records gluing of compatible specified
local diagonal/DNC/vector comparisons to an ordinary realization. It retains the
old affine-target, refinement and degree-zero gluing dependencies.

lem-pur-diagonal-ordinary-orientation-normalization records the coordinate-counit
compatibility for a given realized local composite, with the actual normalized
DNC and vector-integration factors.

lem-pur-diagonal-ordinary-orientation-rigidity records equality of two normalized
ordinary orientations, using smooth coordinate covers and shifted sheaf-map
equality. It constructs no orientation. All new nodes inherit the original
sec-smooth-purity chapter and sk-thm-smooth-purity unit; the blueprint unit itself
and its route are unchanged.

Validation: all five Lean modules compiled through lcompile.py. After correcting
the main proof local-instance style warnings, its final version compiled cleanly
in 19.7 seconds. The tool parser verified every original declaration signature
and every original non-theorem-proof body unchanged across the extraction. Node
signatures, dependency existence, proof-dependency unions, and 100-character Lean
line widths were checked. Delivery preflight will recompile the complete set
with its axiom and direct-hole probes before pushing.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
