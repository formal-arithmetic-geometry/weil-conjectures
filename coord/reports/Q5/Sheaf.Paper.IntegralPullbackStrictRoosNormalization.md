## What changed

Moved the existing concrete definitions to IntegralPullbackStrictRoosData and publicly
reexported them from the original module. This breaks the dependency cycle while
preserving all existing names and mathematical conditions. The existing unclaimed
modules IntegralRoosChainRepresentatives, IntegralRoosResolvingCounits and
IntegralRoosAugmentationLocalization change only their public import to the data module.
Their signatures and proofs are unchanged.

Repair of returned heads 3f13967b7eb and 22e7bc4f79e: retained all 18 original
public imports and added a plain (non-public) import of
Sheaf.Paper.FiniteFreeCompletedScalarComparison (reviewer correction: the delivered
`public import` re-exported WeilConjectures.completedCoefficientMap and broke the bare
`completedCoefficientMap g` of IntegralRoosDerivedPullbackUnit). Restoring the public imports
alone did not restore the old proof-import closure. The landing gate identified
WeilConjectures.completedCoefficientMap, used by IntegralRoosDerivedPullbackUnit,
as still lost. The plain import restores its defining module to the checked import closure, and it
exposes nothing to importers.
The import-direction check confirms that this adds no cycle. No consumer proof,
definition, DAG route or hole count changes in this second repair.
The repaired seven-module sandbox compiled without diagnostics using lcompile.py --all
(result c8dbf3ec50d2bfad3248f301). The delivery command runs axiom probes and server
preflight before pushing.

The parent takes its strict comparison record from chain representatives, its K-flat
and counit clauses from resolving counits, and its completion-unit identities from
augmentation localization. Naturality proves lambda localization. Product projections
and the two cone coordinates prove the chain augmentation identity. Two remaining
normalization equations are separate named theorems with nodes.

Explicit map types bound productMap, unitR and towerCounit. The concrete bT, bU,
lamComplex and Lmap definitions have irreducible boundaries with proved component
lemmas; the parent uses their equations without expanding the chain constructions.
The original IsComparison conjunction and target theorem signature are unchanged.
All seven modules compiled together with lcompile.py. The parent profile reported
33.9 seconds of kernel checking; the development profiling option was then removed.
The delivery command performs the final compilation and preflight.

## Proved and sorry left

Closed the original hole in
WeilConjectures.IntegralPullbackStrictRoos.integralPullbackStrictRoosNormalization
by a decomposition. Original module: 1 hole before, 0 after.
Added holes (two):
- WeilConjectures.IntegralPullbackStrictRoos.integralLambdaQuotientAugmentation
  (lem-sfb-integral-lambda-quotient-augmentation): finite module augmentation identity.
- WeilConjectures.IntegralPullbackStrictRoos.integralRoosScalarLocalization
  (lem-sfb-integral-roos-scalar-localization): scalar localization equation.

The three adapted modules retain their existing holes, unchanged:
- WeilConjectures.IntegralPullbackStrictRoos.integralRoosChainRepresentatives
  (lem-sfb-integral-roos-chain-representatives).
- WeilConjectures.IntegralPullbackStrictRoos.integralRoosResolvingCounits
  (lem-sfb-integral-roos-resolving-counits).
- WeilConjectures.IntegralPullbackStrictRoos.integralRoosAugmentationLocalization
  (lem-sfb-integral-roos-augmentation-localization).

There are five holes across the delivered modules: two added and three existing.
This is a decomposition, not a claim of a net decrease in holes.

## No longer needed

The parent need not directly invoke integral coefficient-square normalization,
augmented quotient-tower existence, or scalar Roos comparison existence: the existing
chain-representative theorem supplies the same witnesses with those normalizations. The derived-unit theorem and its completion-isomorphism witnesses
are not needed for this parent proof. No global module withdrawal is claimed.
No existing module is withdrawn.
Removed the original unused proof-only imports from the extracted data module:
Sheaf.Paper.ConstantCompletionEquivalence, Sheaf.Paper.CartesianCoefficients,
Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact,
Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives,
Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit,
Sheaf.Algebra.Homology.RoosConeCalculus,
Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses,
Sheaf.AlgebraicGeometry.CondensedPullbackTensorComparison,
Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients,
WeilConjectures.Algebra.Homology.RoosComplex and
WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian.
These do not eliminate globally needed modules: the existing child statements still need
the corresponding mathematics. The parent retains all 18 original public imports
for downstream visibility, publicly imports its data module, and privately imports
the chain-representative, resolving-counit and augmentation-localization statements
and two smaller normalization steps. FiniteFreeCompletedScalarComparison is imported plainly. This only
satisfies the landing check's closure comparison; the gate's hit was a name collision.
None of the original public imports is pruned.
The twelve stale tool_uses entries on the parent node are removed: these belong
to the original ten-step proof and remain mathematically needed by the children.
They are not claimed as globally pruned nodes or modules. Removed entries:
lem-pur-ringed-site-grothendieck-abelian,
lem-sp-grothendieck-enough-injectives,
det-prop-sfb-qlbar-colimit-x-integral-limit,
lem-weil-pbc-constant-completion-equivalence,
sk-prop-sfb-cartesian-coefficients,
lem-weil-pbc-flat-scalar-restriction-kflat,
lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
def-sfb-condensed-pullback-tensor-comparison,
lem-weil-proetale-countable-products-exact,
lem-pe-roos-cone-calculus,
lem-weil-pbc-ringed-strict-tower-homotopy-limit,
lem-weil-derived-limit-roos-complex.

## Where the brief, the DAG or earlier work was wrong

The first two deliveries missed a dependency formerly reached through the old
proof-import closure. Restoring only the original public imports was insufficient:
the return at 22e7bc4f79e still identified completedCoefficientMap in
IntegralRoosDerivedPullbackUnit as lost. The second repair imports its defining module,
FiniteFreeCompletedScalarComparison, plainly; a public import breaks that consumer.

The dependency statements imported the parent's concrete definitions, so using them
in the parent formed a module cycle. The earlier data module resolves it without
changing any mathematical construction or weakening a statement.

During this session the shared derived-unit theorem was proved from smaller existing
statements. The parent uses those statements directly; the derived-unit theorem,
its proof and completion-isomorphism dependency are preserved untouched. Its existing
augmentation-localization statement already supplies the quotient-unit equation,
so no duplicate split-off statement is delivered.

The remaining finite augmentation compatibility and scalar localization equation are
strictly smaller steps of the original ten-step argument. Their edge cases include
zero and torsion modules, arbitrary unbounded complexes and noncomplete inputs;
neither adds a geometric hypothesis. Product and cone extensionality are proved in Lean.

## New nodes

lem-sfb-integral-lambda-quotient-augmentation states the finite module-unit compatibility.
Its proof evaluates the normalized lambda formula at residue 1 and uses tensor and
pullback adjunction generation.

lem-sfb-integral-roos-scalar-localization identifies scalar exchange through the specified
Roos comparisons. Its proof uses their normalization on K-injective tower resolutions,
then naturality along resolution quasi-isomorphisms.

The existing definition node def-sfb-integral-pullback-strict-roos-data is attached to
the earlier data module and lists the relocated definitions and proved API helpers.
Change record: coord/changes/Q5-integral-roos-normalization-assembly.md.

## Second reading by Q5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
