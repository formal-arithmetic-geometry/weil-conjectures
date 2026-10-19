## What changed

Recovered and repaired the returned C2 delivery (fcb0af3f45; job
223e368e86632539). Proved integralConstantModelHeart using the existing integral
Serre-closure theorem, the general homology-property triangulation/truncation API (the generic closed declaration recorded
on prop-constructible-derived-subcategory),
and the existing constructible-module essential-smallness theorem. The finite
coefficient comparison is constructed and proved in IntegralCoefficientRingComparison.
The public coefficient abbreviation, theorem signature and public imports are unchanged.

Local irreducibility of upperStarFromPoint and CondensedRing.upperStar prevents
unnecessary pullback expansion. The private general_heart helper proves the complete
abstract-coefficient result before specialization. An explicit unfold in the smallness
proof preserves the needed definitional comparison. No heartbeat or time limit is raised.
The repaired main file compiled cleanly in 19.2 seconds after final import pruning.
The final packet is also checked through lcompile.py and deliver3.py.
The continuation dry run required adding the missing LeanSearch record for the
coefficient-comparison node; LeanSearch, Loogle and source grep were run again.

## Proved and sorry left

Closed one original hole: AlgebraicGeometry.ProEtale.integralConstantModelHeart
(det-lem-int-integral-heart-triangulated). Added zero holes; zero holes remain in
the delivered modules. AlgebraicGeometry.ProEtale.integralCoefficientRingComparison
(lem-int-integral-coefficient-ring-comparison) and every private helper are fully proved.
This is a proof from existing dependency declarations, not a decomposition into new
admitted results. Existing dependency theorems keep their own proof status.

## No longer needed

Removed proof imports:

- Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
- Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
- Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
- Sheaf.CategoryTheory.SiteCoveringAxioms
- Sheaf.CategoryTheory.RingedSiteModules
- Sheaf.AlgebraicGeometry.NoetherianStratumDetection
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
- Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
- Mathlib.Algebra.Homology.DerivedCategory.ShortExact
- Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
- Sheaf.Paper.CartesianCoefficients
- Sheaf.Paper.DerivedNakayamaFirstReduction
- Sheaf.Paper.IntegralHeartLocalModel
- Sheaf.Paper.IntegralModels

The old derived-completeness/residue-reduction route is unnecessary: the existing
weak Serre-closure theorem gives the module-theoretic closure needed by the general
homology-property theorem. The existing essential-smallness theorem already implements
the stratification/subobject counting argument. The proof no longer directly needs
these old dependency nodes:

- lem-weil-l-adic-extension-integers-dvr
- sk-lem-integral-models
- det-pe-derived-nakayama-first-reduction
- lem-pur-derived-change-of-rings
- lem-weil-proetale-dbc-triangulated
- lem-weil-pbc-finite-ring-constructible-derived-origin
- det-lem-int-integral-heart-local-model
- lem-sf-derived-homology-long-exact
- def-weil-abstract-derived-category
- lem-weil-pbc-complex-ses-triangle
- def-weil-size-convention
- def-weil-pbc-proetale-site
- def-weil-pbc-sites-and-cohomology
- def-weil-sheaf-of-modules-category
- sk-prop-sfb-cartesian-coefficients
- lem-weil-pbc-noetherian-stratum-detection

The source unit's assertions and realized steps are retained; its realized arrays are
empty. These removals describe this proof's dependencies, not a claim that other targets
no longer use the same modules. No Lean module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The assigned item has a returned red-build repair in coord/repairs.txt, although the
dispatch budget metadata says repair=false. The repair record supplies the earlier
complete proof, which is reused rather than recreated. Its failing final conjunction
is now assembled in the proved abstract-coefficient helper. Expanding pullback
constructions was the remaining compile bottleneck; local irreducibility fixes it
without changing the constructions. The old nine-step plan is longer than the available
Serre-closure and homology-property route; the node now records the proof actually used.

The coefficient comparison permits any finite extension, including independent
universes via Shrink. Its scalar maps preserve norms and hence the closed unit balls;
it covers the base field case. Zero models use an explicit zero presentation, including
the empty scheme. Smallness is inherited only after proving inclusion in the ambient
constructible-module predicate. No target statement or notion is weakened.

## New nodes

lem-int-integral-coefficient-ring-comparison: the finite spectral-norm coefficient ring
is isomorphic to that of a finite subfield of the fixed algebraic closure. This is a
separate coefficient comparison, completely proved here. The isomorphism is constructed
sectionwise from an isometric ring equivalence. The search log records grep, Loogle
and Lean Finder queries; blueprint_refs.py found no matching blueprint node.
Change record: coord/changes/C2-integral-constant-model-heart-proof-context.md.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
