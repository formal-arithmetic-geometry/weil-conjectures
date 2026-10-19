## What changed

Proved both original declarations in Sheaf.AlgebraicGeometry.ConstructibleProEtaleClassical,
without changing their signatures. The proof converts the actual intrinsic constant models
into fixed-module constant sheaves, upgrades finite generation to finite presentation over
the lifted Noetherian ring, and applies finiteLocalSystemsTwist on each stratum. The proved
stratified essential-image induction then gives global classicality. Canonical pullback
composition and Zariski locality give the locally constructible statement.

Removed unnecessary finite-coefficient assumptions from the unclaimed modules
Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequence and
Sheaf.Paper.ProEtaleStratifiedEssentialImage; their proofs are unchanged.
In Sheaf.Paper.ProEtaleConstantModulePullbackEncoding, retained the published finite
proEtaleModuleRestriction_pullback and added proEtaleModuleRestriction_pullback_of_isIso,
which explicitly assumes invertibility of the specified coefficient map. Its combining
proof is unchanged. The item imports ProEtaleConstantRingOperations and uses the added
theorem in both places; the finite theorem uses ProfiniteCoefficientInverseImage.
No definition changes, arbitrary witnesses, new axioms, or new holed statements.

The constant-model glue reuses the proved private scalar-restriction API by `import all`;
all private helpers added here are proved. The unit route is preserved: finite local systems,
induction on strata, affine shrinking, the open-closed sequence, comparison of the end
terms, extension closure, and Zariski locality. The stratified induction already works for
all schemes, so the final local step does not require an extra affine refinement.

Repair C-68837: removed the private coefficient_isIso that invoked the arbitrary-ring
comparison, bound coefficientIso, coefficient_adjunct and directImageComparison by
IsIso of the canonical map, and retained the original finite theorem via the proved
constant profinite tower specialization. The pullback-encoding node's original finite
statement, proof and proof_deps are retained; the explicit-IsIso comparison is recorded
as an added clause and declaration. The Lean attachment quotes the finite theorem
with its own explicit [Finite B] binder. The item's node now records
def-weil-pbc-proetale-operations where the arbitrary-ring comparison is used.
The obsolete Q6-proEtaleModuleRestriction_pullback.md record is withdrawn.
The statement-change metadata uses the required stage-2 schema and lists only the
published base's citer; the item's new use is recorded in its own proof dependencies.

Validation refreshed on 2026-10-19 against the current published build: all four delivery
modules compile cleanly. A separate scratch overlay uses fresh copies of the four delivery
modules and unchanged current ProEtaleConstantModuleConstructibility,
FiniteRingConstructibleSheafOrigin and ProEtaleStratifiedCounit. All seven compile cleanly;
the longest takes 7.6 seconds, including axiom probes.
The #print axioms checks for proEtaleModuleRestriction_pullback,
proEtaleModuleRestriction_pullback_of_isIso, proEtaleModuleRestriction_constructible_iff
and finiteRing_constructibleSheaf_origin report only propext, Classical.choice and
Quot.sound. Both restored/new import directions pass import_direction.py.
All delivered Lean files contain zero sorry and respect the 100-character line limit.
The pullback-encoding node's proof, proof_deps and proof_origin match the published finite
version exactly; each delivered node's proof_deps equals the union of its proof-step uses.
The two generalized support nodes' proof origins now describe only their own arguments.

Continuation validation: the resumed dry run passed at 70ff2b2f11. Its compile succeeded;
one axiom probe (ProEtaleStratifiedEssentialImage) received no answer from the busy
compile server and is marked by the delivery tool for repetition at merge. An additional
fresh seven-module consumer rerun likewise received no server answer before compiling
its first file; it returned no Lean diagnostic. The earlier successful seven-module
consumer and four-declaration axiom checks remain recorded in consumers-final.log.

Change records:
- coord/changes/Q6-proEtaleModuleRestriction_pullback_of_isIso.md
- coord/changes/Q6-exact_openClosedSequence.md
- coord/changes/Q6-comparison_essImage_of_stratification.md

## Proved and sorry left

Closed 2 of 2 original holes:
- AlgebraicGeometry.ProEtale.constructible_isClassicalModule
- AlgebraicGeometry.ProEtale.locallyConstructible_isClassicalModule

Zero sorry remains in the item; zero holes added; zero split-offs. All three support
modules remain sorry-free. This is a proof from existing declared dependencies,
including finiteLocalSystemsTwist and classicality/locality declarations whose existing
holes remain assigned to their own nodes; none is restated here.

## No longer needed

Removed imports (the two public imports were replaced by the smaller modules that
actually define the statement's constant local models and intrinsic inverse image).
The classical-sheaves module is retained as a direct proof import because the current
public import graph no longer exposes its criterion transitively:
- Sheaf.Paper.ProEtaleFixedModuleLocalConstancy
- Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
- Sheaf.CategoryTheory.SiteCoveringAxioms
- Sheaf.AlgebraicGeometry.TorsorComparisonGlue
- WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
- Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
- Sheaf.CategoryTheory.SiteModuleSheafGluing
- Sheaf.AlgebraicGeometry.ConstructiblePartitionLocalClosedStratum
- Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
- WeilConjectures.AlgebraicGeometry.EtaleConstantRingInverseImageComparison
- Sheaf.CategoryTheory.LocalizedModuleExactIndependent
- WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
- Sheaf.AlgebraicGeometry.ProEtaleSmallModelComparison
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
- Mathlib.CategoryTheory.Sites.CoverLifting
- Mathlib.AlgebraicGeometry.AffineScheme
- Mathlib.Topology.Constructible
- Mathlib.CategoryTheory.Adjunction.Mates
- Mathlib.CategoryTheory.Adjunction.Unique
- Mathlib.AlgebraicGeometry.Morphisms.Separated
- Mathlib.AlgebraicGeometry.Morphisms.Integral
- Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
- Sheaf.AlgebraicGeometry.ClassicalModuleWeakSerre
- Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
- Sheaf.AlgebraicGeometry.ProEtaleFiniteConstantHom
- Sheaf.AlgebraicGeometry.ProEtaleFiniteLocalSystemsType
- Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
- Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme
- Sheaf.CategoryTheory.LocalizedModuleExactForSystems
- Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses

Removed direct proof dependencies:
- det-pe-finite-local-systems-type
- def-weil-pbc-sites-and-cohomology
- def-weil-sheaf-of-modules-category
- det-pe-finite-local-systems-hom
- det-pe-torsor-comparison-glue
- sk-thm-pe-direct-image-comparison
- lem-weil-pbc-etale-site-localization-open
- lem-weil-proetale-weakly-etale-localization
- lem-weil-pbc-site-constant-restriction
- lem-weil-pbc-site-module-sheaf-gluing
- det-pe-classical-derived-weak-serre
- lem-sf-constructible-partition-local-closed-stratum
- lem-weil-pbc-reduced-induced-closed-subscheme
- lem-weil-pbc-affine-scheme-qcqs
- lem-weil-pbc-proetale-ringed-open-closed
- lem-weil-pbc-constant-ring-inverse-image-comparison
- lem-weil-pbc-constructible-open-restriction
- def-weil-proetale-locally-constant-sheaf
- lem-pur-site-restriction-module-adjunction-exact
- lem-weil-pbc-extension-by-zero-adjunction
- def-weil-pbc-site-comparison-morphism
- lem-weil-pbc-etale-inverse-image-restriction
- lem-weil-pbc-conjugate-iso-unit-equation
- def-weil-closed-immersion
- lem-weil-pbc-closed-immersion-integral-separated-uc
- lem-weil-pbc-affine-opens-basis

The finite-local-system torsor/type/gluing work is delegated to the existing
finiteLocalSystemsTwist statement, rather than duplicated here. The open-closed induction
and affine geometric details are reused through the already proved
comparison_essImage_of_stratification. They remain transitive dependencies where that
proof uses them; this list does not claim they are globally unreachable.
The arbitrary ringed open-closed sequence and derived intrinsic realization are not used
by this proof. The local affine-refinement step is unnecessary because the stronger proved
private stratified argument works on the originally supplied open neighborhoods.

Withdrawn obsolete top-level tool_uses approvals, keeping the finite-presentation leaf:
- lem-weil-pbc-site-module-sheaf-gluing
- lem-weil-pbc-etale-site-localization-open
- lem-sf-constructible-partition-local-closed-stratum
- lem-weil-pbc-proetale-ringed-open-closed
- lem-pur-site-restriction-module-adjunction-exact
- lem-weil-pbc-extension-by-zero-adjunction
- lem-weil-pbc-conjugate-iso-unit-equation

The pullback-encoding module retains Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
and lem-weil-pbc-profinite-coefficient-inverse-image for the finite theorem. The arbitrary
ring comparison module is imported by the item only; it is not imported by pullback encoding.
No globally unreachable modules are asserted: pruning here removes direct imports and DAG edges.

## Where the brief, the DAG or earlier work was wrong

The open-closed sequence and stratified essential-image interfaces unnecessarily
imposed finite coefficient rings; their proofs work for arbitrary commutative rings.
The returned pullback generalization accidentally made the published finite theorem
use the existing holed arbitrary-ring comparison. Repair C-68837 preserves its finite
proof and introduces a separate comparison with an explicit IsIso assumption.
The item alone uses the arbitrary-ring instance, with its dependency recorded in the DAG.
The two other node statements and Lean attachments remain generalized with their
statement_change records; their finite specializations remain valid. No target or
assigned statement changes.

The prior DAG expansion duplicated already available finite-local-system descent and
stratified induction. Reusing these declarations is shorter and retains the blueprint
unit's argument. Empty schemes, empty/zero strata, the zero ring, nonreduced ambient
schemes, and infinite Noetherian rings are included: no stratum is identified with its
reduced image, and the support induction treats full-image strata by closed immersion.

## Second reading by Q6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
