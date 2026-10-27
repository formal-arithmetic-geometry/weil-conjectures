## What changed

Proved AlgebraicGeometry.ProEtale.isTriangulated_boundedConstructible in the assigned source
module, with its original signature, coefficient class, universes, attributes, public imports,
and all original definition bodies unchanged. The proof packages constructible heart closure
as the existing derived homology-property criterion and intersects with boundedness.

The continuous field case uses the existing local-freeness/Serre proof, with coefficient-universe
transport; the algebraic-closure case uses its existing Serre theorem. Both integral constructors
use integralConstructible_serre, after identifying their normed coefficient rings. The finite
discrete case uses the new, fully proved finiteDiscrete_constructible_kernel and existing generic
cokernel/extension closure. The kernel proof transports to module-valued pro-etale sheaves,
descends to etale sheaves, lifts the morphism by full faithfulness, applies etale kernel closure,
and transports finite presentations back to the internal coefficient encoding.

To make those existing proofs importable before the instance, factored ordinary coefficient
data from bounded-derived wrappers, retaining all existing names, bodies and public reexports.
Extracted the already proved inverse-image/scalar-extension comparison and local finite
presentation result into two lower modules. The complete adaptation and consumer audit are in
coord/changes/bounded-constructible-heart-imports.md. This dependency refactor is required to
remove import cycles; it does not split any proof because of compile time.

The original instance compiled in 7.6 seconds after the zero-object scope fix, and the
finite-discrete kernel proof compiled in 9.5 seconds. The complete integral-kernel proof now
compiles in 33.7 seconds. Its repeated unfolding of the point inverse-image definitions is
prevented by local irreducibility attributes. The realization module uses the same local
point-inverse-image transparency settings and was recompiled successfully.
Private semireducible caches reuse the coefficient and pullback monoid structures;
the complete kernel module compiled in 42.1 seconds with these caches.
Proved generic private equations handle the
mapped pullback section, conjugated matrices and composed coefficient squares, and local
presentation isomorphisms are abstracted with their equations. No profiling option or
diagnostic exit remains. The full packet is recompiled before delivery; the delivery tool
then performs its independent compilation and preflight.

The returned d2a1eae1fba packet omitted six consumers from the change record's Users table.
All six are explicitly recorded with their effects. The resumed audit uses the delivery
checker's interface comparison and downstream matcher against current shared sources,
including conservative textual matches for anonymous and local instances. Newly introduced
consumers and their current claim holders are recorded as well. Existing coefficient data
retains identical names, signatures and bodies through public reexports; local encoding
instances stay local. No additional consumer code adaptation is needed. The repair preserves
the complete proof packet and refreshes its consumer records. The final server preflight
identified five further source-library users of the EssentiallySmall Profinite instance;
all five are now included in the same Users table. The packet passed compilation.

The 2026-10-23 return at 02fb5a587 identified six more consumers of the anonymous
EssentiallySmall Profinite instance. All six now have individual Users rows, including their
current holders and the fact that the unchanged local instance causes no API change.
A fresh downstream audit against current shared sources adds every further match. The packet
uses the current canonical finiteness-triangulatedness node instead of adding a duplicate.
The upstream instance docstring is restored verbatim; its proof-only Sheaf imports must be
registered by the maintainer to survive future upstream synchronization.

Repair of the c51089c9b return: the lower scalar-extension module no longer duplicates
fp_iff_of_iso, fp_map, fp_extend or lfp_extend. These existing declarations are moved out of
BoundedConstructibleExtendScalars, which publicly imports their lower defining module.
The three originally public theorems retain their exact names, signatures and proof bodies.
The existing lfp_extend is made public at the lower layer and used directly by both consumers;
there is no renamed locallyFinitelyPresented_extendScalars theorem or duplicate wrapper.
This repairs the reported duplication while preserving the acyclic heart-level imports.

A full duplicate-statement scan found five more copied private lemmas before delivery.
FiniteDiscreteConstructibleModel now imports the single lower definitions of encodedConstantFP,
internalLisseFP and internalComparisonConstructible, together with their construction helpers;
its public theorem and proof are unchanged. EllAdicBoundedTriangulated now specializes the
proved source instance and drops its duplicate continuous_lf and triangulated_of_serre helpers.
Both added adaptations are unclaimed and recorded in the change record and node copies.

The repaired packet has 22 Lean modules. The combined current-library-plus-packet
statement/name scan reports zero duplicate findings. The consumer audit was refreshed
against the current shared sources and its newly matched users added to the change record.

## Proved and sorry left

Closed 1 of 1 original holes:
AlgebraicGeometry.ProEtale.isTriangulated_boundedConstructible.

Added 0 holes; split off 0 unfinished statements. Every delivered module has zero actual sorry
bodies. The public pullbackExtendScalarsComparison, relocated
lfp_extend and new finiteDiscrete_constructible_kernel are all completely
proved. Previously proved scalar-extension, coefficient encoding and integral closure results
remain completely proved. This is a proof, not a decomposition into new admitted results.

## No longer needed

No modules or public declarations are withdrawn and no blueprint unit is bypassed. No source public
import is removed. The original instance does not require the conditional derived wrapper or
the ell-adic-only triangulated wrapper as proof imports: their existing generic/heart arguments
are used at their lower layer, while those wrappers and their public declarations remain intact.

IntegralConstructibleKernels no longer imports
Sheaf.AlgebraicGeometry.BoundedConstructibleExtendScalars. Its former proof dependency
lem-weil-pbc-bounded-constructible-exact-scalar-extension is replaced by the two proved heart-level
scalar-extension nodes; the bounded scalar-extension theorem remains and still uses them.

IntegralScalarContractive, ContinuousCoefficientRealizations, IntegralMatrixPivotCover,
IntegralConstructibleKernels and IntegralConstructibleSerre no longer import the high
ContinuousIntegralCoefficients wrapper; they import ContinuousIntegralCoefficientData.
FiniteDiscreteRestrictionEncoding, FiniteDiscreteEncodedPresentation,
FiniteDiscreteConstructibleLocalPiece and FiniteDiscreteConstructibleEncoding similarly replace
FiniteDiscreteCoefficientEncoding with FiniteDiscreteCoefficientEncodingData. These import edges
are removed to eliminate cycles; the old public wrapper modules are still needed elsewhere and
are not claimed as pruned. No mathematical dependency is discarded without its complete proof.

The canonical instance node now cites the proved field local-triviality theorem directly.
Its former embedding route through
lem-weil-pbc-algebraic-extension-embeds-algebraically-closed and
lem-weil-l-adic-extension-absolute-value is unnecessary; continuous_lf transports only
across the universe-lift coefficient isomorphism. No declaration is withdrawn.

For finite coefficients the new kernel theorem packages
lem-weil-pbc-finite-discrete-condensed-ring-constant,
lem-weil-pbc-internal-module-ab-equivalence,
def-weil-pbc-common-finite-discrete-encoding,
lem-weil-pbc-finite-discrete-constructible-encoding,
lem-weil-pbc-finite-discrete-restriction-encoding and
lem-weil-pbc-finite-type-constant-exact. These remain needed below that theorem and are
only removed from the instance's direct proof dependencies. The alternative route through
lem-weil-pbc-proetale-constant-module-encoding,
lem-weil-pbc-proetale-constant-module-constructibility and
lem-weil-proetale-constructible-exact-closure is not used: the kernel argument uses the
existing etale constructible-kernel theorem and exact comparison instead.

lem-sbc-cohomology-in-weak-serre-subcategory is replaced by the already implemented
prop-constructible-derived-subcategory criterion. The original definition/setup nodes
def-sfb-bounded-constructible-complexes, def-sfb-constructible-module,
def-weil-pbc-proetale-site, sk-def-sfb-pulled-back-coefficients,
sk-def-sfb-change-of-scalars, lem-sfb-modobj-abelian and
lem-weil-pbc-sheaf-tensor-closed are supplied by the existing public imports and the
coefficient-transport API, rather than separate proof steps. They remain available and
are not claimed as globally pruned modules.

FiniteDiscreteConstructibleModel no longer imports FiniteDiscreteEncodedPresentation directly;
it uses the relocated private helpers from FiniteDiscreteConstructibleKernels.
EllAdicBoundedTriangulated no longer imports ProEtaleModuleConstructiblePullback,
CondensedConstructibleSerre or IntegralConstructibleSerre privately. It applies the full
finiteness-coefficient instance, so its duplicate private continuous_lf and
triangulated_of_serre proofs are unnecessary. Its old direct proof dependencies are now
supplied by lem-sfb-bounded-constructible-triangulated-finiteness. No public theorem is removed.

## Where the brief, the DAG or earlier work was wrong

Upstream synchronization retention: the source proof needs the private proof imports
Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback,
Sheaf.AlgebraicGeometry.CondensedConstructibleSerre (import all),
Sheaf.Paper.IntegralConstructibleSerre, Sheaf.Paper.ConstructibleCokernelsExtensions and
Sheaf.Paper.FiniteDiscreteConstructibleKernels, plus the proved private helpers
constructible_zero, continuous_lf and triangulated_of_serre. The maintainer must record
this proof in coord/upstream-statement-exceptions.tsv so the next sync preserves it.
The worker has not edited that maintainer-owned table.

The current source statement is correct for IsFinitenessCoefficient. The historical generic
ring-object version is false, as the source already explains; this proof does not restore it.
The current canonical node lem-sfb-bounded-constructible-triangulated-finiteness now
records the restricted coefficient instance; its proof and dependencies are updated to the
complete retained argument, preserving its statement and all maintainer-owned fields. The conditional generic triangulatedness nodes retain their
current statements and attachments; no condition is dropped.

Earlier heart-level proofs had imported bounded-derived wrappers only for coefficient data or
private scalar-extension helpers. Reusing them for the source instance exposed import cycles.
The factorization preserves their mathematics and repairs that dependency arrangement. No
definition is chosen from an admitted existence result. The finite-discrete theorem includes
arbitrary schemes, the zero ring and zero modules; finite-ring noetherianity, not scheme
noetherianity, supplies its etale kernel closure. The main instance retains scheme noetherianity
for its continuous and integral cases. Rank-zero presentations cover the zero-object case.

## New nodes

def-sfb-finite-discrete-module-categories records the unchanged category abbreviations and
additive instance relocated from the realization module to their own lower module.

lem-sfb-finite-discrete-internal-constructible-kernels records the new proved heart-level kernel
closure; the forward encoding and etale constructible-origin declarations are existing inputs.
Its reverse finite-presentation argument is proved in the new module, rather than importing a
bounded-derived comparison theorem.

lem-sfb-pullback-extend-scalars-comparison records the constructive uniqueness-of-left-adjoints
comparison, extracted unchanged in substance from the existing scalar-extension proof.

lem-sfb-locally-finitely-presented-extend-scalars records the existing lfp_extend and its finite-presentation
helpers at their lower defining module, using that comparison. Both scalar helpers have zero holes.

Existing continuous coefficient and finite encoding node attachments are updated to their new
defining modules, with the retained integralConstructible alias attached to the old wrapper.
Existing integral kernel and bounded scalar-extension node proofs name the lower results.
Change record: coord/changes/bounded-constructible-heart-imports.md.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
