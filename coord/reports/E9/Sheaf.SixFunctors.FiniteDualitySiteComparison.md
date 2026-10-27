## What changed

Repaired the landing return C-eb288 (head `eb28853ecb8`), whose mathematical
proof was passed by the independent reviewer. The change record now explicitly gives
its delivery path and the required reviewer-fix filename
`E9-finite-duality-compatibility-sharing.change.md`. The failed landing supplied the
ordinary `.md` basename to `--apply-fixes`; the landing tool accepts `.change.md`
for change-record overrides. Both Old and New code blocks were checked verbatim
against current main and this packet, respectively. The approved Lean proof and
consumer adaptation are retained; the delivery tool rebuilds the packet on current
`sheaf-dag`.

Repaired returned delivery C-58656 (head `586566424f1`). The canonical Hom comparison
now follows thick generation from lisse flat stratum generators. A lisse flat sheaf
has a proved derived exact pairing, so its comparison is invertible for every target.
The proved closed-support comparison, exact open restriction comparison, the two
projection-adjunction Hom isomorphisms, and the bounded-below direct-image comparison
assemble a Hom-object isomorphism on each stratum generator. The retained
`CategoryTheory.isIso_comparisonHom` proves invertibility of the canonical evaluation
arrow there. `etaleThickGeneration` and `siteHomComparison_exact_thick` extend this to
all constructible finite-Tor sources.

The proof uses generic finite-ring helpers from the planned modules. This handles the
actual lifted coefficient ring without changing any dependency signature. It also
avoids requiring bounded constructibility of the stratum exceptional value: boundedness
below is enough for ordinary direct-image comparison, and lisse dualizability handles
an arbitrary second Hom input.

The prescribed dualizing-arrow construction, evaluation and biduality equations, and
transport assembly are retained. The public compatibility predicates retain the
previous packet's shared canonical formulas and Prop structure; pairing normalization
identifies them with the recorded maps. The retained proof adaptation in
`Sheaf.Paper.FiniteStageVerdierBiduality` reads the transport field and rewrites native
biduality to the recorded pairing map. Public theorem signatures are unchanged.
Removed redundant concrete braided-functor instances from the private transport
application. The generic transport constructor uses the existing monoidal structure
and the proved braiding equation directly. The transport assembly is retained.
The definition change record remains
`coord/changes/E9-finite-duality-compatibility-sharing.md`.

Removed the inaccurate, unlanded node `lem-sf-adopted-separated-hom-existence` from the
packet. The item no longer imports the adopted Hom-comparison module directly or
applies either adopted Hom-existence theorem. No adopted source declaration was
changed. The item DAG now records the generator argument and the retained transport
assembly, with the exact dependencies used.

## Proved and sorry left

Closed the one original hole, `WeilConjectures.finite_duality_site_comparison`.
The item has zero `sorry`; the retained consumer has zero `sorry`; the packet adds
zero holes and zero new modules. All private helpers, including the new closed/open
comparison and thick-generation helpers, have complete proofs. No statement is split
off. In particular, the adopted
`AlgebraicGeometry.ProEtale.DerivedCategory.nonempty_iso_mapDerivedCategory_derivedHom_of_isSeparated`
is no longer an input to this item's proof.

For this landing repair, `lcompile.py --all` returned accepted server result
`6ecc5de6d4ef198bd1644278` for both packet modules without errors or warnings.
The launcher reused the result for the identical Lean sources and dependency state.
No development profiler options remain. The delivery command runs the compile,
consumer, definition-change, node and independent-review gates.

## No longer needed

The Hom proof does not use `lem-weil-finite-duality-locally-closed-comparison` or
`thm-sf-preservation-class`: the generic closed-support argument already gives the
needed bounded-below exceptional comparison. Its lisse-flat step works with an
arbitrary target, so there is no need to descend a bounded constructible stratum
exceptional value using `lem-sf-proetale-constructible-origin`. The finite-ring origin
and intrinsic Tor comparison are still used for the final full-subcategory equivalence.
The separate stratum pairing-identity theorem
`lem-sf-stratum-hom-pairing-identity` is also not used: the proved stratum Hom-isomorphism
helpers and the retained categorical canonicality criterion suffice.

Removed the unused private assembly variants `EvaluationDualityData_of` and
`comparisonData_pairings`; the retained assembly uses `comparisonData_allPairings`.

Removed direct imports relative to current main (some remain available transitively):

- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.KInjectiveHomComplex`
- `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`
- `Sheaf.AlgebraicGeometry.ComparisonDirectImage`
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`
- `Sheaf.AlgebraicGeometry.EtaleOriginAdjointClass`
- `Sheaf.AlgebraicGeometry.FiniteDualityLocallyClosedComparison`
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`
- `Sheaf.AlgebraicGeometry.ProEtaleStalkConservative`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`
- `Sheaf.CategoryTheory.DerivedCategory.BoundedFiniteTorPerfect`
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.Paper.ComparisonTorAmplitude`
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`
- `Sheaf.Paper.FiniteFreeHomComparison`
- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.Paper.ProEtaleLisseOrigin`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.SfHomTriangulated`
- `Sheaf.Paper.SfPreservationClass`
- `Sheaf.Paper.StratumAmbientHom`
- `Sheaf.Paper.WeilVerdierPreservationStrata`
- `Sheaf.SixFunctors.EtaleLocallyClosedExtensionComparison`
- `WeilConjectures.Algebra.Homology.HomComplex`
- `WeilConjectures.Algebra.Homology.HomTensorTotal`
- `WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized`
- `WeilConjectures.SixFunctors.Finite.Exact`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy`

Removed from the old item proof-dependency list:

- `lem-sf-comparison-pullback-exact`
- `lem-sf-proetale-constructible-origin`
- `lem-sf-ringed-derived-closed-symmetric-monoidal`
- `lem-sfb-exact-tensor-functor-derived-braiding`
- `lem-sfb-exact-tensor-functor-derived-normalization`
- `lem-weil-finite-duality-locally-closed-comparison`
- `lem-weil-pbc-closed-immersion-finite`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lem-weil-pbc-ringed-topoi-module-pullback-tensor`
- `lem-weil-verdier-preservation-strata`
- `thm-sf-preservation-class`

The native categorical tensor, braiding and pairing proofs replace the old specialized
normalization/preservation dependencies where listed above. No existing library module
or declaration is withdrawn. The rejected unlanded adopted-existence node is dropped,
and no replacement node is added.

## Where the brief, the DAG or earlier work was wrong

The returned packet applied a pre-existing adopted theorem which restated the Hom
claim and both duality conclusions with a `sorry`. Giving that declaration a new DAG
attachment did not reduce the argument; its recorded Lean statement also failed to
match the node's clause-1-only mathematical statement. This repair removes both that
proof dependency and the inaccurate attachment.

The planned public geometric lemmas use an unlifted coefficient quotient in a larger
universe, whereas the item uses a lifted quotient. Their proved coefficient-independent
helpers apply directly. Lisse dualizability also removes the planned constructibility
preservation-and-origin detour for the second Hom argument. The unit's realized route
is retained; only the argument below this item is shortened.

The C-eb288 return was a reviewer-fix filename error rather than a mathematical
rejection. The required override suffix is documented in the change record so that
any further reviewer corrections use the landing tool's accepted filename.

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
