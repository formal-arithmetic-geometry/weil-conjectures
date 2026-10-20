## What changed

Repair of the return at head `545ebfab82`: the change record now explicitly
lists `Sheaf.Paper.OpenRestrictionScalarExchange` in `## Users`, including its
references to `CategoryTheory.RingedDerivedComparisons.Site.D` and
`CategoryTheory.RingedDerivedComparisons.Lift.unit`. Both are relocated
unchanged and publicly re-exported. No consumer adaptation is necessary.
The consumer is absent from this local source/claim snapshot; its references
are recorded from the landing return. A fresh scan of the current local
sources with the packet overlaid finds 48 transitive importers, all already
covered by the retained conservative table. This retry changes documentation
only and retains the assembly proof and its four separately stated holes.

The public statement `CategoryTheory.RingedDerivedComparisons.ringedDerivedMonoidalComparisons`
is unchanged. Its Lean proof constructs geometric composite/identity witnesses,
constructs normalized ordinary and derived adjoint lifts, restricts the existing
site tensor models, assembles tensor-normalized lifts, and applies the separate
composition, identity and specified geometric 2-isomorphism results.

Right derived comparisons are the actual adjunction mates. A proved mate-unit
calculation gives all three Hom-bijection equations. Evaluating the composition
Hom equation on the counit and using the triangle identity proves the full
four-factor composite counit equation.

New proved modules:

- `ResolvingDerivedAdjunction`: a resolving-class/K-injective construction of a
  derived adjunction, including its Hom formula on every chain map. The proof
  transfers the left universal property across the homotopy quotient and uses
  absoluteness and K-injective derivability, rather than redoing fraction calculus.
- `SuppliedTensorAdjunctionNormalization`: constructs the ordinary module
  adjunction for the supplied direct image and proves its underlying-sheaf
  scalar-insertion formula. It transports the explicit tensor-extension adjunction
  along the specified pullback object equalities.
- `RingedDerivedTensorLift`: constructs the normalized unit and the monoidal
  structure from explicit localized coherence equations; both naturality equations
  are proved from the canonical tensor comparison.
- `RingedDerivedAdjointLift`: constructs the geometric algebraic inverse image,
  scalar pullback and both universal derived functors, and applies the preceding
  normalized adjunction results. Its epsilon comparison is invertible on flat-term
  K-flat complexes, and eta on K-injectives.

The existing records are moved unchanged to
`RingedDerivedComparisonData`, publicly re-exported by the item, to let the new
normalization modules use them without an import cycle. No source-library module,
target, record field, universe, or definition body is changed. See
`coord/changes/k4-ringed-derived-comparison-data.md` for the conservative consumer check (1,086 current-source downstream modules).

The remaining four source results are stated separately with full representative
normalization. These are strictly separate portions of the source argument: one
edge's monoidal coherence, composition, the identity case, and a specified
ring-compatible geometric 2-isomorphism. None restates existence of System or
existence of normalized adjoint lifts. Their right comparisons are explicitly
mates; the formal Hom and counit consequences are proved in the item.

## Proved and sorry left

The original hole in `CategoryTheory.RingedDerivedComparisons.ringedDerivedMonoidalComparisons`
has a complete assembly proof from the following intermediate statements. This is
a decomposition, not a sorry-free proof of the original assertion: 1 original hole
closed and 4 new holes added, for net -3 holes before considering import closure.

Proved new public theorems:

- `CategoryTheory.derivedAdjunctionOfResolvingClass`.
- `suppliedTensorAdjunction_normalized`.
- `CategoryTheory.RingedDerivedComparisons.adjointLift_exists`.
- `CategoryTheory.RingedDerivedComparisons.tensorLift_exists`, reduced to explicit
  diagram equations: the ordinary unit witness, derived unit map, both tensorator
  naturality equations and CoreMonoidal construction are now written in Lean.

Every remaining hole, exactly one in each named new module:

- `CategoryTheory.RingedDerivedComparisons.canonicalTensorDiagrams`
  (`lem-sfb-ringed-derived-tensor-diagrams`).
- `CategoryTheory.RingedDerivedComparisons.compositionCore_exists`
  (`lem-sfb-ringed-derived-composition-comparison`).
- `CategoryTheory.RingedDerivedComparisons.identityComparison_exists`
  (`lem-sfb-ringed-derived-identity-comparison`).
- `CategoryTheory.RingedDerivedComparisons.twoIsoComparison_exists`
  (`lem-sfb-ringed-derived-two-iso-comparison`).

The tensor hole is now only invertibility and coherence equations for explicitly
constructed maps; it does not choose a monoidal structure or a unit witness.
`RingedDerivedTensorLift` proves the structure assembly and naturality from them.

Each hole is a public theorem whose body is exactly `by sorry`, with its source,
complete proof in words, and matching new node. No definition contains a hole.
All choices of witnesses in the assembly are within the existential theorem proof;
no public definition chooses arbitrary data from a holed existence statement.

## No longer needed

The original proof-only imports of
`Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`,
`Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`, and
`Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` are unnecessary for
this route. The resolving-class/K-injective Kan-extension construction proves the
normalized derived adjunction directly. The corresponding original DAG proof
dependencies `lem-pc-pre-derived-adjoint-functors-general`,
`lem-pc-derived-adjoint-functors`, and `def-sfb-right-derived-functor` are no longer
used by this proof. The first two obsolete top-level tool approvals are removed;
remaining approvals keep their original order.

Every other removed direct proof import is accounted for as follows:
`SiteDerivedTensorDescentIndependentCoefficients`, `KFlatTotalTensorModel`,
`CochainPullbackTensorCoherence`, `RingedTopoiDerivedPullback`,
`RingedTopoiTensorSections`, `ModulePullbackPushforwardAdjunction`,
`GeometricModuleTransport`, and `DerivedCategory.Fractions` are used in the new
specific normalization modules or their proved adjunction helpers.
`RingedSiteKInjectiveResolutionsOfUniverses` and
`KFlatResolutionIndependentCoefficients` are replaced in the adjoint construction
by their site-in-the-coefficient-universe APIs `RingedSiteKInjectiveResolutions`
and `KFlatResolution`; localization universe w remains independent.
`Mathlib.CategoryTheory.Localization.CalculusOfFractions` needs no direct import:
the fraction API is imported by the comparison modules. These are removals from
the item's direct import list, not claims that these modules disappear from the
entire targets' import closure.

Original proof imports for cochain coherence, total tensor models, tensor descent,
K-flat resolutions and fractions now belong to the specific normalization modules
whose written proofs use them. The geometric transport, ordinary tensor adjunction
and termwise adjunction are used by the proved normalization helpers. The
pushforward-composition module supplies K-injective derivability and right-derived
existence, and remains needed. The unchanged original public imports are all
re-exported by ComparisonData. No upstream declaration or module is withdrawn.
No unit statement or realized unit step is bypassed. No whole module is claimed
pruned merely because its direct import moved into a helper.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. The DAG's fraction proof is a valid plan, but a shorter
formal route to the normalized adjoint lift is available through absolute Kan
extensions and K-injective derivability. The composite, identity and 2-isomorphism
right comparisons can be chosen as mates; their Hom and counit equations then
follow formally. Their geometric representative normalization remains substantive
and is retained in the separate results, rather than inferred from bare adjoint
uniqueness.

The complex pullback comparison includes the homotopy-quotient and localization
factor isomorphisms. It is not syntactically epsilon's component; the proved lift
explicitly simplifies their identity components. Ordinary direct image is never
assumed to preserve K-injectives or ordinary pullback to be exact.

Edge cases checked at statement level: the zero ring and zero complex; identity
geometric maps; theta equal to identity; odd/odd Koszul signs and characteristic
two; and extension of scalars from integers to integers modulo two. The last case
requires K-flat representatives and rules out an exact-pullback shortcut. Arbitrary
supplied derived functors and tensor structures remain pinned by all their original
representative formulas. The independent coefficient/localization universe is kept.

## New nodes

`def-sfb-ringed-derived-comparison-data` owns the unchanged witness records in the
public data module. This breaks the proof-module import cycle without changing the
meaning of any consumer.

`lem-sfb-resolving-derived-adjunction-normalization` is the proved general
resolving-class derived adjunction with normalized Hom formula.

`lem-sfb-supplied-tensor-adjunction-normalization` is the proved ordinary
scalar-extension Hom normalization for a supplied module direct image.

`lem-sfb-ringed-derived-adjoint-lift` is the proved construction of the adjunction
portion of a normalized lift, without any monoidal comparison assertion.

`lem-sfb-ringed-derived-tensor-lift` now proves the single-edge monoidal structure
from explicit maps and their diagrams. It constructs the ordinary unit witness
and the derived unit map, proves the two naturality axioms from the canonical
natural transformation, and applies CoreMonoidal.mk'.

`lem-sfb-ringed-derived-tensor-diagrams` isolates invertibility of the explicit
derived unit and the three localized monoidal diagrams and signed symmetry.
It retains the specified tensor comparison and the actual unit map; there is no
unconstrained existential monoidal witness in its statement.

`lem-sfb-ringed-derived-composition-comparison` isolates the ordinary scalar
association, derived pullback and right-mate representative formulas, and tensor/unit
composition diagrams. The item itself proves the Hom and counit consequences.

`lem-sfb-ringed-derived-identity-comparison` isolates the identity representative,
tensor and unit normalization; its right comparison is a fixed mate.

`lem-sfb-ringed-derived-two-iso-comparison` isolates transport by the specified
ring-compatible geometric theta, including its representative and tensor/unit
normalization; its right comparison is a fixed mate.

The original route and all new Lean attachments are recorded in the node files.
New-node searches include actual LeanSearch queries for all nine new nodes, plus
the logged LeanFinder, Loogle and Mathlib grep searches. Whole-blueprint
searches for monoidal structures, derived adjunctions and scalar extension found
related condensed-coefficient/specialized results, but no duplicate of these
ordinary arbitrary-ringed-site normalization results. Their blueprint ancestor is
`det-prop-p1-adjunction-rational-triangle`, First and Second identity paragraphs.
Compilation: all ten packet modules compile through lcompile.py in import order.
The unchanged direct consumer `Sheaf.CategoryTheory.DerivedBaseChangeMap`
compiles against the packet in 9.7 seconds; its temporary verification copy was
removed and is not delivered. The complete main assembly compiles in 34.7 seconds; the tensor structure assembly
compiles in 40.1 seconds and the normalized adjoint lift in 33.0 seconds. The original six record declarations were also checked
verbatim against the repository source, and the updated dependency graph is acyclic.

The first server preflight found the initial cached 47-consumer list incomplete;
a fresh source scan found 1,086 downstream modules. The change record now lists
all of them with holders and effects. That preflight also noted axiom-probe
timeouts for ComparisonData, AdjointLift and SuppliedTensorAdjunctionNormalization;
it explicitly leaves those probes for the merge to retry. Ordinary file compilation
passed for all ten modules.

The next preflight passed the consumer check and identified two metadata errors:
LeanFinder and Loogle are one search kind, and a structure attachment records its
header rather than its fields. All nine nodes now include their own successful
LeanSearch query; the data attachment now records `structure System`. Every new
Lean attachment was checked with the signature parser against its actual source.

The interface-location change record is
`coord/changes/k4-ringed-derived-comparison-data.md`.

Repair verification: `lcompile.py --all` compiled all ten retained packet modules
successfully on the project server. The main assembly compiled in 9.0 seconds.
The packet still has exactly four named theorem holes, as listed above; the
consumer-record repair adds or closes no further holes.

The repair preflight accepted the originally returned consumer but found six
additional server consumers missing from the retained table:
- `Sheaf.Paper.RingedCoefficientAssociatorShifts` (Site.D).
- `Sheaf.Paper.RingedCoefficientProjectionData` (Site.modules, Site.D, Lift.insertion).
- `Sheaf.Paper.RingedCoefficientPullbackCoherence` (Site.D, Lift.unit).
- `Sheaf.Paper.RingedCoefficientPullbackComparison` (Site.D).
- `Sheaf.Paper.RingedCoefficientPullbackShifts` (Site.modules, Site.D).
- `Sheaf.Paper.RingedCoefficientScalarUnits` (Site.D, Lift.unit).

All six are now listed in the change record with the exact references above
and their unchanged public re-export checked. This is an extension of the
consumer-record repair; it makes no further Lean changes. The axiom probe for
`RingedDerivedAdjointLift` timed out, and the wrapper explicitly defers that
probe to the merge. Ordinary compilation of the packet passed.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
