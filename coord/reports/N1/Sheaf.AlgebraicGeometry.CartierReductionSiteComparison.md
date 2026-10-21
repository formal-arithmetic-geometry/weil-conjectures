## What changed

Repair of the return on head 2f8caf3265: the supported scalar-unit change record now
starts its Status with open. Rebased on the current ExactDegreeZero interface: retain
OrdinarySupportedKummerScalar verbatim and use the proved scalarUniversal_derivedUnit API in the two new
proof consumers. Its existing DAG node is also retained. The delivery tool assembles
the repaired packet on the current sheaf-dag base.

Completed the three original proofs: the relative pole boundary, the two normalized reductions,
and the full comparison theorem. The pole proof uses a free torsor extension and the integral
open-closed sections sequence. The reduction proof uses scalar-unit Ext bijections. The comparison
proof uses exact Ext naturality, normalized Kummer scalar units and the existing simultaneous Cartier
family, retaining the blueprint unit route.

Added fully proved categorical and sheaf lemmas for these arguments. No new theorem has a hole.
The original module publicly re-exports CartierReductionData, which holds its constructions and
existence proofs. This breaks the real import cycle through SupportedCartierBoundaryExistence and
allows reuse of the existing ordinary supported Kummer coefficient theorem. The boundary helper's
statement is unchanged; its proof imports the foundation and unfolds the new equivalent aliases.
OrdinarySupportedCartierKummer itself is unchanged and is not delivered.

The new categorical lemmas name the unbounded scalar-unit predicate abstractly. The
current ordinary supported-scalar interface is preserved, with the proved scalarUniversal_derivedUnit API
used in the two new proof consumers. The Cartier scalar/boundary aliases are definitionally
equivalent. The foundation change record gives the old/new bodies, consumer lists and
reopened definition reviews. No WeilConjectures source file or target declaration changes.

Original delivery validation: all proof components and the assembled comparison theorem compiled through lcompile;
the assembled theorem took 38.2 seconds. The unchanged OrdinarySupportedCartierKummer source
compiled against the adapted boundary helper (53.4 seconds), and the unchanged
SupportedKummerScalarSource compiled against the named scalar-unit predicate (14.0 seconds).
The combined DAG audit finds no newly introduced dependency cycle. All 33 delivered modules compiled across the packet and affected-file checks; after the explicit
comparison-isomorphism proof import was added, the affected batch passed without warnings.
The final main-module transparency check passed in 53.8 seconds. Three further examples applied the
proved declarations to the verbatim original written theorem signatures, with the original implicit
universe notation, and compiled in 6.6 seconds; all three propositions are definitionally unchanged. The delivery dry run passed: commit 62fa2e3e988 compiled, passed its axiom probes and stage-3
preflight, and was classified CODEX for independent review.

Repair validation: the general-site scalar API compiled in 3.0 seconds, the etale Kummer
helper in 47.2 seconds, and the supported integral helper in 10.9 seconds, without warnings.
The other 29 proof components also compiled without warnings. The assembled theorem
compiled without warnings in 58.8 seconds against the current published library.
Profiling showed that additional local derived-category instance witnesses slowed kernel
checking in the assembled proof; they were removed there. All 33 delivered modules have
zero holes and satisfy the 100-column Lean source limit. Diagnostic files are omitted.
The full packet rebuild then exposed a timeout in pro_integral_derived_unit. Restoring
default transparency and removing its redundant reflexive-isomorphism transport reduced
its isolated compile time to 42.3 seconds; no statement or definition changed. The final
combined compile against the rebuilt dependencies passed without warnings: the integral
helper took 38.2 seconds and the main theorem 57.2 seconds. All other 31 modules passed
the full packet rebuild before that proof-only repair.

## Proved and sorry left

Closed 3 of the original 3 holes:

- AlgebraicGeometry.Etale.cartierPoleBoundary_existsUnique.
- AlgebraicGeometry.ProEtale.cartierReduction_existsUnique.
- AlgebraicGeometry.ProEtale.cartier_reduction_site_comparison.

Holes added: 0. Sorries left in the delivered Lean files: none. Split off with sorry: none.
All new subsidiary statements are proved in this session. These proofs use existing project
statements, including the torsor-extension short-exactness, divisible-extension identifications,
supported coefficient unit and Cartier-family results; their pre-existing holes remain separate
items. Closing the three local holes is not a claim that this entire dependency closure is axiom-free.

## No longer needed

The earlier proposed adaptation of OrdinarySupportedKummerScalar and its DAG-node copy
are omitted on rebase. The current M9 definition, node and consumers are preserved;
these are not globally pruned modules. The new proof consumers use an API lemma instead.

The pro integral unit proof also no longer applies the private scalar_unit_iso lemma:
composite coefficient forgetting is definitionally direct forgetting. The module holding
the composition lemma remains needed.

No library module is withdrawn and no upstream declaration is removed. The old public imports remain
exported through the foundation. The boundary helper removes its proof import of the full comparison
module and imports the foundation instead. Trial imports and all scratch/probe modules are omitted. The foundation drops the unused
DerivedScalarExtUnitZero proof import; the comparison theorem imports that lemma where it is used.

The following old direct proof-plan dependencies are replaced by the named proved helper arguments;
some remain statement dependencies or are still used transitively by other imported project results,
so they are not claimed as globally pruned modules:

- lemma-weil-pbc-finite-stalk-formula
- lem-weil-pbc-constant-sheaf-geometric-stalk
- prop-weil-pbc-geometric-stalks-exact
- lemma-weil-pbc-geometric-stalk-conservative
- lem-amb-kummer-any-base
- def-weil-pbc-proetale-site
- def-pur-roots-of-unity-sheaf
- def-weil-abstract-derived-category
- lem-weil-pbc-complex-ses-triangle
- lem-sfb-divisible-extension-derived-reduction
- lem-pur-derived-change-of-rings
- lem-weil-pbc-ringed-topoi-derived-tensor-pullback
- lem-asd-finite-etale-twist-line
- lem-kun-kflat-criteria
- def-pc-divisor-line-bundle
- lem-sc-line-bundle-torsor
- lem-sc-torsor-h1

The following obsolete direct tool_uses entries are removed without adding or reordering approvals:

- lemma-weil-pbc-finite-stalk-formula
- lem-weil-pbc-constant-sheaf-geometric-stalk
- lemma-weil-pbc-geometric-stalk-conservative
- lemma-weil-pbc-finite-direct-image-exact
- prop-pur-kinjective-resolutions-exist
- lem-weil-proetale-module-direct-image-left-exact
- lem-amb-kummer-any-base
- lem-cbc-comparison-pullback-sections
- lem-asd-etale-finite-twist-pullback
- lem-sfb-divisible-extension-derived-reduction
- lem-pur-derived-change-of-rings
- lem-weil-pbc-ringed-topoi-derived-tensor-pullback
- lem-asd-finite-etale-twist-line
- lem-kun-kflat-criteria
- lem-sc-line-bundle-torsor
- lem-sc-torsor-h1

## Where the brief, the DAG or earlier work was wrong

The return identified an invalid change-record status; it now starts with open. The newer
main branch also introduced scalarUniversal, so the earlier raw-predicate replacement would
have overwritten that interface. It is omitted. ScalarUniversalDerivedUnit supplies a proved
general-site normalization API instead. Local references to the existing proved sheafification
and Grothendieck-abelian instance witnesses keep the chosen derived models compact. No
compile-time or heartbeat limit is raised, and no existing definition is changed for this rebase.

The relative pole extension can be obtained directly from its torsor and prescribed complementary
frame. Constructing a separate sheaf of meromorphic units is unnecessary for the published Ext-class
specification. The source scalar-unit bijection already gives existence and uniqueness of each
reduction; Kummer target universality is needed for the full theorem, not for that existence step.

The existing ordinary supported Kummer theorem could not initially be imported: its boundary helper
imported this item for just the two existence results, creating a cycle. Factoring their common
foundation preserves the statements and removes that cycle. The helper's DAG proof now names those
two results separately. No unproved assertion has merely been renamed or moved to a new hole.

The brief suggests LeanFinder, Loogle and grep, but the node schema groups LeanFinder and Loogle
together and also requires LeanSearch. The first preflight exposed this metadata omission; an
additional real LeanSearch returned only constituent scalar APIs, now recorded on all affected nodes.

The explicit intermediate sheaves in the pro-etale source-unit composition avoid an elaboration
heartbeat timeout. Restoring the default backward transparency in the foundation prevents unnecessary
unfolding of geometric definitions; that file then compiled in 46.3 seconds (36.9 seconds in the
final affected-file batch). The same default setting reduces the final comparison compile from
59.3 to 53.8 seconds. No compile time limit or heartbeat limit is raised. The foundation refactoring
serves the import cycle, and the subsidiary modules each isolate a proved mathematical result.

## New nodes

`lem-sp-scalar-universal-derived-unit`: converts the existing canonical scalar universal
property to the exact-functor unit interface on an arbitrary essentially small site.
The proof applies scalarUniversal_iff. Both definitions stay unchanged; the API avoids
repeated normalization of concrete derived localization data. The module compiles in
2.5 seconds and has no hole.

`def-sp-comparison-forget-scalars`: forgetComparisonIso. Its attached declaration is proved.

`def-sp-derived-scalar-ext-unit`: DerivedExtUnit. Its attached declaration is proved.

`def-sp-exact-functor-derived-unit`: DerivedUnit. Its attached declaration is proved.

`lem-sp-cartier-complement-frame`: Invertibility of the canonical divisor section on the complement. Its attached declaration is proved.

`lem-sp-cartier-etale-kummer-derived-unit`: etale kummer derived unit. Its attached declaration is proved.

`lem-sp-cartier-pole-boundary-existence`: cartierPoleBoundary existsUnique. Its attached declaration is proved.

`lem-sp-cartier-pro-integral-derived-unit`: pro integral derived unit. Its attached declaration is proved.

`lem-sp-cartier-pro-integral-residue-derived-unit`: pro integral residue derived unit. Its attached declaration is proved.

`lem-sp-cartier-pro-integral-scalar`: pro supported generator scalar. Its attached declaration is proved.

`lem-sp-cartier-pro-kummer-derived-unit`: pro kummer derived unit. Its attached declaration is proved.

`lem-sp-cartier-pro-root-scalar`: pro root scalar. Its attached declaration is proved.

`lem-sp-cartier-reduction-existence`: cartierReduction existsUnique. Its attached declaration is proved.

`lem-sp-comparison-constant-generator`: comparison constant generator. Its attached declaration is proved.

`lem-sp-comparison-map-ext-bijective`: comparison mapExt bijective. Its attached declaration is proved.

`lem-sp-derived-scalar-ext-unit-transport`: derivedExtUnit transport. Its attached declaration is proved.

`lem-sp-derived-scalar-ext-unit-zero`: extUnit zero. Its attached declaration is proved.

`lem-sp-etale-supported-integral-derived-unit`: supported integral derived unit. Its attached declaration is proved.

`lem-sp-etale-torsor-extension-presentation-exists`: Existence of the free extension presentation of an etale torsor. Its attached declaration is proved.

`lem-sp-open-closed-integral-sections`: The normalized sections presentation of the integral open-closed sequence. Its attached declaration is proved.

`lem-sp-relative-torsor-extension`: Relative extension class of a torsor with a specified section. Its attached declaration is proved.

`lem-sp-residue-finite-root-map-iso`: residueFiniteRootMap isIso. Its attached declaration is proved.

`lem-sp-residue-kummer-derived-unit`: kummer derived unit. Its attached declaration is proved.

`lem-sp-residue-kummer-iso-derived-unit`: kummer iso derived unit. Its attached declaration is proved.

`lem-sp-residue-quotient-derived-unit`: quotient derived unit. Its attached declaration is proved.

`lem-sp-scalar-boundary-comparison`: scalar boundary comparison. Its attached declaration is proved.

`lem-sp-scalar-ext-unit-composition`: derivedExtUnit comp. Its attached declaration is proved.

`lem-sp-scalar-ext-unit-iso`: derivedExtUnit iso. Its attached declaration is proved.

`lem-sp-scalar-unit-ext-bijective`: scalar unit ext bijective. Its attached declaration is proved.

`lem-sp-scalar-unit-ext-comparison`: scalar unit ext comparison bijective. Its attached declaration is proved.

`lem-sp-supported-integral-residue-sequence`: supported integral residue sequence. Its attached declaration is proved.

`lem-sp-universal-unit-shift`: universal unit shift. Its attached declaration is proved.

Change records: `coord/changes/N1-cartier-reduction-foundation.md` and `coord/changes/N1-supported-derived-scalar-unit.md`.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
