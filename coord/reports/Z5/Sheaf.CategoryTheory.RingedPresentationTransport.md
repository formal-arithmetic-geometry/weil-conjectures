## What changed

Replaced `CategoryTheory.ringed_presentation_transport`'s single sorry with a
compiling construction of every field of the original transport record. The
signature and all existing public data are unchanged. Moved those data verbatim
to `Sheaf.CategoryTheory.RingedPresentationData` and publicly re-exported them,
so the genuinely separate subordinate comparisons do not import their parent.
The change record is `coord/changes/Z5-ringed-presentation-data.md`.

The proof constructs localization comparisons from the existing
`scalarLocalization_regularColimit`, including the scalar-to-regular-multiplication
identity and the stage-zero/unit equation. It constructs termwise derived
factorizations, the derived equivalence unit/counit, derived relocalization and
the two kinds of derived restriction squares from the existing exact-functor
API. Additivity, exactness, all needed colimit preservation and preservation of
K-injectives for module equivalences are derived directly from equivalence.
The reverse unit and derived-Hom comparisons follow by cancelling the module
and derived equivalences. Five proved API theorems establish the actual
restriction properties and relocalization, leaving those out of the subordinate
restriction lemma's unfinished assumptions.

Four separate results state exactly the remaining geometric/closed arguments:
module equivalence and closed Hom, arbitrary element-site closed restriction,
ringed slice equivalences and module squares, and presentation invariance of
local ideal tests. Each has a new module, source, full proof in words and DAG
node. None has the full parent conclusion: the parent proves the localization,
derived and assembly steps itself. No arbitrary witness is used in a definition.

Validation: the data and subordinate statement modules compile, and the assembled
parent compiles in 23.6 seconds; the full data module compiled in 36.9 seconds. The unchanged sole consumer,
`Sheaf.Paper.RingedPushforwardCompletion`, compiles in 44.8 seconds with its
pre-existing long-line warning. The copied original definition block was compared
byte-for-byte with its new location. Earlier server preflight axiom probes for the data and parent modules exceeded
the probe limit; the tool noted that merge reruns them. The final delivery dry
run passes preflight with review class CODEX. The module compile checks above passed. No source-library file was modified. The change record lists every conservative
consumer-scan match, including 35 unrelated uses of the common name `derived`.

## Proved and sorry left

Closed the one upper hole in `CategoryTheory.ringed_presentation_transport` by
complete Lean assembly. This is a decomposition, not a sorry-free proof or a
positive net hole reduction. Original holes: 1. Item holes left: 0. Added holes: 4.
Net hole change for this packet: three additional holes.

The four added, named public theorem holes are:

- `CategoryTheory.ringed_equivalence_module_hom` —
  `lem-weil-pbc-ringed-equivalence-module-hom`.
- `CategoryTheory.element_restriction_hom` —
  `lem-weil-pbc-element-restriction-hom`.
- `CategoryTheory.ringed_equivalence_slices` —
  `lem-weil-pbc-ringed-equivalence-slices`.
- `CategoryTheory.ringed_equivalence_local_tests` —
  `lem-weil-pbc-ringed-equivalence-local-tests`.

The original theorem therefore still depends on sorry through those four
results. No sorry occurs in a definition or private helper. The new data module
has zero holes. Its five complete public API proofs are
`presentationElementRestriction_additive`, `presentationElementRestriction_exact`,
`presentationElementRestriction_kInjective`, `presentationElementRestriction_continuous`
and `presentationElementRestriction_relocalization`. The complete private proofs are `sequence_colimit_transport`,
`localization_transport`, `presentationAt`, `presentationRestrictions` and
`presentationDerivedSquare`; `inverseHomComparison`, `elementRestrictionCore` and the other private record
builders are also complete. The reverse-Hom builder maps its input Nonempty
proof directly; it makes no arbitrary choice of comparison data.

## No longer needed

The following four original direct proof imports are no longer needed in the parent:
`WeilConjectures.Algebra.Homology.HomComplex`,
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`,
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`,
`Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`.
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp` remains
a direct proof import because the parent now proves K-injective preservation itself. The Hom-complex/sheaf-Hom imports belong to
the element restriction result; the tensor and closed-monoidal imports belong
to the module-Hom result. Their mathematical dependencies remain needed below
those results. The parent uses `lem-sf-ringed-derived-closed-symmetric-monoidal` through the
module-Hom result. All original maintainer tool-use approvals are retained; none
is added or removed.

No module or node is withdrawn or globally pruned. The whole original unit route
is retained; this node does not itself realize a blueprint unit statement or step.
The old public imports are preserved transitively by the data re-export.

## Where the brief, the DAG or earlier work was wrong

The nine-step proof is mathematically useful, but the existing dependencies do
not supply the arbitrary geometric-equivalence module lift, arbitrary-sheaf
closed restriction, module slice squares or generalized-section local-test
comparison as Lean declarations. The existing site-object restriction theorem
alone does not supply the arbitrary-sheaf statement. These missing bridges are
now separate explicit statements, rather than an unexplained sorry in the whole
transport package.

The shortest available localization argument uses the existing regular-module
sequential-colimit theorem. The scalar presentation definition agrees with its
unitHomEquiv scalar map, proved by evaluating at 1. Colimit preservation compares
the diagrams and their zeroth coprojections, so no fraction calculation needs
to be repeated here. The original definitions, statement and universes required
no correction.

Checked the remaining statements on the identity equivalence, zero ring, empty
site, initial test sheaf, zero ideal, unit ideal, and zero derived object. The
local-test statement has no finite-generation or boundedness assumptions, and
the representable comparison uses sheafified representables without assuming
subcanonicity. The arbitrary choices of module equivalence packages in the
slice lemma are controlled by their specified direct images and uniqueness of
left adjoints.

## New nodes

`def-weil-pbc-ringed-presentation-comparison-data` records the relocated original
data, the two smaller input records and the five proved restriction API
theorems. It introduces no unproved existence claim and no hole. Its module is `Sheaf.CategoryTheory.RingedPresentationData`.

`lem-weil-pbc-ringed-equivalence-module-hom` isolates the module lift and the
closed-Hom comparison. Its conclusion omits all slices, restrictions,
localizations and local tests; the automatic exactness and K-injectivity fields
are proved by the parent rather than required here.

`lem-weil-pbc-element-restriction-hom` isolates closed exact element restriction,
further restriction and the sheafified-representable module comparison. It
concerns one site and does not assert any ringed-topos presentation equivalence
or local-test invariance.

`lem-weil-pbc-ringed-equivalence-slices` isolates the slice geometric construction
and its two module squares. It asserts no derived squares, localization
comparison, internal-Hom comparison or local-test invariance.

`lem-weil-pbc-ringed-equivalence-local-tests` isolates the generalized-section
argument for invariance of local ideal tests, assuming the whole module package.
It asserts none of the transport data in the parent conclusion.

All five nodes inherit the original chapter/unit and point through the original
node to the scalar-extension clause of `prop-weil-pbc-scalar-extension`.
Blueprint and library searches found no duplicate with the same scope. The four
source arguments are spelled out in the docstrings and node proofs.

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
