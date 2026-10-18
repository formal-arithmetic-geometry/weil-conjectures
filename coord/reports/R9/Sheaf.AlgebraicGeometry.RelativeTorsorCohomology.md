## What changed

Proved `AlgebraicGeometry.Etale.relative_torsor_cohomology` without changing any existing
signature or public import. The proof constructs the simultaneous family from an explicit
framed-lift classification, followed by negation to match Mathlib's ordinary Ext convention.
It proves zero normalization, compatibility with forgetting, contracted-product naturality,
and scheme/coefficient pullback naturality for every comparison and equivariant map in the
original statement.

Added five proved supporting modules: `Sheaf.CategoryTheory.Sites.FramedLifts`,
`Sheaf.AlgebraicGeometry.RelativeCocycleCoordinates`,
`Sheaf.AlgebraicGeometry.RelativeTorsorClassNaturality`,
`Sheaf.CategoryTheory.FirstResolutionExtensionClass`, and
`Sheaf.AlgebraicGeometry.RelativeTorsorForgetNormalization`. The assigned module imports
only the naturality and forget-normalization modules for its proof. No existing public definition,
statement, consumer interface, or target was changed. The returned-delivery repair
relocates the existing private `coneMap_XIso` helper into the coordinates dependency and exposes
it for reuse; the old private declaration and duplicate `coneMap_coordinates` are removed.
The change record is `coord/changes/R9-relative-cone-coordinates-shared-helper.md`.
No forced adaptation is required. Updated the existing node's proof, proof dependencies and
proof origin, and removed obsolete tool-use approvals while retaining their original order.

## Proved and sorry left

Closed the original one hole, by declaration name:
`AlgebraicGeometry.Etale.relative_torsor_cohomology`.

Original holes: 1. Closed: 1. Remaining in the item: 0. Added anywhere: 0. Split off: 0.
All five new modules are completely proved. In particular the nontrivial supporting results
are `FramedLift.isIsomorphic_iff`, `FramedLift.surjective`,
`difference_of_equivariant_lifts`, `relativeFrameClass_surjective`,
`relativeFrameClass_eq_iff`, `relativeTorsorEquiv`,
`relativeFrameClass_map_eq`, `relativeTorsorEquiv_coefficient`,
`relativeTorsorEquiv_transfer`, `InjectiveResolution.extMk_firstCycles`, and
`relativeFrameClass_forget`. Definitions contain no postponed data or proofs.

Each of the six delivered Lean files has compiled with the remote single-file compiler.
The repaired item compiled in 13.9 seconds; no splitting for compile time was
used. A fresh topological compilation of all six files completed without warnings. The principal
classification, frame equivalence, naturality, extension-sign and forget-normalization results
all have exactly the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
The previous delivery passed its worker-side preflight but was returned at landing because
of a duplicate private helper. This repair compiled the full six-module delivery; its dry run passed at `bf9f22472c`
with review class CODEX, including compilation and all preflight checks. The original public statements remain unchanged.

Edge cases were checked in the constructions: the zero frame gives the trivial torsor
with zero section; frames are taken over any etale object U (so no inhabitance of U or its
sections is assumed); all arguments are valid for the empty open; equivalence is on
pointed isomorphism classes rather than a quotient that forgets the chosen section. The
naturality lemmas allow arbitrary equivariant maps and arbitrary supplied comparison maps.

## No longer needed

No original import was removed: the original public imports support the unchanged API and
existing resolution/connecting-map declarations, and the existing proof imports support
their already-proved bodies. Neither of the two new proof imports is redundant. No existing
module is withdrawn. The duplicate proof `coneMap_coordinates` is removed, and the original
`coneMap_XIso` proof is retained once in the common coordinates dependency.

The following direct proof dependencies are removed from this item's node. This is a
pruning of its planned proof route, not a claim that every named module is globally
unreachable; the unchanged statements and other parents may still require shared notions.

- `def-weil-pbc-abelian-etale-sheaves` — `Mathlib.CategoryTheory.Sites.Sheaf`.
- `def-weil-pbc-cohomology-pullback` — `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`.
- `def-weil-pbc-derived-inverse-image` — `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
- `lem-amb-bounded-injective-fibre-descent` — `Sheaf.CategoryTheory.BoundedInjectiveFibreDescent`.
- `lem-amb-signed-fibre-triangulated` — `Sheaf.CategoryTheory.SignedFibreTriangulated`.
- `lem-sc-etale-contracted-product-exists` — `Sheaf.CategoryTheory.Sites.EtaleContractedProductExists`.
- `lem-sc-etale-torsor-h1-functoriality` — `Sheaf.CategoryTheory.Sites.EtaleTorsorH1Functoriality`.
- `lem-sc-p1-split-ses-boundary-comparison` — `Sheaf.CategoryTheory.Abelian.SplitSESBoundaryComparison`.
- `lem-weil-pbc-cohomology-pullback-derived-unit` — `Sheaf.AlgebraicGeometry.CohomologyPullbackCanonicalArrows`.
- `lem-weil-pbc-cohomology-pullback-functorial` — `WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`.
- `lem-weil-pbc-complex-ses-connecting-formula` — `Mathlib/Algebra/Homology/HomologySequence.lean`.
- `lem-weil-pbc-complex-ses-triangle` — `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`.
- `lem-weil-pbc-degreewise-split-connecting-morphism` — `Mathlib/Algebra/Homology/HomotopyCategory/DegreewiseSplit.lean`.
- `lem-weil-pbc-dplus-injective-representative` — `Mathlib/Algebra/Homology/DerivedCategory/DerivabilityStructureInjectives.lean`.
- `lem-weil-pbc-etale-inverse-image-algebraic-structures` — `WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`.
- `lem-weil-pbc-etale-inverse-image-restriction` — `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
- `lem-weil-pbc-extension-by-zero-adjunction` — `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
- `lem-weil-pbc-extension-by-zero-exact` — `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
- `lem-weil-pbc-horseshoe-morphism-lift` — `WeilConjectures.CategoryTheory.Abelian.HorseshoeMorphismLift`.
- `lem-weil-pbc-inverse-image-composition` — `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
- `lem-weil-pbc-right-adjoint-preserves-kinjective` — `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`.
- `lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective` — `Mathlib/CategoryTheory/Sites/EpiMono.lean`.

The concrete cone construction and explicit cone homotopies replace the signed-fibre
triangulatedness and bounded-injective descent branches. The coefficient presentation and
arbitrary equivariant-map hypotheses already supply the torsors and maps, so no
contracted-product existence or absolute torsor pullback theorem is needed. Naturality is
proved by gluing the difference of two equivariant lifting maps and checking its boundary,
without a derived-unit comparison. The existing connecting maps are already defined from
actual short exact relative complexes; Mathlib's homology-sequence naturality proves their
squares directly, without a separate split-boundary theorem or horseshoe morphism lift.
The absolute lifting-torsor API already constructs the torsor using local surjectivity, so
this item need not separately invoke a sheaf-epimorphism local-surjectivity declaration.

Obsolete top-level `tool_uses` entries removed (the retained approvals are in their original
order):

- `def-weil-pbc-abelian-etale-sheaves`.
- `def-weil-pbc-cohomology-pullback`.
- `lem-sc-etale-contracted-product-exists`.
- `lem-sc-etale-torsor-h1-functoriality`.
- `lem-sf-derived-ses-triangle`.
- `lem-weil-pbc-cohomology-pullback-derived-unit`.
- `lem-weil-pbc-cohomology-pullback-functorial`.
- `lem-weil-pbc-dplus-injective-representative`.
- `lem-weil-pbc-etale-inverse-image-algebraic-structures`.
- `lem-weil-pbc-etale-inverse-image-restriction`.
- `lem-weil-pbc-extension-by-zero-adjunction`.
- `lem-weil-pbc-extension-by-zero-exact`.
- `lem-weil-pbc-horseshoe-morphism-lift`.
- `lem-weil-pbc-inverse-image-composition`.
- `lem-weil-pbc-right-adjoint-preserves-kinjective`.
- `lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective`.
- `lem-sc-p1-split-ses-boundary-comparison`.
- `lem-weil-pbc-complex-ses-triangle`.
- `lem-weil-pbc-degreewise-split-connecting-morphism`.
- `lem-weil-pbc-complex-ses-connecting-formula`.
- `def-weil-pbc-derived-inverse-image`.

## Where the brief, the DAG or earlier work was wrong

The return at head `128da7203` correctly identified that the new private
`coneMap_coordinates` repeated the existing private `coneMap_XIso` word for word.
The repair moves the original helper to the new coordinates module under its original name,
with its statement and proof unchanged, and removes both the old private copy and the new
duplicate name. The two existing short-exactness calls and the two coordinate-map calls
now use the single shared theorem. A reverse import would make an import cycle.
The downstream consumer scan found only the old private declaration and its two local uses,
so no external consumer requires adaptation.

The old proof plan's ordinary normalization omitted a sign required by the actual Lean
conventions. Mathlib's mapping-cone boundary is minus the first projection. The explicit
cone homotopy proves `I.extMk (I.cocomplex.iCycles 1) = -hS.extClass` for the first resolution
row. Thus a lifting frame `(s,b)` gives the raw cone cycle `(iCycles(s),-b)`, whose ordinary
class is **minus** the lifting-torsor class. The theorem's family is the negative of the raw
equivalence, and all additive naturality maps commute with this negation. No statement or
cone definition was changed. The old docstring is explicitly a historical proof plan;
the updated DAG and new lemma docstrings describe the actual proof and its sign.

An initial compilation cache retained older dependency artifacts and printed `sorryAx` for
the frame equivalence and its consumers. Fresh topological compilation, with explicit axiom
diagnostics in every module, verified that every principal result uses only the three allowed
axioms; no dependency proof or definition required repair. The five new modules retain their
principal axiom checks; the item itself was checked with a temporary diagnostic, then restored
to its original set of top-level commands.

The supplied dependencies are usable; being statements with postponed proofs would not
have been an obstacle. A shorter implementation uses the already-proved absolute
lifting-torsor API and direct concrete homology, rather than rebuilding the generic derived
fibre machinery. The unit record has no realized statement or proof-step constraint that
this replacement bypasses.

## New nodes

`lem-amb-framed-lifts-classification` attaches the general pointed lifting-presentation,
translation criterion and invariant-difference descent module. All results are proved;
it leaves no work to a later worker.

`lem-amb-relative-cocycle-coordinates` attaches the actual cone-coordinate computation,
cycles/boundaries classification, raw pointed-torsor equivalence, absolute projection, and
boundary criterion for maps. All results are proved.

`lem-amb-relative-torsor-class-naturality` attaches coefficient and scheme-transfer
naturality via invariant differences of lifting presentations. Both results are proved.

`lem-amb-first-resolution-extension-class` attaches the explicit cone homotopy and the
negative first-resolution extension-class identity in an arbitrary abelian category.
Both results are proved.

`lem-amb-relative-torsor-forget-normalization` attaches the normalized ordinary comparison
of a framed relative class using the canonical cocycle comparison. It is proved.

Each new node has its source, full proof in steps, exactly matching proof dependencies,
verbatim Lean declaration, three actual Mathlib search kinds, and the same chapter/unit as
the item. Searches of the entire blueprint (framed lifts, relative cocycle, first resolution
extension, extension class, and torsor) found no duplicate of the principal refinements, but missed the private helper duplicate
identified by the return. The existing ordinary torsor theorem was reused.
The helper relocation is recorded in
`coord/changes/R9-relative-cone-coordinates-shared-helper.md`.

## Second reading by R9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
