## What changed

Proved AlgebraicGeometry.Scheme.ProEt.localSystem_affine_descent_presentation in
Sheaf.Paper.LocalSystemAffineDescentPresentation without changing its statement, its
public imports, or any existing definition. All added helpers are private and proved.
The proof constructs the finite affine coproduct cover (including empty X), restricts
and glues the supplied trivializations on its disjoint components, identifies the
constant sheaf with the relative coproduct representable, constructs compatible
arbitrary-scheme transport and proves its identity and cocycle laws, and constructs
the unique overlap isomorphism by the map-pullback adjunction. The existing clopen
coproduct theorem gives both the sections description and the transition conditions.

Private arguments adapt the already-proved source-library EtaleDisjointCover,
EtaleCoproductRepresentation, FiniteLocalModelsDescentDatumCompatibilityDatum,
FiniteLocalModelsDescentDatumTransportDiagonal and
FiniteLocalModelsDescentDatumTransportCocycle proofs to weakly etale objects; the
source-library modules themselves are unchanged. The DAG proof and dependencies
now describe the actual argument. Added only the private proof import
Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.Scheme.ProEt.localSystem_affine_descent_presentation
(node lem-sfb-local-system-affine-descent-presentation).
There are zero textual sorry left in the item, zero holes added, and zero split-off
statements. This is a proof, not a decomposition. All helpers have complete proofs.
The imported declarations may retain their pre-existing upstream dependencies.
The complete item compiled cleanly through lcompile.py in 24.0 seconds after resuming
the interrupted session. The theorem header matches the current repository verbatim;
all Lean lines are at most 100 characters. deliver3.py checks axioms.

## No longer needed

Removed proof imports Sheaf.AlgebraicGeometry.EtaleComparison and
WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal.
The proof uses existing weakly-etale instances for open immersions and the canonical
continuous/cocontinuous restriction-sheafification comparison, respectively.

Removed proof dependencies and obsolete tool approvals:
- det-pe-morphisms-etale-comparison: Mathlib already supplies the needed instances.
- lem-weil-pbc-site-sheafification-sections-local: no local-section uniqueness argument
  is needed; the restriction comparison is the functorial sheafification comparison.
- lem-weil-pbc-qcqs-finite-affine-open-cover: the existing
  Hom.singleton_mem_propQCPrecoverage API gives the singleton covering directly.
- lem-galois-yoneda-fully-faithful: the existing map-pullback adjunction and universal
  point extensionality construct and characterize the overlap isomorphism directly.

No module is withdrawn. No adopted source-library declaration is removed. Public
imports are preserved because their visibility is part of the existing interface.
The unit's finite-chart and clopen-transition descent route is retained.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was required. The existing plan's categorical
steps can be implemented using universal points and the map-pullback adjunction in
place of an additional Yoneda full-faithfulness application. The available proved
etale transport arguments need neither finiteness nor etaleness beyond stability of
the test objects, so their weakly-etale versions can be proved privately here.
The first resumed delivery preflight identified an added file-level variable command
as an interface change. Its binders are now explicit on the two private helpers.
No change record or consumer adaptation is needed: no public signature, definition,
instance, attribute, file-level option, variable command, or public import has changed.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
