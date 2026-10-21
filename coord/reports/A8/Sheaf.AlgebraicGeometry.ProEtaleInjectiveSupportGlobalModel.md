## What changed

Filled `AlgebraicGeometry.ProEtale.proEtaleInjectiveSupportGlobalModel` without changing
its statement or public imports. Added proved private helpers for the sheaf adjunction,
the inclusion-normalized sectionwise kernel comparison, and its naturality. The
adjunction argument follows the already-proved private argument in
`SupportLocalizationTriangle`; no other module is changed.

The section comparison uses `finiteSupportedSections_sections` at the terminal object.
The fibre-product restriction and restriction to the canonical complement differ by an
explicit isomorphism of site objects. `ModuleCat.isLimitKernelFork` then gives the
actual categorical kernel isomorphism, with its kernel inclusion. Composing with
`globalSectionsLowerStarIso`, the supported closed comparison, and global-section
evaluation gives the required natural isomorphism and its exact normalization.

The derived comparison is the proved general
`Functor.rightDerivedFunctorPlusCompIso'`. Its unit compatibility gives the final
model equation after identifying the two induced termwise homotopy maps. Lower bounds,
termwise injectivity and all three invertible units are proved directly.

Updated the item's DAG proof, proof dependencies and proof origin to match this route.
No new public declaration, statement change, definition repair, or consumer adaptation.
The required local-command change record is
`coord/changes/A8-proetale-injective-support-private-scopes.md`; it documents section
variables and local attributes, with zero downstream Lean consumers.

Searches: LeanFinder found ordinary topological pullback adjunctions but no replacement
for closed-support inverse image. Loogle found the generic right-derived API; the local
source search found `PlusComp`, its exact unit equation, and the private sheaf adjunction
in the already-proved localization module. The retained argument uses those existing
constructions rather than new support-theoretic assumptions.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.ProEtale.proEtaleInjectiveSupportGlobalModel`
(node `lem-pur-proetale-injective-support-global-model`).

Zero holes remain in the item. Zero holes added; zero split off. Every private helper
is proved, and every private definition is a concrete construction.

Validation: the final remote single-file compile passed in 19.9 seconds with no
diagnostics. A direct source comparison confirmed that the public theorem statement
and public imports are unchanged; the file has zero `sorry` and all lines have at most
100 characters. The delivery tool runs the required final compile and axiom preflight.

## No longer needed

Removed private proof imports:

- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`.
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`
  (already available through the published sheaf and derived interfaces).
- `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`
  (reexported by `PlusComp`).
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`.

The proof no longer directly depends on nodes
`lem-weil-pbc-ring-sheaves-grothendieck`,
`lem-weil-pbc-proetale-ringed-open-closed`,
`lem-weil-pbc-dplus-injective-representative`, or
`lem-weil-pbc-kinjective-hom-derived`. Ordinary module-valued sheaf Grothendieck
instances replace ringed-presentation transport; direct-image orthogonality is the
existing disjoint-open calculation; the proved bounded-below composition theorem
provides derived canonicity without a separate K-injective Hom argument.

No module is withdrawn. Existing public imports remain verbatim, including the
localization theorem used to specify the support model. Thus these removed direct
proof dependencies do not claim global pruning of their remaining importers or users.
The unit route is preserved: no unit statement or proof step is bypassed or changed.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable dependency was found. The old plan used more general
intrinsic ringed-site machinery than the published ordinary module-valued sheaf
interface needs. Preservation of injectives here requires only finite-limit
preservation of closed direct image, already supplied by its ordinary right-adjoint
structure. The separate K-injective representative-independence argument is already
encapsulated in the proved bounded-below composition theorem and its unit equation.

The adjunction itself was already proved privately in `SupportLocalizationTriangle`,
so its source argument is reused locally without altering that module's interface.

The first delivery preflight requested the local-command change record and pushed
nothing. That record is included in the repaired packet.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
