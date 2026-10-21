## What changed

Proved `AlgebraicGeometry.ProEtale.constructible_internalHom_continuity` in
`Sheaf.Paper.ConstructibleInternalHomContinuity` from the stated finite-model,
closed-support, open-extension, triangle-closure and finite-generation declarations.
The public theorem signature and all public imports are unchanged.

The private proof first identifies continuity of the canonical cohomology cocone
with invertibility of the complex-model comparison. It proves continuity transports
through exact functors and the internal-module/section-module equivalence. The
closed-support model supplies the uniformly bounded input for finite-local-model
Hom; its natural closed formula and the closed-support adjunction supply the
closed stratum generators. Open extension then supplies the generation theorem's
stratum generators. Triangle closure transports through the derived equivalence,
and finite generation finishes the argument.

The new proof uses `import all` only for already proved generic helpers
(`complexHomologyPreserves`, `post_isIso_natIso`, `homFixed_derivedIso`, and
`resolutionDerivedIso`) in the two stated dependency modules. They introduce no
new assumptions or public API. Local irreducibility settings prevent expansion of
large sheaf-Hom/resolution constructions while elaborating abstract transports.
The `privateModule` style linter is disabled locally: this module has its public
theorem, and profiling showed the linter spending about 30 seconds scanning the
imported private declarations. Kernel checking and all proof checks remain enabled.

Naturality in both comparison applications is proved abstractly over categories
before specializing to the concrete sheaf-module functors; this avoids expanding
large coefficient constructions during identity-map rewriting. The helpers are
proved and are local to this module.

The private native continuity predicate is a proposition structure with named
continuity/bound fields. This avoids repeated unfolding of its large conjunction
in proof types. The complete delivered file compiles cleanly in 36.0 seconds;
there are no compiler warnings and no remaining holes.

All private helpers are proved. The auxiliary predicates contain only propositions;
no resolution or comparison data is chosen from an arbitrary unproved existence
statement. The comparison existence theorem is eliminated only in proofs.

The change record is
`coord/changes/F7-constructible-internal-hom-proof-context.md`; it documents the
proof-only commands, private instance, and the unchanged two downstream consumers.
`Sheaf.Paper.CartesianCoefficients` is retained as a unit-route import.

The existing node explicitly cites `det-lem-formal-closed-support-adjunction` for
the exactness/colimit argument; its proof, proof dependencies and proof origin describe this
assembly. Obsolete tool approvals are removed in their existing order. No other
module or existing declaration is changed.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.ProEtale.constructible_internalHom_continuity`
(node `lem-sfb-constructible-internal-hom-continuity`).

Zero holes remain in the item; zero holes are added or split off. The proof uses
existing stated dependencies, including their currently unfinished proofs, as the
stage-3 brief requires. This does not claim the dependency closure is axiom-free.

## No longer needed

Removed direct proof imports:

- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`
- `Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle`
- `Mathlib.CategoryTheory.Sites.LocalProperties`
- `Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four`
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`
- `Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuityDirectImage`
- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`
- `Sheaf.Paper.CondensedOpenClosedRecollement`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus`
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`
- `Sheaf.Paper.CoefficientRingedTensorHomModel`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed`
- `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`
- `WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory`
- `Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomModel`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Free`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.Paper.FiniteModelStratumFiltration`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`

The higher-level stated dependencies now encapsulate the bounded-free calculation,
local descent, support triangles and finite filtration/Postnikov assembly. Their
own needed dependencies remain intact. No module or upstream declaration is
withdrawn, and this report makes no claim that these modules are globally unused.

Removed direct proof dependencies
`lem-weil-pbc-proetale-ringed-open-closed` (exact closed direct image and its
colimits follow from the recorded closed-support adjunction) and
`lem-weil-pbc-unbounded-derived-iso-cohomology` (the public conclusion is already
the cohomology-cocone formulation; the generic model criterion uses Mathlib's
`DerivedCategory.isIso_iff`).

Removed obsolete tool approvals:

- `def-sbc-standard-tstructure-derived-category`
- `def-sfb-module-upper-lower-adjunction`
- `det-pe-bounded-continuity-direct-image`
- `det-prop-sfb-qlbar-colimit-x-integral-limit`
- `lem-pur-rhom-global-sections`
- `lem-sc-dvr-fg-torsionfree-free`
- `lem-sf-derived-homology-long-exact`
- `lem-sf-derived-ses-triangle`
- `lem-sfb-sheaf-cover-local-isomorphism`
- `lem-weil-l-adic-extension-integers-dvr`
- `lem-weil-pbc-completed-constant-sheaf-reduction`
- `lem-weil-pbc-condensed-open-closed-recollement`
- `lem-weil-pbc-constant-module-section-properties`
- `lem-weil-pbc-five-lemma`
- `lem-weil-pbc-left-adjoint-preserves-colimits`
- `lem-weil-pbc-noetherian-submodule-finite`
- `lem-weil-pbc-proetale-ringed-open-closed`
- `lem-weil-pbc-ringed-internal-hom-exact-restriction`
- `lem-weil-pbc-ringed-site-bounded-free-rhom-model`
- `lem-weil-pbc-unbounded-derived-iso-cohomology`
- `lem-weil-proetale-weakly-etale-localization`

The proof does not invoke these as extra direct tools. Its higher-level dependencies
still retain whichever of them their own proofs need. No unit statement or realized
unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The current DAG's six-step devissage is usable. Its support step mentioned two
models of Ri!; the current Lean interfaces already use the same concrete
`closedSupport` right-derived functor. No new uniqueness-of-adjoints theorem or
replacement support definition is required. The Lean proof explicitly checks the
naturality needed to transport the original colimit cocone.

The original theorem docstring described the older seven-step expanded plan; it
now describes the six stated helper applications actually used. The node remains
explicit that this is the internal filtered-colimit elaboration, rather than a
verbatim form of the paper's global direct-sum assertion.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
