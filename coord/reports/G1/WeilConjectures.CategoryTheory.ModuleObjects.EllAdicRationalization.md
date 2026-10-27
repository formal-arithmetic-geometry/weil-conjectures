## What changed

Closed both holes in
`WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization`.
The preservation proof equips E with its induced normed algebra structure,
applies continuous integral scalar exactness, and specializes the already proved
generic exact scalar-extension preservation theorem.

The localization proof compares the actual total left derived extension with
termwise exact extension using its canonical comparison isomorphism, transports
the shift and triangulated structure, and applies the already proved private
`CategoryTheory.rationalization_of_subcategory_models` preserved in
`Sheaf.UpstreamExtra.WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization`.
Its premises are the existing integral model and denominator theorems,
`CondensedRing.derived_nsmul_isIso`, and the preserved proved private
`CondensedRing.integral_scalar_map_eq`. The latter already implements Hom continuity
and finite-stage equality detection. No proof is replaced by another hole.

Added only private proof imports and local irreducibility attributes in the source.
All original declaration signatures, attributes, public imports and non-theorem
bodies stay unchanged. The localization node now describes the reused archive route.

Removed one unused private import of the item from the unclaimed module
`Sheaf.Paper.CompletedCondensedCoefficients`. That module otherwise stays
byte-identical and compiles with its existing explicit coefficient imports.
This breaks the cycle from the archive and model/denominator dependencies back to
this item. The change record is
`coord/changes/G1-ell-adic-rationalization-proof-and-cycle.md`; it lists the complete
consumer union and current holders. No target meaning changes or consumer edits.

Validation: both edited modules compiled through lcompile.py. After adding local
irreducibility attributes, the complete item compiled in 28.6 seconds. The coefficient
module also compiled after removal of the private import. Delivery checks compile
both files with their declaration/axiom probes. No profiling options remain.

## Proved and sorry left

Holes closed: 2 of the original 2.

- `AlgebraicGeometry.ProEtale.boundedConstructible_derivedExtendScalars_obj`
  (`lem-sfb-extend-scalars-bounded-constructible`).
- `AlgebraicGeometry.ProEtale.isLocalization_boundedConstructibleExtendScalars`
  (`thm-sfb-extend-scalars-localization`).

Holes added: zero. Split-off statements: zero. No sorry remains in either edited
module. Existing unresolved dependencies elsewhere in the library are retained;
this is a proof from existing declared inputs, not a claim that all target axioms
are already discharged. The existing derived and rationalization constructions
are unchanged.

## No longer needed

Removed the unused private import
`WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization` from
`Sheaf.Paper.CompletedCondensedCoefficients`. No source-library public import was
removed and no declaration or module was withdrawn.

The following planned direct dependencies of the localization node are unnecessary
for this proof and have been removed from its proof_deps:

- `lem-sfb-integral-derived-extension-comparison`, module
  `Sheaf.AlgebraicGeometry.IntegralDerivedExtensionComparison`: this imports the item,
  so the proof instead constructs the canonical termwise comparison locally using
  exactness and derived uniqueness. The source triangulation is supplied by the
  existing coefficient-specific instance.
- `lem-sfb-rational-derived-scalar-invertible`, module
  `Sheaf.AlgebraicGeometry.RationalDerivedScalarInvertible`: the already proved
  `CondensedRing.derived_nsmul_isIso` supplies the scalar-unit premise, and the archived
  helper obtains powers by induction.
- `lem-sfb-integral-localization-hom-colimit`, module
  `Sheaf.Paper.IntegralLocalizationHomColimit`, and
  `lem-sfb-scalar-unit-equality-detection`, module
  `Sheaf.CategoryTheory.ScalarUnitEqualityDetection`: the archived proved
  `CondensedRing.integral_scalar_map_eq` already performs this continuity/detection
  argument from sheaf Hom continuity and the strict localization-complex model.
  Its actual input nodes are now recorded instead.
- `lem-sfb-rationalization-localization-hom-criterion`, module
  `Sheaf.CategoryTheory.RationalizationLocalizationHomCriterion`: the already proved
  private criterion inside the archive supplies the same categorical glue, using
  `lem-sfb-rationalization-scalar-fractions`.

These modules are not withdrawn; other consumers may need them. The retained archive
still uses its continuity/model dependencies, and none is marked globally unused.
Removed the obsolete `det-prop-sfb-qlbar-colimit-x-invert-ell` entry from tool_uses:
the proof uses the existing continuous scalar-invertibility theorem instead.

## Where the brief, the DAG or earlier work was wrong

The live item has two holes, despite old review metadata from before the source sync
recording zero. The preservation-node plan remains applicable verbatim.
The localization-node plan overlooks that its specialized comparison module imports
this very item and therefore cannot be imported into it. Constructing the canonical
comparison locally avoids that direct cycle. All other relevant dependency cycles
passed through one unused private import in CompletedCondensedCoefficients; removing
that edge makes the already proved archive, model and denominator inputs usable.
The archived helper proofs are preserved unchanged and no zero-hole archive is
withdrawn. The blueprint unit route is retained: bounded constructibility, restricted
extension, localization, and uniqueness of localization in the original equivalence.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
