## What changed

Proved `AlgebraicGeometry.logCondition_etale_local` and
`AlgebraicGeometry.fineChart_etale_local` in the assigned module. All existing public
signatures, definitions, attributes and public imports are unchanged.

The private implementation identifies pointed neighbourhoods on an étale
localization with the slice of global pointed neighbourhoods. Initiality of the
slice forgetful functor gives canonical monoid- and ring-stalk isomorphisms,
compatible with germs and structural maps. These transfer the local log axioms to
the global prelog sheaf. The global log structure retains exactly that prelog data;
its extra fields are proofs. The new proof-only import
`Sheaf.AlgebraicGeometry.LogUnitSectionLift` supplies the existing unique unit-section
lift theorem, giving bijectivity of `unitSectionMap`.

For charts, the stalk isomorphisms preserve units and transport the generated
pushout congruence. The composed cover lifts each geometric point, and the original
monoids and their hypotheses supply fineness and conditional saturation.
The existing proof of `EtaleLogStructure.isChart_comp_prelogIso` is retained; its
three private stalk-isomorphism helpers were moved earlier for reuse.

The node proof and proof dependencies now record this route. The complete
implementation stays in the assigned module; there are no new modules or nodes.

## Proved and sorry left

Closed 2 holes of 2, both belonging to
`lem-trf-log-condition-fine-chart-locality`:

- `AlgebraicGeometry.logCondition_etale_local`.
- `AlgebraicGeometry.fineChart_etale_local`.

Added 0 holes. The item contains no `sorry`. Its existing third public theorem
`AlgebraicGeometry.EtaleLogStructure.isChart_comp_prelogIso` remains proved.

The log-condition proof uses the already stated
`AlgebraicGeometry.EtaleLogStructure.existsUnique_unit_section_lift`
(`lem-trf-log-unit-section-lift`), whose proof remains `sorry` in its owning module;
this delivery neither adds nor changes that hole. All private helpers in this
delivery are fully proved.

Validation: single-file compilation and the delivery tool's compile/probe. Edge
cases checked in the argument include empty covers and empty schemes (the
geometric-point assertions are vacuous), identity localization, the trivial chart
monoid, arbitrary nonintegral monoids in chart transport, and fine monoids without
saturation (saturation is used only for the conditional final clause).

## No longer needed

No imports were removed: existing public imports retain the module's public
interface, and the single new proof-only import is used.

The following former direct proof dependencies are unnecessary for this proof:

- `lem-weil-pbc-etale-covering-base-change`: compare geometric stalks at a lift in
  one cover member instead of constructing pullback covers of every test object.
- `def-weil-pbc-etale-sheaf-of-sets`: its statement dependency remains, while the
  sectionwise argument now uses the existing unique unit-section lift theorem.
- `lem-weil-pbc-small-etale-representable-presheaf-sheaf`: no representable affine
  line or new structure-sheaf descent argument is constructed here; its obsolete
  top-level tool approval is removed from the item's node.
- `def-pc-fibre-product` and `lem-a1-locally-ringed-space-affine-adjunction`: the
  affine-line representation argument is no longer used in this module.

These are removals from this node's proof dependencies, not claims that their
modules are unused elsewhere. No library module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The existing chart statement tests geometric stalks on two different small étale
sites. Thus sectionwise relocalization alone does not make the two `IsChart`
predicates definitionally equal: canonical monoid- and ring-stalk comparisons are
needed. The proof now supplies these comparisons, their germ and structural
compatibility, preservation of log units, and invariance of the generated chart
congruence explicitly.

The alternative stalkwise proof of the log condition avoids repeating the
sheaf-equalizer proof. It uses the existing unit-section lift theorem, which became
available in the shared library during this session. No statement or definition
repair was needed, and the unit route is unchanged.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
