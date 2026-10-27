## What changed

Only `lean/Sheaf/Paper/CompactSupportCondensedRealization.lean` and its existing node,
`lem-pur-compact-support-condensed-realization`, are changed. Public signatures,
definitions and public imports are preserved. No source-library file is changed.

`finiteProjection_isIso` uses a finite basis of the given extension E → F. Private
helpers adapt the existing continuous presheaf and sheaf basis construction from
`ModuleObject.Colimit.Compatibility` to coefficient carriers in Type u. The coordinate
maps are continuous because they are Q_l-linear maps between finite-dimensional
spaces. Sheafification gives an actual finite-free isomorphism; the existing proved
`finitePush_of_pointCopower` criterion applies to the actual coefficient map and c.g.
The prescribed projection is its composite with the invertible open scalar comparison.
The existing `fieldExtension_flat` theorem is used as a declared dependency.

`omegaSupport_preserves` applies the existing bounded-constructible open-extension and
direct-image preservation theorems to c.overI and c.overG. The latter uses exactly the
finite-subextension-valued algebraic-closure coefficient, through its existing
`IsFinitenessCoefficient` instance. No descent choice or new existence statement occurs.

The new proof import is a private `import all` of the source coefficient compatibility
module, exposing its proved private finite-copower criterion. The node retains the
unfinished plan and records the concrete shorter routes for these two auxiliary
declarations. The complete item compiled in 43.2 seconds against the current
setup overlay, with no profiling options.

## Proved and sorry left

Closed two of the seven original holes, with no holes added or split off:

- `WeilConjectures.CompactSupportCondensedRealization.finiteProjection_isIso`.
- `WeilConjectures.CompactSupportCondensedRealization.omegaSupport_preserves`.

Five original holes remain, all attached to
`lem-pur-compact-support-condensed-realization`:

- `WeilConjectures.CompactSupportCondensedRealization.omegaProjection_isIso`.
- `WeilConjectures.CompactSupportCondensedRealization.systemRefinement_id`.
- `WeilConjectures.CompactSupportCondensedRealization.systemRefinement_comp`.
- `WeilConjectures.CompactSupportCondensedRealization.omegaRefinement_isIso`.
- `WeilConjectures.compactSupport_condensedRealization`.

No new module or sorry is introduced. The separately assigned setup
module is outside this delivery and is not edited.

## No longer needed

No existing import, module or node is globally pruned. The original public imports are
needed for the published interface. An initially added private import of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` was
removed: that module is already public through `CondensedERealizationDefinitions` and
`ModuleObject.BaseChangeTheorems.MorphismDefs`. The planned ringed finite-free comparison is not
needed to prove the auxiliary finite projection: its source internal-module finite
copower argument already proves the actual map invertible. That abstract comparison
remains in the node for the unfinished completed-coefficient comparisons.

The auxiliary closure support-preservation theorem does not need finite-field descent,
the two-colimit theorem or `omegaProjection_isIso`. Those dependencies remain needed by
the original closure projection and simultaneous comparison plan, so none is removed
from the node's global dependencies.

## Where the brief, the DAG or earlier work was wrong

The current item has seven holes after the reviewed setup split; the setup module is
not duplicated in this packet. The source finite-basis helper is specialized to Type 0
coefficient carriers, so it cannot be applied directly to the item's Type u fields.
The private helpers here construct the universe-general basis comparison explicitly.
No statement is disputed, weakened or changed.

The descent proof described for `omegaSupport_preserves` is unnecessary: the source
library already proves both preservation factors for this exact coefficient. The
existing nodes `lem-sfb-dc-open-lower-shriek-preserves` and
`lem-sfb-dc-lower-star-preserves` are recorded as proof tools for this shorter route;
the main unit route and the remaining descent/naturality plan are preserved. No
maintainer `tool_uses` approval is added or changed.

For the remaining closure projection, the existing
`isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_app_of_isGE` is relevant, but
its coefficient source is a finite intermediate subfield of the algebraic closure.
It does not immediately identify the universe-general source field and the map in
`omegaProjection_isIso`. The original hole is retained without hiding that transport.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
