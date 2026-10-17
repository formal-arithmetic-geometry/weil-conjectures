## What changed

Proved `AlgebraicGeometry.Scheme.smooth_strict_local_field_model_core` in the item module,
with its public signature and public imports unchanged. Restored the private chart presentation
and repaired its use of the colimit: it now uses the canonical cocone of
`strictHenselizationAffineDiagram`, which actually defines `strictHenselizationRing`.
The compatibility import `Sheaf.AlgebraicGeometry.EtaleLocalRingTriples` exposes the same
triples theorem while compiling with the available algebraic strict-henselization modules.

The proof has three proved private parts: regularity/dimension, the prescribed residue
identification, and the algebraic function-field embedding. For the last part, the chart
algebra is ind-etale, hence flat; flatness over the integral chart makes its structural map
injective. Extend this map to the function field by the fraction-field universal property.
The source ind-etale separability theorem makes numerator and denominator images integral
over that field, so every fraction is algebraic. The structural equation is checked on the
chart's ring by the lift equation and the generic-stalk description.

Added proof import `WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale`. Updated the existing DAG proof and dependency list
for this route. The generic ind-etale-to-weakly-etale result is a source-library tool from
`lem-weil-pbc-ind-etale-stability`; the unit route is preserved. No definitions or existing
public statements changed, and no consumers require adaptation.

## Proved and sorry left

Closed the item's one hole, by declaration name:
`AlgebraicGeometry.Scheme.smooth_strict_local_field_model_core`
(node `lem-sc-smooth-strict-local-field-model-core`). All four private helpers are proved.
There are zero holes left in the delivered module and zero holes added or split off.
This proves the item from the existing named project lemmas; some of those dependencies
remain admitted in the library. It does not claim to close their holes.

Single-file compilation passed without warnings. The public theorem's signature was
compared against the original source; it is unchanged. The affine chart is nonempty because
it contains y; the proof includes the zero-dimensional and generic-point cases, with Nat
subtraction justified by the finite dimension formula. No extra characteristic assumption
or algebra structure is introduced into the public statement.

## No longer needed

Removed direct proof imports `Sheaf.RingTheory.StrictHenselizationTriplesPresentation` and
`Sheaf.RingTheory.StrictHenselizationFaithfullyFlat`. Their nodes
`lem-sc-strict-henselization-triples-presentation`,
`lem-sc-strict-henselization-faithfully-flat`, and
`def-weil-pbc-faithfully-flat-ring-map` are no longer direct dependencies of this proof.
The replacement argument uses flatness of the affine ind-etale algebra over a domain.
Those modules remain reachable through the strict-henselization dimension theorem;
no global pruning is asserted.

Replaced the direct import `WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples` with
its existing compatibility module `Sheaf.AlgebraicGeometry.EtaleLocalRingTriples`.
The triples theorem and its node are still used, so this replacement is not mathematical
pruning. The second reading also removed redundant direct proof imports
`WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs` and
`Mathlib.RingTheory.Flat.TorsionFree`; their APIs remain available through the other
imports. The regular-local-domain node is still used, so it is retained. No further
mathematical nodes or modules are bypassed.

## Where the brief, the DAG or earlier work was wrong

The removed chart proof assumed `smallStrictHenselizationCocone` had vertex
`strictHenselizationRing`. Following the upstream sync it instead has the older upstream
strict-henselization colimit as its vertex; these are distinct constructions. The repaired
proof uses the cocone defining the stated ring throughout, with its canonical coprojections.
The original direct triples import also collided with older compiled dependencies; the
existing compatibility import resolves that interface conflict without duplicating definitions.
The function-field injection needs only flatness over an integral chart, so the planned
faithfully-flat triples-presentation detour is unnecessary. No source statement was weakened.


## Second reading by F3

1. Compared the sole delivered module with the repository version using `diff` and
   compared the public theorem signature byte for byte: unchanged. The public imports
   are unchanged, and there are no definitions, statement changes, or forced adaptations.
   The restored chart presentation and the three additional components are private proved
   helpers, not substitute public statements.
2. Compiled the module successfully without warnings using `lcompile.py`. Searched for
   holes and forbidden declarations: none. A scratch copy with `#print axioms` for the
   public theorem and all four private helpers reports only `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx` from existing imported open theorems. There is no hollow
   definition or arbitrary object selected by a new unproved existence statement.
3. No statements were split off and no holes were added. Read the affine colimit
   comparison, residue-field identification, dimension argument, and fraction-field lift
   from the top down. The chart is nonempty because it contains y; regularity gives a
   nontrivial domain; flatness over the domain chart supplies injection. The equation
   `dim(stalk) + a = d` in natural numbers covers a = d and d = 0 without truncated-
   subtraction assumptions. For the generic point the same localization and fraction-
   field argument applies. The fraction-field algebra structure is exactly the lift i.
4. Checked the existing source and Mathlib routes: regular stalks, the finite-type
   dimension formula, residue functoriality, the affine-chart ind-etale theorem, flat
   torsion-free modules, and the fraction-ring universal property supply the components
   directly. The former faithfully-flat presentation detour is unnecessary. Reviewed
   the source local calculation and `dag/units/sk-prop-sf-cbc.json`: this is an internal
   local algebra argument; the unit's empty `realized` lists and route are unchanged.
   Audited the proof imports with single-file deletion probes; retained imports are
   necessary in the resulting module. The report lists all removed old dependencies.
5. The existing node changes only `proof`, `proof_deps`, and `proof_origin`; its natural-
   language statement and verbatim Lean statement are unchanged. `proof_deps` is exactly
   the union of the proof steps' `uses`. The steps agree with the canonical affine
   colimit, regularity/dimension, residue functoriality, flatness injection, and ind-etale
   separability arguments. No new nodes or change records are required.

Second-reading changes: corrected the public theorem's proof docstring to describe
flatness over the chart and the actual residue-functoriality argument, removed its stale
claim that hK is used to identify the dimension-formula algebra, and restored a source
explanation for the private chart helper. The Lean proof itself required no repair.
The import audit and final delivery checks are recorded below.


The deletion probes also found and removed two redundant proof imports:
`WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs` and
`Mathlib.RingTheory.Flat.TorsionFree`. The final proof compiles with both absent;
all remaining proof imports were required by their deletion probes (including the
separate `PointCount` probe, which needs `specMap_residueFieldAlgebraMap`).
These removals do not prune their modules from the targets' import closure.
