## What changed

Replaced `logIdeal_algebraization_descent`'s single sorry by a complete assembly
of three strictly smaller geometric statements. The assembly constructs the
canonical overlap isomorphisms from a proved equality-of-ideals existence
helper. They are selected only inside the proof and are uniquely determined
by their composites with the monic ideal inclusion. The assembly proves
the diagonal, cocycle and uniqueness equations by cancellation against the
ideal inclusion. The cocycle uses explicit associativity and inclusion
equalities. The main module enables Lean's transparency checks and locally
keeps the existing ideal-module and inclusion implementations irreducible;
these local attributes do not change any importer's environment. It obtains
the normalized tensor isomorphisms from
`existsUnique_idealTensorPullbackComparison` and étale flatness.

On a strict étale source, the assembly applies image-ideal existence again and
uses uniqueness to identify that ideal with `K.comap f.base`. This transfers
finite type and gives uniqueness, the chart formula and canonical descent on
the source. Thus the strict-compatibility lemma does not repeat these clauses.

Moved the seven existing definitions, byte for byte with their docstrings,
to the new `LogIdealAlgebraizationData` module and publicly re-exported them.
This permits the three new theorem modules to state their hypotheses without
an import cycle. All original public dependencies remain publicly re-exported through the data
module, and the main theorem's signature is unchanged. No existing module besides the assigned item was edited.
The relocation is recorded in
`coord/changes/X2-log-ideal-algebraization-data.md`.

## Proved and sorry left

Closed the body of `AlgebraicGeometry.logIdeal_algebraization_descent`
(node `lem-trf-log-ideal-algebraization-descent`), originally the item's only
sorry. The item now has zero textual holes. This is a decomposition, not a
complete proof independent of the three new holes. Count: one original hole
reduced, zero original holes fully discharged without new assumptions, three
holes added; net hole reduction is minus two.

Added exactly three public theorem holes, each in its own new module:

- `AlgebraicGeometry.logIdeal_image_exists_unique`
  (`lem-trf-log-ideal-image-existence`): existence, finite type and uniqueness
  only, from the finite-chart image construction and étale algebraization.
- `AlgebraicGeometry.logIdeal_image_chart_formula`
  (`lem-trf-log-ideal-image-chart-formula`): the inclusion-normalized affine
  tilde formula for an already given image algebraization.
- `AlgebraicGeometry.logIdeal_image_strict_etale`
  (`lem-trf-log-ideal-image-strict-etale`): preservation of fine coherent
  generators, equality of structural image sections and the image predicate
  for the extended ideal; no finite-type, uniqueness, chart, descent or
  tensor-isomorphism conclusions on the source are assumed.

Every remaining hole has its complete natural-language proof and source in
its docstring and a matching DAG node. The seven relocated definitions have
no holes. The three private helpers are proved completely. The final development
compile checked all five modules successfully, with the main module taking
16.0 seconds and the others at most 1.1 seconds. The delivery tool checks the
final import cleanup again. All profiling and diagnostic heartbeat options
have been removed.

## No longer needed

The item now needs only one public import, its common data module. The eight
old direct public imports are redundant in the item and removed there:
`FineLogCoherentIdeal`, `LogRegularPair`, `LogIdealChartPresentation`,
`CoherentFiniteType`, `TensorPullbackSectionAdjunction`,
`EtaleTensorSectionsSheaf`, `TensorPullbackStructureSheaf`, and
`Mathlib.AlgebraicGeometry.Modules.Tilde`. They are retained as public imports
of the data module, preserving exactly the original public dependency closure.

Removed these four direct proof imports from the item:
`WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`,
`Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence`,
`Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`, and
`Sheaf.AlgebraicGeometry.EtaleExtensionFreePresentationsHom`.
The parent's now-obsolete direct `tool_uses` entries for
`lem-weil-pbc-quasi-coherent-module-cokernel-image`,
`lem-weil-pbc-affine-tilde-gamma-adjunction`, and
`lem-sfb-scheme-etale-module-exact-finiteness-comparison` are removed.
Their mathematical content remains in the proof plans of the smaller image
lemmas; this is not a claim that those nodes can be withdrawn globally.

The original image construction, affine tilde adjunction, exact/finiteness
comparison, Zariski/étale equivalence, site quasi-coherence definition, and
étale extension lemmas remain necessary below the three new statements.
No existing module or node is withdrawn and no unit route is bypassed.
`HasCanonicalEtaleIdealDescent` itself needs only equality of repeated ideal
pullbacks, not a separate new effective-descent theorem.

## Where the brief, the DAG or earlier work was wrong

The existing declared dependencies provide the general quasi-coherent and
site-comparison APIs but do not state the logarithmic generator-to-image
calculation or its strict étale stalk compatibility. Those geometric steps
are now exposed as smaller theorem items rather than left inside the main
proof. The existing descent predicate concerns ideals already identified as
restrictions of K; its identities can be proved directly by equality and
monicity, including on nonaffine overlaps and for an empty index type.

The cited ILO VIII 3.4.2 is written under the log-regular fs convention of
3.4.1. Only its image-ideal construction is used, with the extension to fine
log schemes justified by the coherent-chart definition in VIII 3.3.7 and the
Stacks quasi-coherent comparison. Neither log regularity, saturation nor
Noetherian hypotheses are added. Edge checks cover the empty scheme, the
zero ring, unit image ideals, zero structural images, and nonsaturated fine
monoids. The full definition bodies and the theorem signature were compared
against the source and are byte-identical after relocation.

## New nodes

`def-trf-log-ideal-algebraization-data` owns the seven unchanged definitions
in the new common data module; it adds no unproved assertion.

`lem-trf-log-ideal-image-existence` isolates steps 1–3 of the old plan:
constructing and uniquely algebraizing the finite-type structural image.

`lem-trf-log-ideal-image-chart-formula` isolates the affine-chart part of
step 4, using the finite-generator computation of steps 1–2.

`lem-trf-log-ideal-image-strict-etale` isolates the generator and image
restriction argument of step 5. The main proof derives all further source
properties from the first two new statements and the flat ideal comparison.

All new nodes inherit the item's chapter, unit and existing blueprint
ancestry. Searches for log ideals, coherent logarithmic ideals, monoidal
ideals, structural images and ideal chart formulas found no duplicate
blueprint statement. The existing ideal tensor-pullback theorem is reused
rather than restated. Change record:
`coord/changes/X2-log-ideal-algebraization-data.md`.

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
