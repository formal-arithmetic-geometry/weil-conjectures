## What changed

Replaced the sole sorry in
`AlgebraicGeometry.HilbertSamuel.component_dimensions_eq_of_function_eq` by a complete
Lean proof from two strictly lower geometric statements. The original declaration signature,
its public imports, the target statements, and all existing definitions are unchanged.

The proof identifies an upstairs component with the closure of the unchanged part of an
original component, proves that the image of that closure stays inside the original closed
component, and uses near-point incidence for the converse. It derives nonemptiness of the
unchanged component part from incidence; it does not exclude components in the centre by
an extra hypothesis. The parent DAG now records this actual assembly.

Added `Sheaf.AlgebraicGeometry.StrictTransformComponentClosures` for the ordinary blowup
component classification and dimension calculation (old steps 4--5), and
`Sheaf.AlgebraicGeometry.HilbertSamuelNearComponentIncidence` for membership of a near point
in each original component's closure (old steps 1--3, with the support identification).
Each is a single public theorem with exactly one whole-body sorry, a self-contained proof
in words, its source, and a matching new DAG node.

Validation: remote `lcompile.py --all` compiled the two new modules in 13.2 s and 2.9 s,
and the parent in 13.6 s. After correcting the sole style warning, the final parent compile was clean in 2.6 s. The source excerpt ILO VIII 2.3.13, printed p.94, was read locally;
it supplies the synchronization context, not a claimed verbatim proof of component rigidity.

## Proved and sorry left

Closed the original direct hole in
`AlgebraicGeometry.HilbertSamuel.component_dimensions_eq_of_function_eq` (1 of 1).
There is no sorry left in the item module.

Added two direct holes:

- `AlgebraicGeometry.HilbertSamuel.strictTransform_component_closures`, node
  `lem-trf-strict-transform-component-closures`.
- `AlgebraicGeometry.HilbertSamuel.near_point_mem_component_closure`, node
  `lem-trf-hilbert-samuel-near-component-incidence`.

This is a decomposition, not an unconditional proof or a net reduction in holes:
one upper hole closed, two strictly lower holes added. The assembly is complete Lean.
The incidence statement has no dimension conclusion or upstairs component classification;
the general component theorem has no near-point or Hilbert--Samuel hypotheses and cannot
supply incidence at a specified exceptional point. Both parts are essential.

## No longer needed

No mathematical dependency or module is pruned from the argument. The original five-step
route and the unit route are retained, with its geometric glue now separately stated.

Removed the following direct proof imports from the item, replacing them with private
imports of the two new modules:

- `WeilConjectures.Compactification.StrictTransformBlowup`
- `WeilConjectures.Blowup.Affine.Defs`
- `WeilConjectures.Blowup.Proper`
- `WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange`
- `WeilConjectures.RingTheory.FiniteTypeDomainDimensionTrdeg`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.RingTheory.Spectrum.Prime.Topology`
- `Mathlib.RingTheory.ReesAlgebra`

Their mathematical roles remain below the two new nodes, through the existing normal-cone,
Rees, strict-transform, finite-type and dimension declarations. The parent's old direct
`tool_uses` entry for `lem-weil-pbc-finite-type-domain-dimension-trdeg` is removed because
the parent no longer invokes it directly; the new component-closure node still uses that
generic dimension tool. Its approval is requested from the independent reviewer; no new
maintainer approval is written by this worker.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. The existing declarations express the local normal-cone and
minimal-prime algebra, arbitrary relative Proj base change, the strict-transform comparison,
and the affine dimension formula. None directly provides either the near-point incidence
in the global component closure or the component-closure/dimension classification used
by the final set proof. These are the two strictly lower groups of proof steps isolated here.
The generic component theorem permits arbitrary fields and arbitrary centres; characteristic
zero and smoothness are confined to the incidence theorem, where the original normal-cone
argument needs them.

Edge cases checked mathematically: empty X, zero ideal (empty blowup), unit ideal (identity
blowup), components contained in the centre, reducible X with distinct component dimensions,
and nonclosed exceptional points. In the zero-ideal or empty case there is no y. For the unit
ideal the incidence hypothesis is impossible. A component contained in the centre has empty
unchanged part, so its survival at a near point is deduced by contradiction, not assumed.
The generic component statement remains valid even when some components disappear globally.

## New nodes

`lem-trf-strict-transform-component-closures` realizes old steps 4--5: ordinary component
closures and equality of their dimensions. The source is Stacks Divisors 0804/080E and
Varieties 0A21. Existing `ReducedBlowupGenericGeometry` and
`GenericallyReducedStrictTransformGeometry` require a centre avoiding every component
generically and do not cover arbitrary centres here; they are not duplicate statements.

`lem-trf-hilbert-samuel-near-component-incidence` realizes old steps 1--3 and their support
interpretation. It retains the existing near-normal-cone and directrix/minimal-prime nodes;
it does not replace either by an equally strong renamed copy. Searches of the current
blueprint for “component blowup”, “component closure”, and “near point”, and Mathlib
LeanFinder/LeanSearch/grep searches found no exact statement. Both nodes keep the item's
chapter, unit and blueprint ancestry. No change record is needed: no existing interface
or definition has changed, and no existing module other than the item was edited.

## Second reading by Z9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
