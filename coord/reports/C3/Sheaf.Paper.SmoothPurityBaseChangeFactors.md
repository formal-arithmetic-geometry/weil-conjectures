## What changed

Decomposed the remaining `tower_factors` proof in
`Sheaf.Paper.SmoothPurityBaseChangeFactors` into the two independent factor steps of
the blueprint: `tower_factor_orientation` and `tower_factor_tensor`. The item
assembles their conclusions and proves the gamma equation by naturality of the
fixed tensor comparison and functoriality of tensor. All hypotheses and conclusions
of `finite_factors` and `tower_factors` are unchanged; the finite proof is unchanged.

Moved the nine existing tower-coordinate constructions to the new
`Sheaf.Paper.SmoothPurityBaseChangeData`, publicly imported by the item. Eight bodies
are unchanged. `towerGamma` is constructed directly as its orientation/tensor
composite, instead of eliminating the compactification record to call the published
gamma. Eliminating the record identifies both definitions by rfl; the map is the same.
This removes the import cycle that would otherwise prevent separate factor modules.
The same declaration names and maps remain available to every importer.
Added proved APIs `towerGamma_eq` and `towerTensorComparison_naturality` in that
module. A private generic `tensor_factors_compose` lemma in the item carries the
bifunctor calculation. The tower proof applies it and composes explicit equalities,
so the kernel does not repeatedly reduce tower realizations in a chain of rewrites.
The private `extend_factor_pair` lemma similarly performs the existential/conjunction
elimination on abstract predicates before instantiation with tower statements.
Both split modules import the actual definitions, rather than taking repackaged
hypotheses asserting the desired theorem.

The orientation step gives only the two canonical comparison witnesses, their
finite WordComparison equations, and the orientation square. The tensor step
assumes the independently characterized coefficient-unit comparison and gives only
the tensor/counit square. It does not assume an orientation square or a gamma
square. Thus neither is the original theorem under another name.

Edge cases checked in stating the steps: d=0 uses the constant unit comparison;
the first tower index is n=0 with exponent ell^(n+1); empty schemes have unique
maps. The statements retain every original finite-field, smoothness, domain and
normalization hypothesis. They make no normalization assumption on K and no claim
that evaluation is faithful on arbitrary derived morphisms. Unit comparison
uniqueness and orientation detection are used only for equally shifted sheaf
towers. Ramified coefficient extensions are retained. The tensor step keeps the
unit WordComparison hypothesis: allowing an arbitrary s would be false already
for an identity square, by multiplying the unit isomorphism by a nontrivial scalar.

Validation: `lcompile.py --all` compiled all four sandbox modules successfully
(exit 0). After optimizing the logical assembly, the profiled item compiled in
50.4 seconds. Profiling options were removed; the final item and its direct importer
`Sheaf.Paper.FinitePurityCounitSystem` then both compiled successfully (exit 0)
against the final sandbox definitions. The unchanged consumer source copy was
removed from the delivery packet.
Before optimization, all nine moved definition blocks were compared byte for byte
with the originals. After optimization, eight remain identical and towerGamma has
the equivalent factor formula recorded in the change record. Both existing theorem
signatures remain byte-identical. All four
JSON node records parse and every dependency ID exists. Delivery preflight runs
through `deliver3.py`.

## Proved and sorry left

Closed the single original hole in
`AlgebraicGeometry.ProEtale.SmoothPurityBaseChange.tower_factors`
(node `det-sp-purity-bc-factors`) by a complete proof from two strictly partial
factor statements. This is a decomposition, not a net proof: 1 hole closed,
2 holes added, net -1. The final gamma composition is fully proved.

New proved declarations:

- `AlgebraicGeometry.ProEtale.SmoothPurityBaseChange.towerGamma_eq`.
- `AlgebraicGeometry.ProEtale.SmoothPurityBaseChange.towerTensorComparison_naturality`.
- The private helper `tensor_factors_compose`, the generic categorical composition.
- The private helper `extend_factor_pair`, the generic logical assembly.

Every remaining delivery-local sorry:

- `AlgebraicGeometry.ProEtale.SmoothPurityBaseChange.tower_factor_orientation`
  in `Sheaf.Paper.TowerFactorOrientation`, node `lem-sp-tower-factor-orientation`.
- `AlgebraicGeometry.ProEtale.SmoothPurityBaseChange.tower_factor_tensor`
  in `Sheaf.Paper.TowerFactorTensor`, node `lem-sp-tower-factor-tensor`.

No sorry remains in the item or in any definition. Each new hole is exactly a
public named theorem with a complete source/proof docstring and its own module/node.

## No longer needed

No existing module is withdrawn, and no mathematical branch is globally pruned.
No existing proof import was removed: the finite proof still uses its existing
proof imports. The original tower maps are reexported, not deleted; towerGamma has an equivalent
construction with a smaller dependent term.

The item's direct tower proof dependencies are now the two factor statements and
the shared construction/API node. Its old direct tower proof dependencies
`lem-sp-diagonal-exchange-cube`, `lem-sp-section-dnc-integration-square`,
`lem-pur-dnc-coefficient-transport`, `det-sp-finite-general-ring`,
`lem-sp-orientation-scalar-tower-transport`, `det-sp-tower-gamma`,
`det-sp-tower-exceptional-bc`, `lem-sp-proetale-ctf-pullback-domains`,
`lem-sp-compact-projection-base-change`, `lem-sp-tensor-counit-exchange-calculus`,
and `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` are delegated to the
appropriate genuine factor subarguments or are already embodied in the published
construction. They are not claimed as unused by the project. In particular the
monoidal pullback naturality needed for final composition is already a field of
`SpTowerShriek.Geometry`; that composition needs no new generic tensor theorem.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The remaining tower plan had not been
connected to its Lean interfaces. The generic orientation transport requires finite
orientation equations and strict-heart source presentations; the generic tensor
calculus requires identification with the actual restricted adjunction and projection
comparisons. These are the two source-backed subarguments now stated separately.
The unit's orientation/tensor route is preserved.

## New nodes

`def-sp-purity-bc-tower-data` records the existing named-compactification tower
constructions and the two proved expansion/naturality APIs, in
`Sheaf.Paper.SmoothPurityBaseChangeData`.

`lem-sp-tower-factor-orientation` records proof (1), including construction of the
specified constant-unit and Kummer Tate-line pullback comparisons and the actual
orientation square, in `Sheaf.Paper.TowerFactorOrientation`.

`lem-sp-tower-factor-tensor` records proof (2), the inverse projection/counit
transpose compatibility on the full uniform ctf domain, in
`Sheaf.Paper.TowerFactorTensor`.

Change record: `coord/changes/C3-tower-gamma-factor-formula.md`. No existing module
other than the item is edited. The direct importer is compiled unchanged against
the equivalent gamma definition.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
