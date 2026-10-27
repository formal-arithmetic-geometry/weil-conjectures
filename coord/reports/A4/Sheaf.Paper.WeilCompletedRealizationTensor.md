## What changed

`Sheaf.Paper.WeilCompletedRealizationTensor` now assembles its unchanged theorem
from the ordinary tensor comparison for completed constant modules and the already
proved `completedCechModuleTensorTransport`. Private proved helpers compose curried
tensor comparisons, derive regular-module normalization from the right-unitor
formula, and identify the successive maps of the total tensor bifunctor. A generic proved
helper also lifts the normalized comparison to total cochain tensors.

The proof establishes preservation of countable coproducts: evaluate the constant
module presheaf, apply the module sheafification adjunction and the named ordinary
scalar adjunction, then use the equivalence for coefficient and site transport.
The existing `mapBifunctorComparison` supplies the chain isomorphisms and their
summand formula. Naturality of the ordinary comparison and its regular-module
equation give precisely the displayed `(0,0)` normalization.

The new module `Sheaf.Paper.WeilCompletedConstantModuleTensor` states only the
ordinary-module construction and its regular-unit equation. Its docstring and
node describe how to assemble the already proved sheafification tensor and
scalar-extension constraint comparisons. No definition or existing signature is
changed. All new imports in the item are private proof imports.

Validation: the item compiled without warnings in 58.4 seconds through
`lcompile.py`; the new ordinary-module file compiled in 10.6 seconds. The item has
zero textual holes and the new module has one. The declaration signature was
compared byte for byte with the original, all node dependencies exist, and both
Lean files meet the 100-character line limit. Temporary profiling and heartbeat
overrides were removed. The delivery tool performs the independent preflight.

## Proved and sorry left

Closed in the item: `AlgebraicGeometry.Scheme.completedRealizationTensor`
(node `lem-weil-pbc-completed-realization-tensor`).

Added, and the only remaining textual hole in this delivery:
`AlgebraicGeometry.Scheme.completedConstantModuleTensor`
(node `lem-weil-pbc-completed-constant-module-tensor`). Its proof is exactly
`by sorry` in its own new module.

This is a decomposition: one upper hole closed, one strictly smaller ordinary
module obligation added, net zero holes. The remaining theorem contains no
cochain complexes, tensor totalization, naturality in chain maps, site
equivalence, coefficient-back transport or `(0,0)` inclusion. Those parts are
proved in the item using the existing declarations. No data is selected from a
new unproved existence theorem in any definition.

## No longer needed

None. All three original declared dependencies remain needed for the definitions
and the specified total tensor. No original imports were removed, and no module
or node is withdrawn. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original node describes the ordinary tensor calculation in words but cites
only definition nodes. There was no stated normalized ordinary tensor comparison
for `completedKoszulConstant`. The existing coefficient/site module transport is
already proved and is reused. Totalization, its summand formula, and naturality
already exist in `WeilConjectures.Mathlib.Algebra.Homology.Bifunctor`; they do not
need another split. The parent node now records the actual assembly.

The new ordinary theorem was checked mathematically on zero modules, the zero
ring, and the empty site: every map is the same sectionwise balanced tensor map,
so no nonzero, flatness or nonempty-site hypothesis is needed. The two scalar
formulas are inverse by balancing and multiplication, and regular maps are fixed
by the section 1.

## New nodes

`lem-weil-pbc-completed-constant-module-tensor`, in the parent's chapter and unit,
records the ordinary constant-module sheafification and scalar-extension tensor
comparison and its regular-unit equation. Its proof plan explicitly names the
existing pro-etale sheafification tensor theorem and the scalar-extension
constraint coherence theorem, followed by the calculation at section 1.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
