## What changed

Proved `AlgebraicGeometry.Scheme.proEtaleProjectionMateShiftData` in its existing module,
with its signature unchanged. A proved private helper `tensorModel_exact` resolves any fixed
coefficient by a flat-term K-flat complex, compares the published exact derived tensor with
the supplied tensor model by localization, and transports its shift and triangulated structures.
The main theorem composes these fixed tensor structures with the existing exact derived
pullback and K-injective derived direct image. The original public imports are retained;
all added imports are private proof imports. The item's DAG proof now records this argument.
Remote compilation accepted the proof in 7.3 seconds; the sole remaining warning, an
implicitly used existential binder in the private helper, was then renamed before delivery.

## Proved and sorry left

Closed the one original hole, `AlgebraicGeometry.Scheme.proEtaleProjectionMateShiftData`
(node `lem-weil-pbc-proetale-projection-mate-shift-data-s4`). No holes added, none left in the
item, and no split-off statements. The private helper is proved completely from the existing
resolution, fixed-tensor exactness, representative-comparison and localization APIs.

## No longer needed

No modules or declarations withdrawn; no existing imports removed. The former sole proof
dependency `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` is replaced in the proof route
by the explicit resolution, fixed-tensor exactness and normalized comparison dependencies.
It remains a statement dependency through `ProEtaleTensorModel`, so its module is still needed.
The existing `lem-sp-fixed-tensor-representative-comparison` is used as a generic localization
tool: its statement concerns arbitrary ring sheaves and tensor models on native pro-etale sites,
with no smooth-purity assumptions or geometric steps of that other unit.
`lem-pc-kflat-resolution` is likewise the generic resolution theorem needed for arbitrary
module sheaves, rather than a geometric step from the Picard unit.

## Where the brief, the DAG or earlier work was wrong

The original proof plan's only cited theorem supplies tensor/pullback comparison and preservation
of flat K-flat representatives, but does not itself assert fixed-tensor shifts or triangulatedness.
The published fixed-K-flat tensor exactness theorem and normalized fixed-tensor comparison
supply those missing interfaces. No mathematical statement or definition was changed, and no
unit route was bypassed. The fixed coefficient may be unbounded; no flatness or perfectness
assumption was added to it.

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
