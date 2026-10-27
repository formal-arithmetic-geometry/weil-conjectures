## What changed

Proved `WeilConjectures.pointRationalFibreScalar_existsUnique` by normalized integral
natural isomorphisms, fully faithful carrier descent, and descent through raw
scalar localization. The sole new proof import is
`Sheaf.CategoryTheory.ScalarLocalizationNaturalIso`.

The normalized natural comparisons and the fully faithful carrier comparison are
private proof helpers. Existing public normalization definitions, public signatures,
public imports, and exported reduction attributes are unchanged.

Direct proofs of additivity and a streamlined integral-linearity calculation avoid
unnecessary unfolding. Fully proved private lemmas now perform the raw tensor
functor construction and the coefficient tensor scalar calculation over abstract
linear categories and modules. Their applications retain the original public
theorem statements while avoiding repeated geometric-category reductions. The
stagewise comparison supplies explicit associator arguments
for the same canonical composite; this elaboration-only definition edit is recorded
in `coord/changes/A9-point-stage-scalar-iso.md`.

## Proved and sorry left

Starting holes: two. Closed `WeilConjectures.pointRationalFibreScalar_existsUnique`.
The complete module and the original `PointFibreEquivalence` and
`PointRationalFamilyCommonStageNaturality` consumers compiled together using
`lcompile.py --all`. Neither consumer needed an adaptation; their unchanged copies
were used only for compatibility validation and are excluded from this delivery.
The original hole in `WeilConjectures.pointQbarFibre_existsUnique` is unchanged,
attached to `def-weil-finite-coefficient-point`. No split statements are added.
Holes closed: one; holes added: zero; actual holes remaining: one.

## No longer needed

No original import, node, module, or declaration is removed. The scalar proof uses
the proved `ScalarLocalization.naturalIso_of_integral` instead of repeating the
pure-tensor naturality calculation on rational morphisms. The original sections,
coefficient-lift, and tensor comparisons remain necessary.

## Where the brief, the DAG or earlier work was wrong

The latest blueprint's `sec-six-functors-basics/sk-def-sf-admissible/` version uses
condensed coefficients and the ordinary derived category over the algebraic
closure. The existing module and its consumers retain the earlier four-stage
interface. As in the preceding Q8 delivery, this packet proves the assigned
existing signature; it does not claim that the semantic migration is completed.

The localization theorem is an existing proved generic tool from
`lem-real-raw-localization-natural-iso` (unit `sk-r-real-linear`). Its statement
applies to the raw rational category and imposes no target linearity. No new
mathematical statement or alternative unit route is introduced.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
