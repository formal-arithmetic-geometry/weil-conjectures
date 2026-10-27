## What changed

Replaced the body of `WeilConjectures.sfQcqsCompactSupport_reduction_ext` by a
complete assembly proof through finite-coefficient inputs. Its statement,
binders, universes, visibility and existing public import are unchanged.
Two private proof imports supply the geometric steps.

The proved private helper `reduction_map_ext_on_restriction` works for any
adjunction `L ⊣ R`. It shows that `L` detects equality of maps whose target is in
the essential image of `R`: identify the target with `R(N)` and use the inverse
Hom transpose, which composes `L.map f` with the counit at `N`.
This does not require faithfulness of `L` on its entire source category.

For a finite-coefficient input, the new proved theorem
`sfQcqsCompactSupport_torsion_coefficient_action` places the recorded
compact-support value in the essential image of scalar restriction. The helper
and the corresponding equation in the item's hypothesis then give equality of
the original components at that input. The remaining torsion-input detection
lemma turns these component equalities into equality of natural transformations.

The coefficient-action theorem is proved by constructing the comparison from
the actual proper/open compact-support image to the recorded value, using the
strict reduction-system adjunction and gamma. Its finite reductions are the
proper/open scalar mates. Finite comparison and conservativity on derived-complete
constructible objects show that the comparison is an isomorphism. The actual
proper/open image commutes with restriction of scalars; composing that
isomorphism with the constructed comparison proves the essential-image claim.
The private construction reuses the existence calculation of
`QcqsCompactSupportNormalizedLift` and the conservativity proofs of
`QcqsCompactSupportRealization`, without importing those downstream modules or
using their uniqueness statements. In particular it does not invoke the item
being proved, directly or indirectly through those modules.

Only the item, two new modules, and their DAG records change. No existing
statement, definition, public import or source-library declaration changes.

## Proved and sorry left

One original textual hole is closed:
`WeilConjectures.sfQcqsCompactSupport_reduction_ext`.
Its assembly proof compiles relative to the one remaining geometric obligation.
The new theorem
`WeilConjectures.sfQcqsCompactSupport_torsion_coefficient_action` is proved;
its private adjunction, completeness and constructibility helpers have no holes.

One hole is added, the entire proof of the public theorem
`WeilConjectures.sfQcqsCompactSupport_torsion_input_ext`, in its own new module,
node `lem-qcqs-compact-support-torsion-input-detection`.

The item's module contains zero textual holes, and the delivery contains one.
This is a decomposition of the original obligation, with net zero holes closed;
it is not a completed proof of the full rigidity assertion. Existing imported
geometric declarations may themselves still use sorry. No definition, instance
or private declaration contains a hole. Existential witnesses are eliminated
inside proofs only; no data definition chooses an arbitrary unproved witness.

All three modules compiled cleanly together after the final import changes.
The compile service checks each actual Lean run against the 60-second limit;
all three were accepted. The displayed wall times also include import-artifact
preparation, so those are not the Lean-only acceptance times. The isolated
coefficient-action proof check also passed cleanly in 6.8 seconds.

## No longer needed

No existing import is removed, and no node or module is withdrawn or claimed to
be globally pruned. The item now directly uses the two new nodes and
`lem-weil-derived-scalar-extension-restriction-adjunction`. Its former six direct
proof dependencies remain in the proof plan for the torsion-input detection step:

- `lem-weil-compact-support-reduction-tower-functor`;
- `lem-weil-compact-support-representative-independence`;
- `lem-sf-integral-open-reduction-comparison`;
- `prop-weil-pbc-direct-image-limits`;
- `lem-weil-pbc-ringed-strict-tower-homotopy-limit`;
- `lem-coef-derived-system-evaluation-calculus`.

The coefficient-action proof uses the already stated strict-system comparison,
finite comparison, constructible triangulated closure, and actual proper/open
restriction isomorphism. It does not need a new theorem asserting that scalar
restriction commutes with a newly chosen finite-action total limit: transporting
through the constructed isomorphism to the actual proper/open image avoids that
additional proposed route. No such extra module is added. Neither downstream
`QcqsCompactSupportNormalizedLift` nor `QcqsCompactSupportRealization` is imported.

The two new modules publicly import `CompactSupportFiniteAction` and
`IntegralCompactSupportCoefficientData` for their statement vocabulary. All additional imports of the proved coefficient-action
module are private proof imports. Its redundant explicit proof import of
`IntegralCompactSupportCoefficientComparison` was removed: the required API is
already exposed by `QcqsCompactSupportStrictReductionComparison`.

## Where the brief, the DAG or earlier work was wrong

The original plan does not expose a declaration asserting that arbitrary natural
comparisons are determined by their finite scalar images. In particular,
`integral_reductions_jointly_faithful` requires a `FiniteFieldDatum`, a
`SixFunctorOperationDatum`, and a `SixFunctorSpace`; it cannot be applied to the
arbitrary base field here. The scalar-reduction/total-limit adjunction alone does
not identify maps from their separately evaluated finite components.

The remaining lemma isolates adic density for ordinary natural transformations.
It assumes equality of the original components on actual restricted
finite-coefficient inputs; it has no hypothesis about reduced components.
The separate coefficient-action assertion does not quantify over natural
transformations and is proved in this delivery. The scalar-adjunction assembly
converts the original hypothesis into the density lemma's hypothesis. This is a
reduction through a different test class, with a separately proved preservation
step, rather than the original assertion renamed. The density/naturality step
itself remains unproved; no formal joint-monicity argument for separate derived
limit projections is claimed.

The current blueprint proof describes the proper/open coefficient mate and its
refinement/composition compatibility, rather than a ready-made theorem about
arbitrary natural transformations. The new statements are agent-formulated steps
in that context, not verbatim theorems of Bhatt--Scholze 6.7.7. No unit statement
or realized unit step changes; `sk-def-sf-operations` has no realized nodes
assigned to this item.

Edge cases checked at the statement level: zero inputs and empty schemes give
zero coefficient objects, and the adjunction argument still applies. Level zero
means positive coefficient exponent one. A finite coefficient presentation is
required as essential-image membership of derived scalar restriction; no action
is inferred merely from a scalar acting by zero on a derived object. The proved
action lemma exhibits an actual finite-coefficient object. No finite-field or
separated structure-morphism hypothesis has been added.

The blueprint ancestor tool returns no ancestor when following the stage-3
`created.item` module-valued chain. The new records use a null computed ancestor,
retain the item's source ancestor in the place text, and retain the intermediate
node chain. Whole-blueprint searches for torsion natural transformations and
compact-support restriction of scalars found no duplicate.

## New nodes

`lem-qcqs-compact-support-torsion-input-detection`, module
`Sheaf.Paper.QcqsCompactSupportTorsionInputDetection`: adic density for natural
comparisons tested on constructible integral objects in the essential image of
finite scalar restriction. Its source is the strict resolving-category and
naturality step of the original rigidity plan. The original scalar-reduction
hypothesis is absent. LeanSearch and LeanFinder returned generic derived
transformation and localization lemmas; Mathlib/source grep found no matching
geometric theorem. This is the single new unproved obligation.

`lem-qcqs-compact-support-torsion-coefficient-action`, module
`Sheaf.Paper.QcqsCompactSupportTorsionCoefficientAction`: the recorded value of a
finite-coefficient input retains that coefficient action. This theorem is proved
from the existing strict-system and finite comparison declarations, triangulated
closure, and `PurCompactSupport.restriction`. The actual image restriction theorem
found in the source library suffices after the constructive comparison; no new
limit-commutation assumption is needed. LeanSearch and LeanFinder returned
unrelated scalar/topological support lemmas; Mathlib pattern search found no
match. Neither new node adds a definition. No change record is needed because
no existing interface changes.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
