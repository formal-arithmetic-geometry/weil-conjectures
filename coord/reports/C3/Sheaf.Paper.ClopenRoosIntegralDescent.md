## What changed

Extracted the canonical integral restriction interface into
Sheaf.Paper.ClopenIntegralRestriction and publicly re-exported it from the item.
Existing theorem names, instance attributes and definition bodies are preserved.
The ordinary functor is renamed clopenIntegralModuleRestriction to resolve the returned
global-name collision; every occurrence in the item and augmented consumer is adapted.
Its mathematical definition and all hypotheses are unchanged. The completed coefficient
comparison and exactness are now proved.
This extraction breaks the reverse import from AugmentedIntegralDescent, allowing
its stated comparison theorems to be used by the item.

The item applies the generic signed Roos comparison, including its transition,
cone-coordinate and evaluation equations. It applies integralRoosCalculus for derived
Roos descent and projects the augmented reduction and integral membership assertions.
Both integral full-subcategory equivalences are constructed by restricting the ambient
derived equivalence, retaining all morphisms and its unit and counit.

## Proved and sorry left

Seven of the original twelve holes are closed; zero holes are added and zero are split off.
The two proved declarations moved to the extracted interface are:

- WeilConjectures.PurityFiniteSetting.clopenCompletionMap_existsUnique
- WeilConjectures.PurityFiniteSetting.clopenIntegralRestriction_exact

Their node is def-pur-clopen-integral-restriction. The extracted module has zero holes.
The five proved declarations in the item are:

- WeilConjectures.PurityFiniteSetting.finiteClopen_strict_roos_comparison
- WeilConjectures.PurityFiniteSetting.finiteClopen_derived_roos_descent
- WeilConjectures.PurityFiniteSetting.finiteClopen_augmented_reduction
- WeilConjectures.PurityFiniteSetting.finiteClopen_integral_membership
- WeilConjectures.PurityFiniteSetting.finiteClopen_integral_subcategories

Five existing holes remain, each belonging to lem-pur-clopen-roos-integral-descent:

- WeilConjectures.PurityFiniteSetting.finiteClopen_strict_tower_equivalence
- WeilConjectures.PurityFiniteSetting.finiteClopen_resolution_reduction
- WeilConjectures.PurityFiniteSetting.finiteClopen_completed_tensor_unit
- WeilConjectures.PurityFiniteSetting.finiteClopen_strict_tensor_reductions
- WeilConjectures.PurityFiniteSetting.finiteClopen_integral_scalar_extension

The adapted AugmentedIntegralDescent retains its two existing holes,
augmentedIntegralReductionComparison and augmentedIntegralMembershipBounds, belonging
to lem-pur-clopen-augmented-integral-descent. All its existing proofs are preserved.
Temporary diagnostic modules ending __probe.lean are excluded from the delivery.

## No longer needed

No modules are withdrawn. No original item imports are removed. The old direct import
of ClopenRoosIntegralDescent in AugmentedIntegralDescent is replaced by the extracted
interface. The full-subcategory proof uses the derived equivalence already supplied by augmented
descent. All four original proof dependencies remain used or needed by the five retained
proof plans, so no dependency node is pruned. No module pruning is claimed.

The returned packet compiled before this repair. A textual declaration inventory over
current main with all three delivered Lean files overlaid finds zero collisions among
the integral restriction declarations. Validation of the renamed interface, consumer,
item and simultaneous import is recorded after the repair checks.

## Where the brief, the DAG or earlier work was wrong

Repair of returned head 265e2b9d020, sole return point: the extracted ordinary functor
collided with WeilConjectures.PurityFiniteSetting.clopenIntegralRestriction in
Sheaf.Paper.ClopenStrictSystemComparison. The earlier report's claim that these names
were in different namespaces was wrong. They share a namespace but define different
objects. The existing functor takes a PurityFiniteSetting and a morphism over its field
and returns constructibleIntegralPullback on constructible derived categories. Ours
takes a prime and an open immersion of arbitrary schemes, and maps ordinary completed-ring
module sheaves to ordinary module sheaves by exact restriction and scalar transport.
Its source is scalarReductionSource, not a constructible derived category. Reusing the
existing declaration would change the statement's categories and operation. Under the
return's explicit exception for different declarations, the ordinary functor is renamed
clopenIntegralModuleRestriction. The existing derived declaration and all its consumers
are unchanged; this is not a duplicate theorem under another name.

AugmentedIntegralDescent imported the item for definitions, preventing the item from
importing that declared proof dependency. The interface extraction repairs the cycle.
The shared augmented dependency acquired proved exactness and integralRoosCalculus
during this session; the delivery was refreshed to preserve those proofs verbatim.

The completed-operation theorem states strict comparisons on good flat K-flat
representatives, whereas the item's strict tensor and scalar statements quantify over
arbitrary complexes. A direct specialization therefore does not prove those clauses.
The resolution clause likewise allows K-flat resolutions without termwise flatness;
the augmented comparison's flat-term hypothesis cannot simply be assumed.
These unchanged statements retain their documented proof plans.

## New nodes

def-pur-clopen-integral-restriction records the extracted interface and its two proved
properties. No new sorry-bearing theorem is introduced. The change record is
coord/changes/C3-clopen-integral-restriction-extraction.md.

## Forced adaptations

Sheaf.Paper.AugmentedIntegralDescent is currently unclaimed (previously held by T5).
Its import changes from ClopenRoosIntegralDescent to ClopenIntegralRestriction,
and its six references to the ordinary functor become clopenIntegralModuleRestriction.
The original import gives the module-system dependency cycle
ClopenRoosIntegralDescent → AugmentedIntegralDescent → ClopenRoosIntegralDescent
when the item imports its stated proof dependency. The adapted import removes that cycle.
Apart from those six name substitutions and the import, all consumer lines are unchanged
from current main. The substitutions preserve the denoted functor and hence the mathematical
signatures. The consumer is unclaimed, so this interface repair does not modify a held
module. The consumer scan lists exactly the item and this dependency.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
