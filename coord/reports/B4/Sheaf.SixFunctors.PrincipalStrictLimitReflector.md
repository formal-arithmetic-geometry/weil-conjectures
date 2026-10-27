## What changed

Replaced the proof hole of
`CategoryTheory.RegularRoosKoszul.principal_strict_limit_reflector` without changing
its statement, definitions, or public imports. The proof uses the existing general
`CategoryTheory.ringedKoszulCompletionReflector` on the canonical small site.
It proves sectionwise monicity of the restricted scalar, constructs the singleton
unit-module generating family as a split epimorphism, transports the completion
property, and transports the universal Hom bijection. The last transport explicitly
uses the normalized unit equation and cancels the fully faithful derived-equivalence
map on Hom sets. The private proved helper
`precomposition_bijective_of_equivalence` performs this last calculation for an
abstract category equivalence, keeping the large derived-equivalence construction
out of its elaboration. Native and small-site instances are supplied explicitly
to the local-test comparison; the derived equivalence is locally irreducible only
while checking this proof. No shared definition or exported attribute is modified.

Added two proof imports for the comparisons described below, the proof import for
the general reflector, and the Mathlib presheaf monomorphism API. The two new modules
publicly import only the interfaces their statements need. No other existing module
or shared definition is changed. No change record or forced adaptation is needed.

Validation: `lcompile.py --all` compiled all three final modules without warnings:
1.9 s for the normalized comparison, 2.1 s for the local tests, and 18.5 s for
the reflector. No diagnostic options, heartbeat changes, or temporary Lean modules
remain in the delivery. The original theorem statement matches verbatim, and neither
new node depends back on the item.

## Proved and sorry left

The original module had one hole. Its declaration
`CategoryTheory.RegularRoosKoszul.principal_strict_limit_reflector`
(node `lem-sf-principal-strict-limit-reflector`) now has a complete Lean proof
from the existing ringed reflector and two comparison statements. There are zero
holes in the item module.

This is a decomposition, not a hole-free proof of the reflector. Two named theorem
holes are added, each in its own new module:

- `CategoryTheory.RegularRoosKoszul.principal_strict_small_model_comparison`,
  node `lem-sf-principal-strict-small-model-comparison`;
- `CategoryTheory.RegularRoosKoszul.principal_strict_small_model_local_tests`,
  node `lem-sf-principal-strict-small-model-local-tests`.

Thus one original hole is closed and two are added (net minus one hole closed).
Each remaining proof is exactly `by sorry`, with source and proof in words.
No definition contains a hole. Existing imported theorems keep their current proofs
and holes; this delivery does not claim to prove their dependencies.

## No longer needed

None: no original import, node, module, or unit step is withdrawn. The original
singleton dual-tower and normalized-derived-limit ingredients remain needed by the
new comparison node. The local-test comparison retains the slice restriction and
localization ingredients. The exact-product Roos variant was considered but is not
imported: its hypotheses do not match this theorem. This is not a claim to prune it
from the library or from another consumer.

## Where the brief, the DAG or earlier work was wrong

The existing node's plan is mathematically appropriate, but its small-model
completion/unit comparison and its local-completeness comparison were not available
as declarations with these particular universe and normalization interfaces.
The new nodes state precisely those missing steps. The attached Lean record for the
ringed-reflector node points to a specialized paper interface; its original general
`ringedKoszulCompletionReflector` declaration still exists and is the one used here.
The nearby principal Roos presentation comparison requires exact products, a
hypothesis absent from this item, so it cannot replace the total-derived-limit
comparison. No existing statement is disputed or weakened.

The comparison statements were checked on empty sites, zero rings, zero complexes,
and zero and invertible sections. Neither asserts regularity or exact products;
the regularity hypothesis of the original theorem is used to apply the existing
ringed ideal reflector through a monic scalar presentation.

## New nodes

`lem-sf-principal-strict-small-model-comparison`, in
`Sheaf.SixFunctors.PrincipalStrictSmallModelComparison`, identifies only the
normalized augmented strict total-limit object with a singleton small-site
presentation, including its unit. It asserts no completeness or Hom universal
property. Its proof in words follows singleton Koszul duality and derived-limit
uniqueness (Stacks Tags 0A0E and 0941), and retains the original dual-tower and
normalization dependencies.

`lem-sf-principal-strict-small-model-local-tests`, in
`Sheaf.SixFunctors.PrincipalStrictSmallModelLocalTests`, compares only the two local
vanishing predicates for an arbitrary derived object. It neither constructs a
completion nor asserts its universal property. Its proof in words uses the exact
module equivalences on slices, localization, derived internal Hom, and preservation
and reflection of zero objects. Sources are Modules on Sites localization and
Stacks Tags 0999 and 099B. Both new statements are strictly separate parts of the
original argument, and their combination with the reflector is proved in the item.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
