## What changed

Proved `RingHom.exists_limit_module_localization_ring_data` in
`Sheaf.RingTheory.LimitModuleLocalizationRingData` with its signature and existing public import
unchanged. Two proved private helpers implement the construction: `presentationSystem` descends
one finite presentation and builds its pushout diagram on the cofinal upper tail;
`localizedSystem` builds the prime-localized diagram from the existing localization-colimit
theorem, retaining each stage's actual localization predicate. Their local definitions have
concrete data and proved compatibility fields.

Added `Sheaf.RingTheory.LocalizedPushoutTensor` with the fully proved generic theorem
`RingHom.exists_localized_pushout_tensor`. It pastes the original pushout with localization base
change, identifies the result with the tensor product, and applies nested localization. Both
transition and limit tensor-localization clauses follow from this theorem. The remaining
locality, essential finite type, and compatibility clauses are proved directly in the item.
All added imports in the item are proof-only. Updated the item's node proof and dependencies
and added the generic lemma's node. No existing interface, definition, or target was changed;
no forced adaptation is needed.

Source read: Stacks Tags [00QV](https://stacks.math.columbia.edu/tag/00QV) and
[00QX](https://stacks.math.columbia.edu/tag/00QX), including the explicit polynomial-quotient and
contracted-prime construction. The proved upstream finite-presentation descent theorem
implements that finite-polynomial-quotient argument. The unit `sk-thm-p1` and all its realized
steps are unchanged. `lem-kun-fp-algebra-descent` is used as a proved generic tool, not to replace
any unit-level step.

## Proved and sorry left

Closed 1 original hole: `RingHom.exists_limit_module_localization_ring_data`
(node `lem-limit-module-localization-ring-data`). Neither private helper contains a hole.
Added 0 holes: `RingHom.exists_localized_pushout_tensor`
(node `lem-weil-pbc-localized-pushout-tensor`) is also fully proved. No `sorry` remains in either
delivered module. This is a proof, not a decomposition.

Both modules compile without warnings via `lcompile.py --all`. The delivery dry run checks
all delivered declarations with its axiom probe. The original public signature was compared
with the repository version and is identical.

The new theorem was checked on the boundary cases before being stated: M=N only localizes
once; if M consists of units, the intermediate localization is the original pushout; zero
rings are permitted whenever the hypotheses hold; transitions need not be injective or flat.
The proof uses only universal properties and localization at nested submonoids, so it covers
all these cases without further hypotheses.

## No longer needed

Second reading removed the redundant proof-only import
`Mathlib.CategoryTheory.Filtered.Final`; its API is already available through the other imports.
No pre-existing import was removed. The existing public import of
`Sheaf.RingTheory.LimitModuleRingData` still provides the unchanged statement's exported
interface. Its theorem `RingHom.exists_limit_module_ring_data` and the finite-type-image
construction in `Sheaf.RingTheory.LimitModuleRingDataCore` are not used by this proof: images of
finite-type algebras do not supply the required transition pushout squares. Their nodes
`lem-weil-pbc-limit-module-essentially-finite-presentation-over-system-ring`,
`lem-weil-pbc-limit-module-ring-data-core`, and `lem-weil-pbc-finite-type-ring-system` are not
proof dependencies of the updated node; these modules remain imported through the unchanged
public interface, so this delivery claims no module has left the target import closure.

Removed redundant candidate imports before delivery: `Mathlib.RingTheory.Localization.Basic`,
`Mathlib.RingTheory.TensorProduct.Basic`, and `Mathlib.RingTheory.Localization.BaseChange` from
the new module, since `Mathlib.Algebra.Category.Ring.Constructions` exports the needed API;
`Mathlib.RingTheory.Localization.AtPrime.Basic` and
`Mathlib.RingTheory.LocalRing.RingHom.Basic` from the item, since its used imports provide them.
No module or node outside the argument was added. The original 14 proof steps are implemented
by the same finite-presentation, pushout, and prime-localization route, with the existing
localization-colimit theorem handling the fraction witnesses.

## Where the brief, the DAG or earlier work was wrong

The item's original DAG marks each construction step non-elementary but supplies no proof
uses (`proof_deps` was empty). The delivery now records the actual proved descent and colimit
lemmas and the new, proved generic tensor-localization lemma.

The source `.tex` and blueprint text are not present in this read-only clone; the cited Stacks
pages were read online. LeanSearch returned HTTP 500 and is recorded as unavailable, not as a
negative search. Loogle and source grep supplied the localization APIs used in the proof.

`blueprint_refs.py ancestor` cannot follow this item's `created.item`, which records a Lean
module rather than a node id. The new node inherits the item's already recorded blueprint
ancestor and adds the item node to its `via` chain; no existing blueprint field was changed.
The upstream descent theorem's `@[stacks 00R4]` annotation is already noted as a citation error
in `lem-kun-fp-algebra-descent`; the declaration's proved statement and finite-relation proof,
not that tag annotation, are used.

## New nodes

`lem-weil-pbc-localized-pushout-tensor` in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-localized-pushout-tensor.json` records
`RingHom.exists_localized_pushout_tensor` in
`lean/Sheaf/RingTheory/LocalizedPushoutTensor.lean`. This is a generic single-square result with
arbitrary nested multiplicative submonoids and arbitrary rings. It has no directed diagram,
finite-presentation descent, colimit construction, or locality conclusion. It is fully proved
and is used twice in the item's real construction. Searches for localization/pushout and
localization/tensor in the whole blueprint found no exact duplicate. The existing
`lem-pc-localized-approximation-base-change` also changes the base to its prime localization
and includes modules; it does not state this single-square result. The three logged searches
are attached to the new node. No change record is required.

## Second reading by C1

1. **Visible interfaces — pass.** Compared the item module with the repository using diff and
   an exact substring check: the existing public theorem signature is byte-for-byte identical.
   No existing definition or public import changed. The new module is declared in this report.
2. **Proofs — pass.** Both delivered files compile without warnings through `lcompile.py --all`.
   A scratch axiom probe reports only `propext`, `Classical.choice`, and `Quot.sound` for both
   public theorems, with no `sorryAx`. There are no holes or forbidden declarations. The selected
   colimit structures and localization equivalences are determined by universal properties;
   no data is obtained from an unproved arbitrary-existence assertion.
3. **New statements — pass.** No sorry statement was split off. The fully proved generic tensor
   theorem is strictly a single-square part of the argument. Checked identity/trivial-denominator
   and zero-ring cases: none requires an omitted injectivity or nonzero hypothesis. Read its
   docstring, node, and proof. Independent LeanFinder search returned localization base-change,
   tensor-localization, and tensor-pushout ingredients, but no exact theorem with this square and
   nested localizations; Loogle did not recognize `IsPushout`. Source rg found the stronger-context
   localized approximation result, not a duplicate of this generic statement.
4. **Route and pruning — pass after repair.** Read the construction top down against Stacks
   Tags [00QV](https://stacks.math.columbia.edu/tag/00QV) and
   [00QX](https://stacks.math.columbia.edu/tag/00QX). It descends one finite presentation, forms
   concrete pushouts, and prime-localizes the system; it does not merely rename the original hole.
   The old node had no `proof_deps`; the report also identifies the unused ring-image route.
   The `sk-thm-p1` realized statement and steps are untouched and no unit step is bypassed.
   Individually tested removal of five candidate proof imports: only
   `Mathlib.CategoryTheory.Filtered.Final` was redundant, and it was removed. No module is claimed
   pruned from the targets' closure.
5. **DAG — pass.** Checked the existing-node diff, all actual dependency theorem applications,
   the new node's fields and verbatim Lean signature, and the unit's `realized` record. The proof,
   dependencies, and origin describe the actual finite-presentation/pushout/localization route.

Second reading changed only the redundant proof import and this report. No theorem statement,
proof body, or node was changed. Closed 1 original hole and added 0 holes.
