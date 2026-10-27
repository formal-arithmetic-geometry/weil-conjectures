## What changed

Proved `AlgebraicGeometry.Scheme.CompletedConstantPresentation.completion_preservesCokernel`
in `Sheaf.Paper.CompletedConstantCompletionRightExact`, with its original signature and public
imports unchanged. All added helpers are private and proved; no other existing Lean module is
changed. Updated the item's node proof, proof dependencies and proof origin to the actual route.

The proof works directly on the pro-etale site with the original universes. Constant module
sections are exact: their functor preserves finite limits, and a set-theoretic splitting of a
surjection induces a splitting of constant set sheaves. For a module surjection, quotient kernels
come from one fixed kernel module; successive corrections by that module construct compatible
lifts, proving sectionwise surjectivity of completion without any finiteness assumption.

For an injection into a finite module, Mathlib's Artin-Rees lemma supplies a uniform shift in the
kernel filtrations over the Noetherian completed ring. Equality of the extended-ideal filtration
with the original-ideal filtration follows from `restrictScalars_map_smul_eq`. Exact constant
sections transfer the kernel bound. Shifting arbitrary lifts by that bound constructs compatible
kernel lifts. Factoring the original map through its image then gives sectionwise right
exactness, and evaluation reflects the resulting cokernel universal property.

Private proof imports supply the existing constant-module exactness/additivity API, ordinary
module exactness and cokernels, exact restriction of scalars, Noetherianity of completion,
Artin-Rees, and ideal extension identities. The existing `CompletedConstantSheafReduction`
dependency was already in the completion functor's import closure; this proof uses its proved
constant-module lemmas, not its tensor comparisons.

Validation: the final module compiled through `lcompile.py` in 21.8 seconds, with no errors or
warnings and no profiler options. The local quotient tower uses Mathlib's `mapQ_id` and
`factor_comp` API for its functor laws, avoiding expensive kernel unfolding of quotient maps.
No shared definition or interface was changed to meet the compile-time limit.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.CompletedConstantPresentation.completion_preservesCokernel`
(node `lem-weil-pbc-completed-constant-completion-right-exact`).

No `sorry` remains in the item. No holes or split-off statements are added. Every new private
helper has a complete proof. The proof handles arbitrary maps by image factorization; it makes
no injectivity assumption on the map in the public theorem. Zero modules, the zero ring, the
zero ideal and the unit ideal require no extra hypotheses or case exclusions.

## No longer needed

No original import was removed: the original item had only its necessary public import of
`Sheaf.Paper.CompletedConstantCompletionFunctor`. The following planned dependencies are omitted
from this proof and removed from this node's proof dependency list:

- `lem-weil-pbc-adic-completion-mod-power`: the original and extended ideal filtrations are
  compared directly on modules; quotient-ring evaluation is unnecessary.
- `lem-sc-noetherian-finite-module-finite-presentation`: no tensor comparison or finite
  presentation is needed.
- `lem-weil-pbc-constant-module-section-properties`
  (`Sheaf.Paper.ConstantModuleSectionProperties`): the exactness argument is proved directly at
  the required site universes; the tensor and flatness components are unnecessary.
- `lem-weil-pbc-limit-flat-modules`
  (`WeilConjectures.RingTheory.LimitFlatModules`): compatible lifts replace the tensor-limit
  comparison of Tag 0912.
- `lem-weil-pbc-tensor-right-exact`: the cokernel universal property follows from the direct
  sectionwise exactness proof.

These are dependencies unused by this item, not assertions that their modules can be withdrawn
from all other consumers. No module or declaration is deleted. The blueprint unit's statements
and realized proof steps are preserved.

## Where the brief, the DAG or earlier work was wrong

No statement repair was needed. The tensor-limit route in the original node is a possible plan,
but it is unnecessary: Artin-Rees and exact constant sections give a direct proof. The original
module's docstrings are preserved. The actual route and its sources are recorded in the updated
node: Stacks Tag 093J and the Artin-Rees/induced-topology lemmas in `algebra.tex`, following the
compatible-lift method also used in Mathlib's ordinary completion exactness proof.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
