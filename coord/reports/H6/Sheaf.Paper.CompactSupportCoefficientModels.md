## What changed

Proved `WeilConjectures.compactSupportCoefficientModels_furtherTensor` in
`Sheaf.Paper.CompactSupportCoefficientModels`. Specialize the existing ordinary
cancellation comparison to the retained quotient map. Its local section formula
identifies its inverse with the chosen unique module-balancing map. Its naturality
produces a natural isomorphism with the second module fixed. This is a constructed
private definition with a proved component equation, determined uniquely by its
local tensor formula. The existing module-balancing proof now uses a component of
this same comparison, sharing the cancellation construction with furtherTensor.
Apply the existing mapHomologicalComplex construction and conjugate with mapBifunctorSingle₂Iso.
Localize that chain isomorphism through the existing exact-restriction factorization.
A proved private lemma over arbitrary complexes cancels the target comparison in
every degree and proves uniqueness after localization, avoiding repeated unfolding
of the large sheaf expressions. Local irreducibility attributes keep the natural comparison, tensor-single
comparisons and coefficient constructions from unfolding during conversion; the
coefficient attributes are restored before the following scalar-extension proof.

The proof preserves all public signatures, definitions and imports. The existing
node's sixth proof step now records this argument. No new node or public statement is added. The complete file has typechecked through `lcompile.py`; all profiling options
are removed. Delivery validation also checks the axiom probe and file-time limit.

## Proved and sorry left

Original item holes: 2. Holes closed: 1. Holes added: 0. Item holes left: 1.

- `WeilConjectures.compactSupportCoefficientModels_furtherTensor`: proved.
- `WeilConjectures.compactSupportCoefficientModels_ordinary`: original named `sorry`
  remains, attached to `lem-pur-compact-support-coefficient-models`, with its original
  source and complete natural-language proof.

The chain identity works without the retained K-flat hypothesis, because both
objects in this clause are localizations of explicit ordinary tensor complexes.
No flatness of the ramified quotient is required, including at zero exponents.

## No longer needed

None. No import, node or module is removed. Existing dependencies remain for the
other proved clauses and the open ordinary-comparison clause. The unit route stays.

## Where the brief, the DAG or earlier work was wrong

The old sixth proof-step text still called moduleBalancing open after it was proved.
The update removes that stale wording and records the actual chain-localization
argument. The ordinary-comparison restatement in CompactSupportScalarLimitReduction
is proved by applying this item's open ordinary theorem; importing it would make a
circular proof, so it is not used.

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
