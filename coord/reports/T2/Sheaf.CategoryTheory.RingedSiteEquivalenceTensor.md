## What changed

Filled `SheafOfModules.pushforward_equivalence_tensor_iso` in
`Sheaf.CategoryTheory.RingedSiteEquivalenceTensor`. Added the proof-only import
`Sheaf.CategoryTheory.RingedCocontinuousMonoidal`. The inverse equivalence functor
is cover preserving by continuity; the equivalence adjunction therefore makes
the forward functor cocontinuous. Forgetting commutativity maps the given
coefficient isomorphism to the exact ring-sheaf comparison required by the
already proved `SheafOfModules.ringed_cocontinuous_monoidal`. Its strong monoidal
structure supplies `Functor.Monoidal.μNatIso`; taking the inverse proves the
requested natural isomorphism. The local monoidal structures agree with the
original statement, since they use the same localization construction and their
monoidality witnesses are propositions.

Only this module and its own DAG node are changed. The statement, universes,
public imports, and existing docstring are preserved. There are no changes to
shared definitions, consumers, or unit routes. No direct-importer adaptation is
necessary for the proof-only import. The corresponding DAG proof now records
this reuse of an existing stronger theorem.

Read the Stacks source `sites-modules.tex`, section-tensor-product,
lemma-sheafification-tensor and lemma-tensor-product-pullback, and the current
blueprint unit `sec-six-functors-basics/sk-prop-sf-cbc/_section.md`.
LeanFinder found the sheaf-equivalence and general sheaf-monoidal APIs; Loogle
for `"pushforward", "tensor"` returned no hits. Local searches located the
already proved ringed cocontinuous theorem, which avoids reconstructing the
presheaf tensor comparison and sheafification transport. Import-direction check
allows the new proof import.

## Proved and sorry left

Closed the one original hole:
`SheafOfModules.pushforward_equivalence_tensor_iso`
(node `lem-sf-ringed-site-equivalence-tensor`).

Holes closed: 1. Holes added: 0. Holes left in this module: 0.
No split-off statements or modules.

## No longer needed

No imports were removed, and no whole module is claimed pruned.
The direct proof dependencies `def-pur-presheaf-tensor-product`,
`def-pur-sheaf-tensor-product`, and
`lem-weil-pbc-site-equivalence-sheaf-transport` are replaced in this node's
`proof_deps` by `lem-sfb-ringed-cocontinuous-monoidal`: their sectionwise tensor
and sheafification arguments have already been assembled in that stronger
theorem. The tensor definitions remain statement dependencies, and tensor
construction dependencies of the reused theorem remain needed indirectly.
The separate `Equivalence.sheafCongr` transport argument is unnecessary here;
the equivalence is used only for its adjunction. No declarations are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The DAG planned a valid construction but missed
an existing theorem giving the stronger strong-monoidal result for continuous,
cocontinuous functors with invertible coefficients. This delivery specializes
that theorem rather than creating another layer of unfinished lemmas. Empty
sites and zero rings are still included: no additional hypotheses are used.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
