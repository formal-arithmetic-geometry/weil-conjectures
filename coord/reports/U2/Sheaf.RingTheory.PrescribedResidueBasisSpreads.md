## What changed

Proved `Module.FinitePresentation.exists_basis_away_of_prescribed_residue_basis`
in `lean/Sheaf/RingTheory/PrescribedResidueBasisSpreads.lean`, with its signature,
visibility, and existing docstrings unchanged. Added only the proof import
`Mathlib.RingTheory.LocalRing.Module`; existing public imports stay as they were.

The proof implements all five steps of the existing node
`lem-weil-pbc-prescribed-residue-basis-spreads`:

1. Define the prescribed linear combination on `Fin r →₀ A` and its localization,
   using `Finsupp.mapRange.linearMap` to realize the localization of the domain.
2. Identify the two residue tensor products using `LocalizedModule.equivTensorProduct`,
   `LinearEquiv.baseChange`, and `TensorProduct.AlgebraTensorModule.cancelBaseChange`.
   Check the prescribed pure tensors explicitly, transport the residue basis, and apply
   `IsLocalRing.span_eq_top_of_tmul_eq_basis` (Nakayama).
3. Compose the resulting surjection with the given local basis representation.
   Apply `OrzechProperty.bijective_of_surjective_endomorphism` and recover injectivity
   of the original localized map.
4. Apply `Module.FinitePresentation.exists_notMem_bijective` to that map.
5. Transfer the bijectivity to the localized Finsupp domain, build a basis from the
   inverse linear equivalence, and evaluate each standard vector using
   `IsLocalizedModule.map_linearCombination`.

This preserves the planned route and every existing proof dependency; no node edit
is needed. The node is not among `dag/units/sk-thm-p1.json`'s realized unit statements
or steps, and no unit route is bypassed.

Sources checked: [Stacks 0GWM](https://stacks.math.columbia.edu/tag/0GWM),
[00DV, part (8)](https://stacks.math.columbia.edu/tag/00DV), and
[05G8](https://stacks.math.columbia.edu/tag/05G8).
The local checkout has no `literature/stacks-project/algebra.tex`, so these source
pages were read directly. Mathlib's `Smooth/StandardSmoothOfFree.lean` supplies a
useful model for spreading a prescribed linear combination, and
`LocalRing/Module.lean` supplies the residue-tensor identification pattern.

Searches used the prescribed msearch launcher (LeanFinder, Loogle, and grep), plus
`rg` in Mathlib and both library roots. No direct prescribed-basis spreading theorem
was found. All lemmas used in the proof are already proved in Mathlib.

Validation: the entire module compiles with the prescribed `lcompile.py`, without
warnings. The delivery dry run also checks the axioms of its declarations.
The proof works uniformly for `r = 0`; no nonempty-index assumption is introduced.
It allows different ring/module universes and makes no domain or Noetherian assumption.
The chosen bases come from the theorem's hypotheses, not an unproved existence lemma.

## Proved and sorry left

Closed the one original hole:
`Module.FinitePresentation.exists_basis_away_of_prescribed_residue_basis`
(node `lem-weil-pbc-prescribed-residue-basis-spreads`).

Sorries left in the item: none. New holes: none. Split-off statements: none.
This is a proof, not a decomposition, and uses only proved Mathlib dependencies.

## No longer needed

None. No imports were removed, and no planned dependency nodes or modules were
pruned. All ten existing `proof_deps` remain used as the mathematical notions and
results of the five-step proof. No Sheaf or WeilConjectures proof imports are needed:
the planned dependency results are all available in Mathlib.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error was found. The original node's proof plan is
fully realizable from existing Mathlib declarations, including the prescribed-image
condition. The source file cited in the node is absent from this machine; the cited
Stacks pages were read online instead. No statement, definition, or public import
was changed, and no forced adaptation is required.

## Second reading by U2

1. **Interface and statements.** Compared the delivered module with the repository version.
   The theorem signature, visibility, declaration name, and docstring are byte-for-byte
   unchanged; the only interface change is the plain proof import of
   `Mathlib.RingTheory.LocalRing.Module`. Verdict: pass.

2. **Proof and axioms.** Compiled the module with `lcompile.py`; it succeeds without
   errors or warnings. The module has no `sorry`, `axiom`, `unsafe`, `opaque`,
   `implemented_by`, or `extern`, and delivery preflight checks declaration axioms.
   Verdict: pass.

3. **Statements and dependencies.** Searched Mathlib and the repository for an existing
   prescribed-basis spreading theorem. None duplicates this declaration. The proof uses
   the ten dependencies listed by the node, and no split-off statements or new nodes are
   introduced. The argument handles the edge case `r = 0` without adding hypotheses.
   Verdict: pass.

4. **Route and pruning.** The proof follows the node's five planned steps: residue tensor
   identification, Nakayama generation, bijectivity at the prime, spreading bijectivity,
   and construction of the prescribed basis. No planned dependency is bypassed and no
   import or module can be pruned. Verdict: pass.

5. **DAG agreement.** The theorem declaration and proof uses agree with the existing node,
   whose unit is `sk-thm-p1`; that unit's realized route is unchanged. No node metadata
   needs editing. Verdict: pass.

I changed only this report by adding the required audit section. No Lean source, node,
statement, definition, or proof was changed during second reading.
