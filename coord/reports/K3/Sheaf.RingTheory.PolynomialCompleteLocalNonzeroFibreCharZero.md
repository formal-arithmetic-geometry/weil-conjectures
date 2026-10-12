## What changed

`Polynomial.completeLocalNonzeroFibreCharZero` eliminates a regular-base reduction and applies the regular-base formal-fibre theorem to the resulting ring. Its existing signature and docstring are unchanged. Two new modules state separate steps: the finite-subring transfer implication and regularity of the smaller fibre. Their imports contain the definitions used by their statements and the declarations needed by their documented proof plans. The target imports both new modules privately.

The second reader removed the unused private `finite_polynomial_extension` helper and its redundant imports. The polynomial finite-module argument is explained in the reduction's docstring. The reduction no longer publicly imports the unrelated complete-local-domain quotient reduction. The regular-base module imports the fibre definition directly rather than the geometric-regularity definition. Node statements, proof plans, dependencies, and verbatim Lean records were repaired.

## Proved and sorry left

Hole closed in the item: `Polynomial.completeLocalNonzeroFibreCharZero` (node `lem-weil-pbc-polynomial-complete-local-nonzero-fibre-char-zero`). There is no direct sorry remaining in the item's module.

Holes added, both still open:

- `Polynomial.completeLocalNonzeroFibreCharZero_reduction`: node `lem-weil-pbc-polynomial-complete-local-nonzero-fibre-char-zero-reduction`.
- `Polynomial.regularBase_formalFibre_isRegular`: node `lem-weil-pbc-polynomial-regular-base-formal-fibre`.

This is a decomposition: one original hole closed, two lower holes added, net minus one within this delivery. No theorem is claimed closed without sorryAx. The target's proof genuinely combines the conditional transfer with the separately stated regularity input; neither new theorem simply restates the target. No definitions, hollow definitions, or additional axioms are introduced.

All three modules compile without errors or warnings with lcompile.py. Scratch copies with `#print axioms` for all three declarations show only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`, as expected for this decomposition.

## No longer needed

Removed direct imports of the target, compared with the repository:

- `Mathlib.FieldTheory.PurelyInseparable.Basic`.
- `Sheaf.RingTheory.AdicCompletionNoetherian`.
- `Sheaf.RingTheory.CompleteLocalDomainFiniteOverRegular`.
- `Sheaf.RingTheory.CompletionRegularLocal`.
- `Sheaf.RingTheory.Derivation.CompletionAndLocalization`.
- `Sheaf.RingTheory.FormalFibreQuasiFiniteAscent`.
- `Sheaf.RingTheory.HypersurfaceDerivationRegular`.
- `Sheaf.RingTheory.RegularLocalLocalization`.
- `Sheaf.RingTheory.RegularRingSmoothAscent`.

All eleven old proof_deps are replaced as direct dependencies of the target by the two new nodes. Their disposition is:

- `lem-weil-pbc-complete-local-domain-finite-over-regular`, `lem-weil-pbc-formal-fibre-quasi-finite-ascent`, and `lem-weil-pbc-adic-completion-noetherian`: retained under the reduction node.
- `lem-weil-pbc-regular-local-localization`, `lem-weil-pbc-completion-regular-local`, `lem-weil-pbc-derivation-extends`, and `lem-weil-pbc-hypersurface-derivation-regular`: retained under the regular-base node.
- `lem-weil-pbc-regular-ring-smooth-ascent`: unnecessary for this route, because Mathlib's `Polynomial.isRegularLocalRing_localization_atPrime_of_comap_eq_maximalIdeal` supplies regularity of the polynomial local ring directly.
- `def-weil-pbc-localization-at-prime` and `def-weil-pbc-g-ring`: remain statement dependencies, not proof lemmas.
- `def-weil-pbc-finite-purely-inseparable-extension`: its notion is supplied by Mathlib through GRing and the reduction's proof import; it is not a separate proof lemma.

No whole-library module pruning is claimed: most removed direct imports are still dependencies of a split step, and other targets may reach the smooth-ascent module. No unit realization is removed.

## Where the brief, the DAG or earlier work was wrong

The first worker's target node still carried the original five-step plan after replacing its Lean proof by a two-step decomposition. Both new nodes had empty proof dependencies despite relying on substantial existing lemmas. Their prose statements omitted hypotheses, and the regular-base node incorrectly restricted its statement to nonzero primes although its Lean statement allows zero. These were repaired without changing an existing declaration's signature.

The reduction's earlier docstring did not explain characteristic-zero geometric regularity or why a nonzero prime has nonzero contraction under the finite polynomial extension. The second reader supplied those arguments. The redundant private finite-polynomial helper and unrelated public quotient-reduction import were removed.

The local literature source file is absent on this machine. The second reader read the official Stacks pages directly: https://stacks.math.columbia.edu/tag/07PV, https://stacks.math.columbia.edu/tag/07PU, https://stacks.math.columbia.edu/tag/07PE, and https://stacks.math.columbia.edu/tag/07PP. The nonzero fibre requires the hypersurface argument documented in the existing target, rather than treating a nonzero-prime fibre as just a localization of the completion.

## New nodes

`lem-weil-pbc-polynomial-complete-local-nonzero-fibre-char-zero-reduction` states only the existence and conditional transfer part of the argument. It does not assert regularity of the contracted fibre. Its proof plan uses the already stated finite regular subring, finite-map quasi-finiteness, Noetherian completion/fibre, and formal-fibre ascent declarations. The witness is used only in a proof of a proposition, never as data of a definition.

`lem-weil-pbc-polynomial-regular-base-formal-fibre` treats regularity of the smaller fibre, including the zero-prime localization case. The nonzero case uses polynomial localization regularity, completion regularity, localization, and the hypersurface derivation criterion. It asserts neither geometric regularity nor transfer to the original coefficient ring. No change record is needed: no existing statement, definition, or public import is changed.

## Second reading by K3

1. Compared every existing delivered module against the repository with diff. Only the original target module exists in the repository; its declaration signature and docstring are byte for byte unchanged. Its public imports are unchanged. The two other modules and nodes are new. No change records or unrelated adaptations are needed.
2. Compiled all three modules in import order using only lcompile.py, without errors or warnings. Checked each declaration with `#print axioms` in scratch copies: only the three allowed axioms and sorryAx. Exactly the two listed new public theorems have whole-proof sorry; there is no partial-proof sorry, no definition, and no forbidden trust mechanism. Verdict: a sound conditional decomposition, not a fully closed proof.
3. Read both new statements and their proof docstrings. Checked the regular-base zero-prime case, a characteristic-zero field coefficient ring, the nonzero irreducible-polynomial case, and finite-subring contraction. The reduction's nonzero contraction follows after localizing to a finite field extension and taking the nonzero polynomial norm. Characteristic zero makes purely inseparable residue-field extensions trivial. Neither split statement is a restatement of the target. New loogle, leanfinder, and grep searches plus rg of lean/ found no existing match; the positive-characteristic polynomial-fibre theorem and DVR generic-fibre theorem do not apply. Both statements are true steps of the argument; closing either in a few minutes would require substantial localization/tensor-product constructions, so both remain explicitly open.
4. Read the original dependency declarations and checked shorter routes. Mathlib already supplies polynomial-localization regularity, replacing smooth ascent in the regular-base plan. Removed the unused helper and redundant imports. Enumerated every old proof_dep above. Read dag/units/sk-thm-p1.json: neither the target nor either new node is a realization of its statement or steps; the split is below the unit level and changes none of the realized route. Verdict: route preserved and direct imports pruned.
5. Rewrote the target node's proof and proof_deps to the actual two-lemma application. New nodes now have complete hypothesis-bearing statements, matching verbatim Lean signatures, named proof dependencies with their union, source/proof_origin, search records, creation metadata, and the target's chapter and unit. Corrected the regular-base node's zero-prime coverage. Verdict: nodes agree with Lean and the open proof plans.

Changes by this second reader: removed the unused private helper and redundant imports; expanded the reduction proof docstring; repaired all three node proof records, new-node statements and Lean records, search evidence, hole accounting, and dependency dispositions. The target's proof was left intact.
