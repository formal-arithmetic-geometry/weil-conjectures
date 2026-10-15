## What changed

Proved `CategoryTheory.horizontal_comparison_lift` in
`lean/Sheaf/CategoryTheory/HorizontalComparisonLift.lean`, preserving its complete signature
and all existing public imports. Added the proof-only import
`WeilConjectures.Mathlib.CategoryTheory.Abelian.Injective.Resolution` to reuse
its existing augmentation exactness and monicity lemmas.

The proved private helper `CategoryTheory.lift_from_exact_augmentation` uses the existing
`CochainComplex.exact₀_of_quasiIso_single₀`, `exact_succ_of_quasiIso_single₀`, and
`mono_f_zero_of_quasiIso_single₀` declarations, then extends
a closed augmentation map recursively using `Injective.factorThru`,
`ShortComplex.Exact.descToInjective`, and `CochainComplex.mkHom`. This is the specialized
injective-resolution descent construction, without assuming the source terms injective.
The main proof applies it columnwise and performs the residual augmentation calculation,
including the equality transport at `(p + 1) - 1 = p`.

Updated the existing node's `proof`, `proof_deps`, and `proof_origin` to describe this direct
construction. A local unused-variable linter option preserves the theorem's original
first-quadrant and horizontal-row binders, which this stronger argument does not use.

## Proved and sorry left

Closed: `CategoryTheory.horizontal_comparison_lift`
(node `lem-sp-ce-horizontal-lift`), the module's only original hole.

Added holes: none. Remaining holes: none. The private helper is fully proved.
This is a proof, not a decomposition. Single-file compilation passes without warnings.
The required delivery dry run checks the compiled declarations and their axioms.

## No longer needed

No original imports were removed: the three public Mathlib imports provide the existing
statement and its definitions. No Sheaf proof modules are needed. The added WeilConjectures proof import supplies
proved exactness lemmas; its source has no holes and only imports Mathlib.

Removed the proof edge to `lem-weil-pbc-lift-along-injective-quasi-iso`: its special case
is now constructed and proved inside this module. That node is a Mathlib leaf and has no
Sheaf module to remove. It may still be needed by its other parents; no global withdrawal
is proposed. No other planned dependency nodes or modules are bypassed.

The first-quadrant hypotheses, horizontal cycles/boundaries/homology quasi-isomorphisms,
and horizontal-row injectivity hypotheses are unnecessary for this conclusion; their
binders remain exactly as before. Natural-number vertical indexing is enough for the
recursion. In particular the negative horizontal indices need no separate case.

## Where the brief, the DAG or earlier work was wrong

The statement is true unchanged. The old plan invokes an integer-indexed bounded-below
model-category lifting theorem. Its claimed specialization is mathematically valid, but
extension by zero and the comparison with natural-indexed columns add avoidable glue.
The direct exact-augmentation recursion proves precisely the needed special case and
eliminates that proof dependency. The node's unit record has no realized steps involving
this dependency, so no fixed unit route is bypassed.

No source error, statement change, definition change, forced adaptation, or new node.

## Second reading by R4

1. **Unchanged interface — pass.** Diffed the complete delivered module against the
   shared repository version. The full signature of
   `CategoryTheory.horizontal_comparison_lift` is byte-for-byte identical, including
   every first-quadrant, quasi-isomorphism, row and injectivity hypothesis, and all
   three existential conclusions. Existing docstrings and public imports are unchanged.
   No definition changed, no other module was adapted, and no change record is needed.

2. **Proof and axioms — pass.** Compiled the delivered module through `lcompile.py`
   without errors or warnings. A scratch copy containing `#print axioms` for the main
   theorem and private helper reports exactly `propext`, `Classical.choice`, and
   `Quot.sound` for each. Scanned for `sorry`, `axiom`, `unsafe`, `opaque`,
   `implemented_by`, `extern`, and explicit `sorryAx`: none occur. The choices of
   injective extensions and column maps depend entirely on proved facts.

3. **Intermediate statements — repaired, then pass.** No statement was split off and
   no hole was added. Checked the helper at degree zero and the first recursive step:
   monicity permits the initial extension, the closedness hypothesis permits descent
   through the first differential, and `d ≫ d = 0` permits each succeeding descent.
   The zero source and zero target cases impose no extra assumption. Negative horizontal
   indices use the same natural-degree recursion; no negative vertical index is used.
   Independent LeanFinder and Loogle searches through `msearch.py` found no direct
   general-purpose natural-indexed lift. Local `rg` searches in Mathlib, upstream,
   and `lean/Sheaf` found the existing exactness and kernel proofs in
   `WeilConjectures.Mathlib.CategoryTheory.Abelian.Injective.Resolution`; replaced
   their duplication with those declarations and the existing monicity instance.
   `InjectiveResolution.descOfQuasiIso` is not directly applicable: its target is an
   injective resolution, while this theorem does not assume the target column
   augmentation is a quasi-isomorphism. The helper retains only the needed recursion.

4. **Route and pruning — pass.** Read the proofs of
   [Stacks Tag 013P(2)](https://stacks.math.columbia.edu/tag/013P) and
   [Tag 015I](https://stacks.math.columbia.edu/tag/015I), the old node proof, and the
   unit record `dag/units/sk-prop-av-pqf-finite.json`. The former supplies successive
   injective extension; the latter supplies the Cartan--Eilenberg setting. The main
   proof lifts the closed augmentation columnwise, then proves the residual vanishes
   using augmentation naturality and `hhom`, including the `(p + 1) - 1 = p` transport.
   All three original public imports serve the statement (bicomplexes, the abelian
   complex instance, and single-degree/quasi-isomorphism and injective interfaces).
   The added upstream import is plain `import` because only the proof needs it.
   The old `proof_deps` had exactly one edge, to
   `lem-weil-pbc-lift-along-injective-quasi-iso`; it is removed and fully listed above.
   That leaf has no Sheaf module to prune. The unit's `realized` statement and step
   arrays are empty; this edge realizes no fixed unit step. No unit route changed.

5. **DAG agreement — repaired, then pass.** Compared the node JSONs: only `proof`,
   `proof_deps`, and `proof_origin` change. The three proof steps now describe the
   existing exactness lemmas, the actual injective-extension recursion, and the
   residual augmentation calculation. Their `uses` union and `proof_deps` are empty;
   no unproved DAG statement is used. No new node or statement change is present.

Second-reading changes: removed the duplicated kernel and exactness arguments in
favor of already proved upstream lemmas through a proof-only import, updated the
node and report to match, and checked line widths. The column recursion and main
residual proof were retained. Closed one original hole; added zero; no modules pruned.
