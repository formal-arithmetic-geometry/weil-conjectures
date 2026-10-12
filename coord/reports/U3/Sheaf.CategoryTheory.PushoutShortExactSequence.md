## What changed

Proved `CategoryTheory.pushout_short_exact_sequence` in
`Sheaf.CategoryTheory.PushoutShortExactSequence`, with its signature unchanged.
No imports changed and no declarations were added. Mathlib's
`Abelian.BiproductToPushoutIsCokernel.isColimitBiproductToPushout` gives the
cokernel presentation and uniqueness of cokernels gives the compatible isomorphism.
The projection is `pushout.desc 0 S.g`; the original cokernel universal property
proves directly that this projection is a cokernel. The monomorphism instance and
`ShortComplex.exact_of_g_is_cokernel` give short exactness. The two commuting
squares give the requested morphism of complexes.

Updated the item's DAG proof, proof dependencies, and proof origin to record this
route. All unit realization nodes remain unchanged: this item is below the unit's
realized statements and steps. Searches used LeanFinder, Loogle, launcher grep,
and local searches in Mathlib and both library roots.

## Proved and sorry left

Closed the one original hole: `CategoryTheory.pushout_short_exact_sequence`
(node `lem-weil-pbc-pushout-short-exact-sequence`). This is a full proof from
Mathlib, not a decomposition. Holes added: none. Sorries left: none.
Local single-file compilation passed without warnings. The delivery dry run
checks compilation on the server and the declaration's axioms as well.

## No longer needed

No imports were removed: both existing public Mathlib imports are needed by the
unchanged statement. The proof no longer needs the node
`lem-weil-pbc-pushout-cokernel-iso`, whose Mathlib declaration is
`CategoryTheory.Limits.isIso_cokernel_map_of_isPushout` in
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels`.
That module is not imported. All other existing proof dependencies still describe
facts used by the proof, supplied directly by Mathlib. No other nodes or modules
are pruned by this delivery; other users may still need the omitted node.

## Where the brief, the DAG or earlier work was wrong

No incorrect statements or definitions found. The planned Step 5 is longer than
necessary: checking the cokernel universal property directly avoids constructing
and inverting a cokernel comparison isomorphism. The existing documentation of
the planned proof was preserved; the DAG now records the implemented direct proof.

## Second reading by U3

1. Compared the only delivered Lean module with the repository using `diff`.
   Only the original theorem's proof body differs; the existing signature,
   definitions, documentation, module header, and public imports are byte for byte
   unchanged. No statement change or change record is needed. Verdict: pass.
2. Compiled the delivered file locally through `lcompile.py`: no errors or
   warnings. A scratch copy with `#print axioms
   CategoryTheory.pushout_short_exact_sequence` reports exactly `propext`,
   `Classical.choice`, and `Quot.sound`. The delivered module has no `sorry`,
   additional declaration, hollow definition, or forbidden proof escape.
   Read the cokernel isomorphism compatibility, projection factorization and
   uniqueness, mono/epi instances, exactness, and both morphism squares.
   Verdict: pass; one original hole closed and zero holes added.
3. There are no split-off statements or new nodes. Checked the argument also in
   the degenerate cases `u = 0`, `u = id`, and a zero short complex: the same
   universal-property factorizations apply without extra assumptions.
   Verdict: pass; no decomposition or restatement of the target.
4. Searched both library roots, the upstream source, and Mathlib with terms for
   pushouts and short exactness, and repeated launcher grep with
   `pushout.*ShortExact|ShortExact.*pushout` (zero hits). Read Mathlib's
   `isColimitBiproductToPushout`, the pushout mono instances, and
   `CokernelCofork.IsColimit.ofπ'`: the existing proof uses their direct route.
   Both public imports supply notions used in the unchanged signature and are
   necessary. The old proof-dependency set minus the new one is exactly
   `lem-weil-pbc-pushout-cokernel-iso`, already reported above. Read
   `dag/units/sk-thm-p1.json`; this lemma is below its realized statements and
   steps, and that unit's route is preserved. Verdict: pass.
5. Compared the delivered node with its repository version and read the Lean
   records / Mathlib matches of every old proof dependency. Only `proof`,
   `proof_deps`, and `proof_origin` changed. Step 5 matches the direct cokernel
   argument; the remaining dependencies match colimits, abelian structure,
   short exactness and pushout monicity actually used from Mathlib. Verdict:
   pass.

Second reading changed only this report, adding the independent checks and
verdicts. No Lean or DAG repair was needed. The original docstring describes the
longer planned Step 5, as the first reader's report already explains; the DAG
records the implemented proof.
