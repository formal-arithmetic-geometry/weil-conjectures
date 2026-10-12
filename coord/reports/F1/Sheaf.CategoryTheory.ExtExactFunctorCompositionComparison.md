## What changed

Repair of the return at head `521cd6155`: the independent reviewer passed the
proof, but landing timed out waiting for the maintainer's merge lock. This repair
retains the accepted Lean proof and rebases the delivery through deliver3.py onto
the current server `sheaf-dag`, with fresh local compilation, axiom audit, server
compilation and preflight. No push is made by this worker; the second reader
performs the delivery.

Proved `CategoryTheory.Abelian.Ext.exactFunctorCompositionComparison` without changing
its signature or existing docstrings. Added the proof-only import
`WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor` and a proved
private helper expanding the single-complex comparison. The proof uses the existing
library's derived natural-isomorphism and composition comparisons, establishes
compatibility on single complexes degreewise, and applies shifted naturality with
endpoint cancellation. Updated the existing node's proof and proof origin to record
these concrete steps. No definitions or statements changed; no change record is needed.

## Proved and sorry left

`CategoryTheory.Abelian.Ext.exactFunctorCompositionComparison`: the sole original
sorry is closed. No sorry remains in the item, and no new sorry or node was added.
The private helper `singleComparison_hom` is also proved. Local compilation is clean.
The delivery dry run performs the axiom audit and the server compilation.

The proof covers arbitrary n, including zero; it never requires n to be positive.
For identity functors and the reflexive comparison it reduces to the identity square;
for a natural automorphism it retains both endpoint components. Zero classes and
zero objects are allowed. The degreewise single-complex proof handles separately
the supported degree zero and every other degree. No enough-injectives assumption
or resolution is introduced.

## No longer needed

None. No original imports or proof-dependency nodes were removed. The original
three dependencies remain: `lem-weil-pbc-exact-functor-derived-factorization`,
`def-weil-abstract-derived-category`, and `def-pc-ext`. All are existing Mathlib
interfaces used by the proof. The new proof-only import supplies the comparison
isomorphisms and their shift compatibility. No realized unit statement or step is
bypassed, and no extra resolution theory is imported.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan was valid. The pinned Mathlib lacks the newer
`Ext.comp_mapExactFunctor` and `Ext.mapExactFunctor_comp_mk₀_natTransApp` found by
the live search index. The existing WeilConjectures derived-category comparison
API suffices instead. An earlier exploratory proof from K1's scratchpad unfolded
all comparisons simultaneously and did not complete. This proof instead isolates
the single-complex comparison expansion and uses the existing factorization
lemmas, compiling within seconds. Searches used leanfinder, loogle, grep, and local
rg; their results are recorded in searches.jsonl. Import-direction validation passes.


## Earlier second reading (a previous round; superseded)

1. **Unchanged public interface: PASS.** Read the entire delivered module and compared
   it with the repository version using diff. The existing theorem signature is
   byte-for-byte identical (also checked by extracting the text before `:= by`).
   Its docstring is unchanged. The only additions are a private proved lemma and
   a plain, proof-only import. There is no definition change, target change, or
   change record. The node diff changes only `proof` and `proof_origin`.

2. **Kernel proof: PASS.** Compiled the file locally through lcompile.py, cleanly.
   Compiled a scratch copy with explicit `#print axioms` for
   `CategoryTheory.Abelian.Ext.exactFunctorCompositionComparison` and
   `singleComparison_hom`: both report exactly propext, Classical.choice and
   Quot.sound. Scanned the delivered Lean for sorry and forbidden declarations or
   kernel-check bypasses: none. The transparency option affects elaboration only.
   The standard derived-category choices are local proof instances, not extra
   public hypotheses. All Lean lines meet the 100-character limit.

3. **Split statements and small cases: PASS.** There are no split-off statements,
   new public statements, or new nodes. The private helper expands the existing
   canonical single-complex isomorphism; it does not restate the target. Read the
   degreewise arguments `hm` and `hn`: at i = 0 the first reduces to identities,
   the second retains e.hom.app A, and at i != 0 the single complexes are zero.
   The final shifted-naturality argument imposes no positivity condition on n.
   At n = 0 the target is the naturality square for ordinary morphisms; identity
   functors with reflexive e give the identity square, and a nontrivial e retains
   components at both X and Y. Zero classes and zero objects are not excluded.

4. **Shortest route, imports and unit: PASS.** Independently searched with
   leanfinder (`transport of Ext along naturally isomorphic exact functors and
   successive functor images`), loogle (`"mapDerivedCategorySingleFunctor"`),
   grep (`mapExactFunctor.*[Cc]omp|[Nn]at.*mapExactFunctor`), and local rg in
   lean/Sheaf, lean/WeilConjectures and pinned Mathlib. The online single-comparison
   hom-app and composite-compatibility lemmas are absent from pinned Mathlib;
   its available factor-inverse lemma does not supply the composite/natural-iso
   square. No existing Ext composition comparison was found beyond this item.
   Read the imported shift-comparison instances and the upstream localization
   factorization lemmas: these are proved and used directly. The public Mathlib
   import supplies the signature's Ext interface; the plain upstream import
   supplies both comparison isomorphisms and their CommShift instances. Neither
   import is unused. All three old proof dependencies are used, so `No longer
   needed: None` is complete. Read dag/units/sk-thm-p1.json's realized statement
   and every realized step: this auxiliary node is not one of those unit nodes,
   and its same exact-functor route bypasses none of them.

5. **DAG and Lean agreement: PASS.** Read the item's node and the Mathlib matches
   of lem-weil-pbc-exact-functor-derived-factorization,
   def-weil-abstract-derived-category and def-pc-ext. They supply the exact-functor
   localization factorization, derived localization and shifted-Hom Ext model
   used by the code. The revised first step describes `hc`, with the two
   localization factorization equations and degreewise equalities. The revised
   second step describes `hi`, cancellation, ShiftedHom.map_naturality and the
   final shift-isomorphism naturality rewrite. proof_deps is still precisely
   their cited union, and proof_origin records this argument. The node's Lean
   signature matches the unchanged declaration. No new-node fields are needed.

**Changes by second reader:** Added this independent review and recorded fresh
searches in searches.jsonl. No Lean or DAG repair was necessary; retained the
completed proof rather than rewriting it. Dry run and delivery follow below.

## Earlier second reading (a previous round; superseded)

1. **Public interface: PASS.** Independently read the whole delivered file and its
   diff against the repository. Extracted the existing theorem signature and
   checked byte-for-byte equality. The existing docstring, definitions and target
   statements are unchanged. The additions are one private proved helper and one
   plain proof-only import. The node diff changes only proof and proof_origin;
   no change record is required.
2. **Kernel proof: PASS.** Fresh lcompile.py compilation passed without warnings.
   Verified that scratchpad/AxiomCheck.lean contains the identical delivered file
   before its audit commands, and compiled it afresh. Both the public theorem and
   private helper depend exactly on propext, Classical.choice and Quot.sound.
   Checked for sorry, axiom, unsafe, opaque, implemented_by, extern and sorryAx:
   none occur. All lines meet the 100-character limit.
3. **Auxiliary statements and edge cases: PASS.** No statement is split off and
   no new public statement or node is added. singleComparison_hom is a proved
   expansion of an existing isomorphism, not a restatement of the item. Read hm
   and hn degreewise: degree zero gives identities for the composite comparison
   and e.hom.app A for the natural comparison; other degrees are zero. The final
   naturality proof applies to every n, including zero, and admits zero objects,
   zero classes, identity functors and nontrivial natural automorphisms without
   discarding either endpoint component.
4. **Route and pruning: PASS.** Repeated searches with a fresh leanfinder query
   about transport through composite exact functors, loogle for mapExactFunctor,
   grep for single-complex and naturality comparisons, and local rg on Sheaf,
   upstream and pinned Mathlib. Newer online comp_mapExactFunctor and
   mapExactFunctor_comp_mk₀_natTransApp are absent in the pinned source. Its
   factor-inverse comparison lemmas do not provide the required composition
   square. The retained proof directly uses the proved upstream localization
   comparison API and its shift instances. The public import supplies Ext in the
   signature; the plain import supplies the comparison maps and CommShift
   instances. Neither is unused. Read sk-thm-p1.json's statement and realized
   steps: this auxiliary node realizes none of them and bypasses none. All three
   old proof dependencies remain used; No longer needed: None is complete.
5. **DAG: PASS.** Read the item and the three dependency records with their
   Mathlib matches. The revised first step follows hc, the factorization equations
   and the degreewise checks. The second follows inverse cancellation hi and
   ShiftedHom.map_naturality with the final shift-naturality rewrite. proof_deps
   is exactly the union of the steps' uses; proof_origin describes this argument.
   The node's recorded Lean statement agrees with the unchanged theorem.

**Changes by this second reader:** Added this fresh independent review and fresh
search records in searches.jsonl. No Lean or DAG repair was needed. One of one
original sorry is closed, zero statements split off, and nothing pruned.

## Second reading by F1

1. **Unchanged public interface: PASS.** Compared the delivered module with the repository version. The theorem signature and existing docstring are byte-for-byte unchanged; only a proof-only import, a private helper, and the theorem proof were added. The node changes only proof text and proof origin, with no statement or definition change.

2. **Kernel proof: PASS.** Compiled the delivered module with `lcompile.py`; it is clean. The existing scratch axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound` for the public theorem and helper. Scans found no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or `sorryAx`.

3. **Split statements and edge cases: PASS.** No public statement or node was split off. The private `singleComparison_hom` lemma expands an existing comparison and is not a restatement of the target. The degreewise checks cover degree zero and nonzero degrees, and the final argument applies for every natural `n`, including zero, with arbitrary zero objects and natural isomorphism components.

4. **Shortest route, imports, and unit: PASS.** The proof uses the existing derived-category comparison and localization factorization API, with the new plain import needed only by the proof. Searches recorded in `searches.jsonl` found no shorter applicable theorem in the pinned Mathlib or library. All original proof dependencies remain used, so no pruning is needed. The unit statement and realized route are preserved.

5. **DAG and Lean agreement: PASS.** The node's recorded proof steps now match the concrete Lean route through `mapDerivedCategoryNatIso`, `mapDerivedCategoryCompIso`, factorization equations, degreewise single-complex equalities, cancellation, and shifted naturality. Its proof dependencies are exactly those used by the proof, and the recorded Lean statement matches the unchanged declaration.

**Changes by second reader:** Added this independent review only. No Lean, DAG, or statement repair was necessary.
