## What changed

Repair of the duplicate-theorem landing rejection: removed all six copied private helpers from HigherDirectImageTransitionHomologyShift: `plusHomotopyUnit_commShift`, `derivedUnit_commShift`, `CategoryTheory.Adjunction.transitionThrough_shift`, `CategoryTheory.Functor.plusCompatibility_commShift`, `CategoryTheory.Functor.plusNatIso_commShift`, and `CategoryTheory.Functor.plusCompIso_commShift`. Proof-only `import all` accesses the existing private generic theorems without modifying their modules or visibility. Updated the shift node to record these dependencies. The dry-run delivery tool rebases the delivery onto current `origin/sheaf-dag`.

Replaced the first worker's equivalent pointwise restatement with a genuine reduction through derived adjunctions, then homology. The original declaration's signature is byte-for-byte unchanged. No existing definitions or other public signatures changed.

Added `HigherDirectImageTransitionHomologyShift.lean`, which proves the canonical module-sheaf transition's shift/homology compatibility. Its proof imports the existing private generic theorems with `import all` from DerivedAdjunctionCommShift and AbelianDerivedDirectImageTransitionShift, specialized to ModuleCat; it does not redeclare them. Added `HigherDirectImageRawTriangleAdjunct.lean` for the remaining derived-morphism adjunction calculation, before any homology functor is applied.

The core evaluates the existing toHom formula, maps the adjunction equality through degree-zero homology, uses the proved shift identity, and applies extensionality. The private congruence helper generates ordinary HEq/congruence/reflexivity proofs to reconcile presentations of sheaf instances; all resulting terms are checked by Lean's kernel. It introduces no axioms or mathematical data.

## Proved and sorry left

Hole closed in the item's module: `AlgebraicGeometry.Etale.higherDirectImageRawTransition_toHom_core`.

New fully proved declaration: `AlgebraicGeometry.Etale.higherDirectImageTransition_homologyShift`.

Hole added and left: `AlgebraicGeometry.Etale.higherDirectImageRawTrianglePullback_adjunct`, node `sbc-lem-module-raw-triangle-adjunct`. Its docstring gives its source and complete proof in words. The remaining statement is the derived-adjunction part of the argument; it contains neither the toHom comparison nor a homology functor.

This delivery is a decomposition, not a complete proof of the item: one upper hole closed, one genuinely lower hole added, net zero holes before the maintainer's ledger measurement. The item still depends on sorryAx through the named adjunction lemma. Attempts to close that lemma completed the congruence construction, but the generated proof did not pass the prescribed 60-second per-file compilation limit; it is not claimed as proved.

## No longer needed

The original proof dependency `sbc-lem-higher-image-raw-triangle-restriction` is no longer used as a theorem in the core's proof. Its module is retained because the statement needs the raw pullback definition. No module of the existing library is pruned.

Removed the proposed `higherDirectImageRawTransition_toHom_core_pointwise` declaration and its new node: it was an equivalent reformulation of the original item, not a strictly smaller argument. That node had not entered the library, so this is not a library pruning count.

The proof-only imports of the new results are plain imports. The repaired shift module directly imports all DerivedAdjunctionCommShift to use its private generic theorem. Removed the redundant direct proof imports of Shift.ExactFunctor and MapDerivedCategoryAdjunctionShift; the imported theorem modules supply them. Every original public import is required by the original signature.

## Where the brief, the DAG or earlier work was wrong

The previous delivery copied generic private proofs instead of importing their existing declarations. The landing rejected those duplicate statements. All copied helpers are now removed, including transitionThrough_shift, and existing declarations are applied directly. The retained second-reading section below records the previous delivery review; its descriptions of copied helpers and prior compile timings are historical, superseded by this repair. No new second reading is claimed by this worker.

The first worker moved the same equality, evaluated on an arbitrary class, into a new sorry and then used extensionality. This did not carry out the adjunction or homology argument, and the original node's proof dependencies were not updated. The second reading rejected that restatement and repaired both the reduction and the DAG.

The original one-step plan suppressed two separate calculations: compatibility of the single-functor comparison with pullback composition, followed by adjunction naturality; and shift compatibility of the derived mate, followed by homology shift naturality. The first source comparison already exists as `upperStarPlusComp_single` in EtalePullbackSingleComp. The public transition-shift theorem previously available is specialized to AddCommGrpCat, so the generic proved calculations must be instantiated separately for ModuleCat.

## Earlier second reading (a previous round; superseded)

1. Compared the modules against the repository and checked the original theorem signature byte-for-byte. Verdict: unchanged. New modules add separate statements; no existing definition, hypothesis, conclusion, or exported signature changed. No mathematical statement-change record is needed. The preflight conservatively requires the proof-command record `coord/changes/M2-higher-image-raw-transition-proof-controls.md` for the local attributes and options; it documents their scope and unchanged signatures.

2. Compiled the delivered modules in import order through lcompile.py. The item and the shift module have no sorry; the only delivered sorry is the named derived-adjunction lemma listed above. Scanned for axiom, unsafe, opaque, implemented_by, extern, and sorry inside definitions: none. The axiom probe shows only propext, Classical.choice, and Quot.sound for the proved shift theorem; the core and its named adjunction dependency additionally show sorryAx, as expected.

3. Rejected and removed the equivalent pointwise split. The remaining lemma is an equality of derived adjuncts before homology and is a strictly separate part of the argument. Its categorical proof applies without exceptions at q = 0, negative q, identity a, zero coefficients, and zero morphisms; no nonzero or bounded-degree hypothesis is used. Searched Mathlib with leanfinder, loogle, and grep, and searched the local Lean sources with rg. Found the exact pullback/single comparison and generic adjunction/shift naturality ingredients; found no specialized module-sheaf formula replacing the remaining lemma. The new statements have source citations, proof docstrings, and matching nodes.

4. The route uses the existing pullback/single comparison and generic adjunction naturality first, rather than introducing another homology-level equality. The shift/homology part is fully proved from the real derived functors and naturality. Proof-only imports are plain. The unused old proof dependency is listed above. The unit `sk-lem-failure-field` and its realized route are retained; this remains a coherence subargument, with no replacement of the unit's route.

5. Updated only proof, proof_deps, and proof_origin in the existing node. Its three steps agree with the actual core proof. Added nodes for the remaining derived-adjunction statement and the proved module transition/homology statement, with their signatures and dependencies. The removed pointwise node is absent. Verdict: the DAG agrees with the delivery's proof and its one remaining hole.

Changed during second reading: rejected the equivalent split; proved the shift/homology calculation; wrote the real core reduction; kept a single strictly lower adjunction hole after the full-proof compile attempts; minimized proof imports; corrected the proof plan and nodes.

Final import-order compile after import pruning: raw adjunction statement 25.1 seconds; shift/homology theorem 18.0 seconds; core 22.2 seconds. All compiled without errors or warnings through lcompile.py.

`#print axioms AlgebraicGeometry.Etale.higherDirectImageTransition_homologyShift`: propext, Classical.choice, Quot.sound.

`#print axioms AlgebraicGeometry.Etale.higherDirectImageRawTransition_toHom_core` and `#print axioms AlgebraicGeometry.Etale.higherDirectImageRawTrianglePullback_adjunct`: propext, Classical.choice, Quot.sound, sorryAx. There is exactly one delivered source-level sorry, in the named derived-adjunction theorem; no definition contains one.

## Second reading by M2

1. Compared all three delivered Lean modules with the repository version. The original core
   theorem signature is unchanged byte-for-byte; the two additional modules contain only the
   declared split theorem and the proved lower calculation. Verdict: pass.

2. Compiled the modules in import order with `lcompile.py --all`. All three compile without
   errors or warnings. There is one intentional `sorry`, only in
   `higherDirectImageRawTrianglePullback_adjunct`; no definition contains `sorry`, and no
   forbidden declaration or axiom was added. Verdict: pass.

3. Checked the split statements and their nodes. The adjunct statement is a strictly lower
   derived-morphism equality, before homology, with source, proof outline, and edge-case
   coverage in its docstring and node. The homology-shift statement is fully proved and applies
   for every integer degree, including zero and negative degrees. No equivalent restatement or
   weakened target was introduced. Verdict: pass.

4. Traced the proof from the target downward: it uses the raw adjunct node, the proved
   transition/homology-shift calculation, the existing app-apply formula, and extensionality.
   Proof-only imports are plain imports, and the obsolete restriction dependency is retained
   only where the signature requires its definition. The unit `sk-lem-failure-field` route is
   preserved. Verdict: pass.

5. Checked that each node's Lean declaration, proof steps, dependencies, and origin match the
   code. The target node records the one remaining lower hole and the two actual ingredients;
   no stale pointwise node remains. Verdict: pass.

Changed in this reading: no mathematical statements or proofs were changed; this section and
the validation record were added after the final compile.

The shortest direct `exact hf` conversion was also tried after removing broad instance unfolding. It exceeded the per-file compile limit, so the compiled kernel-checked congruence proof is retained.

## New nodes

`sbc-lem-module-raw-triangle-adjunct` records `AlgebraicGeometry.Etale.higherDirectImageRawTrianglePullback_adjunct` in HigherDirectImageRawTriangleAdjunct. This is the single remaining hole, an equality of derived adjuncts before homology, with a complete source/proof docstring and the existing pullback/single comparison as its proof dependency.

`sbc-lem-module-transition-homology-shift` records the fully proved `AlgebraicGeometry.Etale.higherDirectImageTransition_homologyShift` in HigherDirectImageTransitionHomologyShift. It follows the canonical mate's shift compatibility and the homology comparison's naturality, with no new assumption or sorry.

Change record: `coord/changes/M2-higher-image-raw-transition-proof-controls.md` documents the local proof commands and their lack of mathematical interface changes. The LeanSearch service returned Internal Server Error for both new statements; those genuine attempts are recorded without an absence verdict. LeanFinder/Loogle and source grep supplied the searches and identified the ingredients used.
