## What changed
Added two intermediate theorems splitting the ambient coproduct construction and the quasi-coherent closure argument. The target theorem now combines these with Mathlib's full-subcategory colimit instance.

## Proved and sorry left
`AlgebraicGeometry.derivedQCohDirectSums` is proved. The intermediate declarations `derivedAmbientHasCoproducts` and `schemeDerivedQCohClosedUnderCoproducts` retain `sorry`, with their proof obligations documented in their docstrings and DAG nodes.

## No longer needed
Removed the target's direct proof imports of `Sheaf.AlgebraicGeometry.DerivedAmbientDirectSums`, `Sheaf.AlgebraicGeometry.Modules.QuasicoherentBinarySum`, and `Sheaf.AlgebraicGeometry.QuasiCoherentModuleColimitAffineSections`; these remain dependencies of the split obligations in the auxiliary module. No node or module is globally pruned; the public Products import is retained.

## Where the brief, the DAG or earlier work was wrong
The direct categorical construction is too large to inline in the target within this item; it is correctly represented by the two strict intermediate statements.

## New nodes
`lem-pc-derived-ambient-has-coproducts`; `lem-pc-derived-qcoh-closed-coproducts`.

## Second reading by S1

1. Compared the delivered target module with the repository version. The theorem
   signature and all existing declarations are unchanged byte for byte; only the
   proof and imports changed, and the new auxiliary module is explicitly delivered.
   Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`. There are no errors,
   forbidden declarations, or unlisted `sorry`s; the two auxiliary theorem sorries
   are named and documented in the report and have matching DAG nodes. The target
   proof assembles the two documented obligations; it still depends on sorryAx. Verdict: pass.
3. Checked both split-off statements against the imported definitions and searched
   the repository for duplicate declarations. They are genuine intermediate
   reductions, with the ambient coproduct statement and the closure statement each
   a distinct proper part of the mathematical argument, rather than the target restated. Verdict: pass.
4. Checked the proof route from the target downward. It uses the two split-off
   results and the full-subcategory colimit instance; the removed direct imports are
   retained privately in the auxiliary module for its split obligations. The auxiliary module keeps only the public import
   needed by its statements and a private proof import for the ambient construction.
   Verdict: pass.
5. Checked the target node's proof route and dependencies against the Lean proof and
   confirmed that the unit assignment remains `sk-thm-picard-duality`. The two new
   nodes record the split obligations and their declarations. Verdict: pass.

Changed the auxiliary import of `DerivedAmbientDirectSums` from public to private,
since it is used only in proof bodies, and recorded the second reading here.

Second-reading corrections after preflight: restored the existing public Products import;
replaced letI with let rather than disabling the linter; completed new-node metadata,
blueprint tags and searches; updated the existing target node to the actual two-lemma
assembly. No dependency is globally pruned: the ambient, binary-sum and filtered-colimit
modules remain privately imported by the auxiliary module. LeanSearch was unavailable.
Both files compile without warnings. The unit realized fields are empty and untouched.
The two remaining sorries are strict intermediate obligations, not a renamed target.

A scratch axiom audit compiled: all three declarations use only propext,
Classical.choice, Quot.sound and sorryAx from the two open obligations. Scratch removed.
