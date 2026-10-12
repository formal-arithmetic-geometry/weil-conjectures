## What changed

Proved `IsFiniteLocallyConstantSheaf.nonempty_ihom_unit_stalk_iso` by reducing to a trivializing étale cover, transporting the stalk to a constant module, and composing the étale restriction and constant-module dual comparisons. Added two strictly smaller intermediate theorem modules, each left as a named `sorry`.

## Proved and sorry left

Closed the upper hole `IsFiniteLocallyConstantSheaf.nonempty_ihom_unit_stalk_iso` by decomposition, not by an axiom-free proof. One hole closed, two added (net −1). Added `nonempty_etaleDualRestrictionIso` and `nonempty_constantModuleDualIso`, with nodes `lem-weil-pbc-etale-dual-restriction` and `lem-weil-pbc-constant-module-dual`.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The DAG's prose proof omitted the explicit restriction comparison and the constant-module dual comparison; these are exposed as separate intermediate statements.

## New nodes

`lem-weil-pbc-etale-dual-restriction` in `EtaleDualRestriction.lean`; `lem-weil-pbc-constant-module-dual` in `ConstantModuleDual.lean`.


## Second reading by U2

1. **Unchanged interface: pass.** Diffed the item against the repository. After removing
   one extra space before `:=`, the existing declaration signature is byte for byte
   unchanged. There are no new definitions, changed hypotheses, or changed conclusions.
   Both new modules are absent from the repository; no change record is needed.
2. **Proof: pass with reported dependencies.** All three modules compile through
   `lcompile.py --all`. Only the two named public split theorems contain `sorry`;
   neither is a definition. There are no forbidden commands. A scratch-copy `#print axioms` check on all three declarations shows only
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`, the latter expected
   from the two open comparisons and upstream open results. No arbitrary witness is exported as definition data:
   all choices of trivialization and isomorphisms occur within a proof of `Nonempty`.
3. **Split statements: pass.** Read both docstring proofs against the upstream
   `IsFiniteLocallyConstantSheaf.ihom_unit` source. Étale restriction is localization
   at an object, so it preserves internal Hom even without finiteness. Constant
   finite-module duality uses finite presentation and left exactness of constant
   sheafification, not projectivity. For M = 0 both duals are zero; for Λ = ℤ and
   M = ℤ/n both duals are zero despite nonprojectivity. On the empty scheme the
   sheaf comparisons hold in the trivial sheaf category, and the target has no
   geometric point. Identity étale restriction is immediate. Neither comparison
   restates the stalk theorem: one addresses restriction, the other constant objects.
   Fresh leanfinder searches for preservation of exponentials under local inverse
   image and linear duals under constant sheafification, a Mathlib grep search for
   preservation of internal Hom, and local rg over both library roots found no
   directly applicable theorem. The pro-étale comparison is on a different site
   with different hypotheses. Closing either remaining theorem needs substantial
   categorical infrastructure, not a short replacement proof.
4. **Pruning and unit route: pass.** The old node's `proof_deps` is empty, so no old
   dependency is omitted from `No longer needed`. Both new dependencies are applied.
   The four added imports serve the proof and are plain imports. The original three
   public imports supply the types and monoidal-closed structures in signatures.
   Read `dag/units/sk-thm-p1.json`: this auxiliary node realizes none of its fixed
   steps; no unit statement, realized step, or chapter route is bypassed.
5. **DAG agreement: pass.** The target proof steps describe cover lifting, transport
   of finite generation, the two comparisons, stalk transport, and linear dual
   transport. Its dependency union is exactly the two new nodes. New nodes have
   matching verbatim signatures, docstring sources and complete prose arguments,
   creation records, searches, blueprint provenance, chapter and unit.

Second reading changed only signature whitespace and the report: it now explicitly
counts the result as a decomposition (one hole closed, two added), not net proof progress.
