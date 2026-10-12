## What changed

The four constructions `CategoryTheory.SiteCechComplex.tuplePresheaf`, `tupleMap`,
`tupleSimplicial` and `freeComplex` are extracted verbatim into
`Sheaf.CategoryTheory.Sites.SiteCechFreeComplexExactAux`. Their names, signatures,
bodies and docstrings are unchanged. The target module publicly imports them.
The extraction record is `coord/changes/SiteCechFreeComplexExactAux.md`.

`CategoryTheory.SiteCechComplex.freeComplex_exactAt` now derives exactness from
an objectwise contracting identity: on a cycle x the identity gives d(h(x))=x;
`ShortComplex.moduleCat_exact_iff` establishes evaluated exactness. Evaluation
preserves homology, and sectionwise morphism extensionality reflects zero homology.
The target's signature, visibility and docstring are unchanged.
`InjectivePresheafModuleCechExact` receives one forced ordinary import of
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian`, replacing its reliance on the
old public proof import; its declarations and proof bodies are unchanged.

The second reader replaced the first worker's equivalent adjacent-short-complex
restatement by `CategoryTheory.SiteCechComplex.freeComplex_evaluation_contracting`.
That statement asserts two linear homotopy maps at a fixed object, without naturality.
It covers only the fibrewise contraction step; deriving exactness and reflecting it
back to module presheaves are now actual Lean proofs.

## Proved and sorry left

Hole closed: `CategoryTheory.SiteCechComplex.freeComplex_exactAt`.
Hole added and left: `CategoryTheory.SiteCechComplex.freeComplex_evaluation_contracting`,
node `lem-weil-pbc-site-cech-free-complex-exact-fibrewise`, in the auxiliary module.
No other delivered declaration contains sorry. The four extracted constructions have
no holes and do not use the new unproved theorem to choose data.

This is a decomposition (one hole closed and one added, net zero), not an axiom-free
proof of the target. The rejected `freeComplex_exactAt_short` was never in the library
and is not delivered; removing it is not counted as closing a baseline hole.

All three delivered modules compile locally without errors or warnings. The scratch axiom
checks list only propext, Classical.choice, Quot.sound, and sorryAx where a remaining
imported proof obligation is used. The direct user's original compiles against the baseline but fails against the
delivered overlay; its forced one-line proof-import adaptation compiles. Whole-library verification belongs to the maintainer.

## No longer needed

No whole library module is pruned. The original `Sheaf.Paper.PowerSetComplexContractible`
proof import moves from the target to the auxiliary contraction lemma; its node
`lem-weil-pbc-power-set-complex-contractible` remains needed there.
The target's old direct proof dependencies `def-weil-pbc-site-cech-complex` and
`def-weil-presheaf-modules-sheafification` are replaced by the fibrewise node; the former
is still used by the auxiliary construction and both remain statement dependencies.
The presheaf homology reflection step is proved directly with Mathlib.

The redundant direct public imports of SiteCechComplex, Presheaf.Free and
AlternatingFaceMapComplex are removed from the target but remain public via the auxiliary
module. Presheaf.Abelian is now an ordinary proof import of the target and is removed
from the auxiliary module. The first worker's unnecessary proof import
`WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact` is replaced by
`Mathlib.Algebra.Homology.ShortComplex.ModuleCat`. No old dependency module is claimed
unreachable from targets.

## Where the brief, the DAG or earlier work was wrong

The first worker's `freeComplex_exactAt_short` has exactly the target's mathematical
content under `HomologicalComplex.exactAt_iff'`. Calling that restatement a strictly
lower fibrewise component was incorrect. The second reader removed it and wrote the
cycle-lifting and homology-reflection steps, retaining only the local contracting
identity as a hole. The original extraction record omitted verbatim definitions and
most downstream users; it is now complete. Its extraction does not alter any target's
meaning.

## New nodes

`lem-weil-pbc-site-cech-free-complex-exact-fibrewise`: the objectwise contracting identity
on the evaluated chosen-product complex, with a complete fibre-decomposition and
prefix-homotopy proof in the docstring. It is true for empty lift sets (zero modules)
and nonempty lift sets (prefix contraction), including degree n=0. Searches with
LeanFinder, Loogle and grep were repeated through msearch.py and recorded;
LeanSearch was also attempted and returned Internal Server Error (recorded unavailable); local
library searches found only different nerve constructions and private contraction
lemmas requiring their explicit set complexes. No result directly supplies this
chosen-product contraction. Change record: `coord/changes/SiteCechFreeComplexExactAux.md`.

## Second reading by V3

1. Compared the target and auxiliary modules with the repository's original module.
   All four extracted declarations including their bodies/docstrings are byte-identical;
   the existing target's signature and docstring are byte-identical. The only interface
   change is the documented extraction/public import arrangement, with complete
   downstream listing and the one-line forced downstream import adaptation. No target or definition is weakened or altered. Verdict: pass.
2. Compiled all three delivered files locally, scanned every sorry and prohibited declaration
   form, and added #print axioms for all six declarations to a scratch copy. The only
   new hole is the named contraction theorem; no definition chooses data from it.
   The target still depends on sorryAx through open obligations, which is reported.
   Verdict: valid decomposition, not a completed axiom-free target proof.
3. Rejected the short-complex restatement. The replacement contraction is a local
   algebraic step with no presheaf exactness claim and no naturality hypothesis. Read
   Stacks sites-cohomology.tex, lemma-homology-complex and
   lemma-complex-tensored-still-exact, and the power-set contraction implementation.
   Checked empty T, empty individual lift fibres, zero ring, singleton lift fibres,
   and n=0: zero summands vanish; in degree one the first prefix face is the identity
   and the other faces cancel with h d. The full docstring supplies the construction
   and proof; its node and three real Mathlib searches match. Verdict: pass.
4. The target now uses Mathlib's concrete exactness criterion and homology comparison,
   with a direct sectionwise zero-identity proof. Imports are minimal for signatures,
   construction and the retained proof plan; proof-only imports are ordinary imports.
   No whole module pruning is claimed. Read dag/units/sk-prop-cd.json: realized fields
   are empty and unchanged, and the fibre contraction/reflect-exactness route remains
   the original route below unit level. Verdict: pass.
5. Updated the main node's proof and proof_deps to the actual cycle-lifting and
   homology-reflection proof. The new node's statement and Lean signature name the
   contracting identity, and its proof steps/proof_deps retain the chosen-product
   and power-set construction. Existing node fields outside stage-3 ownership stay
   unchanged. Verdict: pass.

Second reading changed: replaced the equivalent sorry restatement with the genuine
objectwise contracting-identity reduction, expanded its proof docstring, repaired
imports, synchronized both DAG nodes, corrected hole accounting, and completed the
extraction change record with every downstream user. The substantial basis comparison
and transported contraction remain the single new proof obligation.

## Forced adaptations

`Sheaf.CategoryTheory.Sites.InjectivePresheafModuleCechExact` (unclaimed in the
local claim snapshot): its original source compiles against the compiled baseline.
Against the changed overlay, it fails at line 162:

```text
Application type mismatch: ShortComplex.Exact.descToInjective ?m.323 ?m.325 ?m.327
has type ShortComplex.X₃ ?m.322 ⟶ ?m.324
but is expected to have type (S.freeComplex R).X q ⟶ M
```

The old target publicly imported Presheaf.Abelian; hiding this proof-only import
removes the instance needed by `descToInjective` inference. Added exactly one ordinary
import `Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian` after its target-module
import. The adapted file compiles against the changed overlay. No declaration,
signature, visibility, docstring or proof body in this module is changed.
The extraction change record names the module and necessity of this edit.

## Forced adaptations

### Sheaf.CategoryTheory.Sites.InjectivePresheafModuleCechExact
Original against changed dependencies failed:
```
/tmp/forced-adaptation-fzfyrjk8/lean/Sheaf/CategoryTheory/Sites/InjectivePresheafModuleCechExact.lean:162:14: error: Application type mismatch: The argument
  ShortComplex.Exact.descToInjective ?m.323 ?m.325 ?m.327
has type
  ShortComplex.X₃ ?m.322 ⟶ ?m.324
but is expected to have type
  (S.freeComplex R).X q ⟶ M
in the application
  (e q) (ShortComplex.Exact.descToInjective ?m.323 ?m.325 ?m.327)

(with the modules compiled into /tmp/forced-adaptation-fzfyrjk8/.lbuild) [6.8 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
