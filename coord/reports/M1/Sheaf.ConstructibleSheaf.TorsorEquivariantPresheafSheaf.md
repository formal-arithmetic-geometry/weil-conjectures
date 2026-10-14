## What changed

Completed duplicate-removal repair #1428 by retiring the public re-export in
Sheaf.ConstructibleSheaf.TorsorEquivariantPresheafSheaf. The module is retained as
an empty historical file, with documentation pointing to the canonical theorem.
Its two direct importers, TorsorInvariantSections and
TorsorSectionEvaluationBijective, now import TorsorEquivariantModuleIsSheaf
instead. Each adaptation changes exactly one proof import.

The canonical declaration
AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_isSheaf
remains the only implementation. No theorem statements, proof bodies,
definitions, visibilities, target signatures, or unit routes change.
The DAG already records that declaration in its canonical module.

Change record: coord/changes/retire-equivariant-sheaf-compatibility.md.

## Proved and sorry left

Holes closed: none (0 of 0). Holes added: none. No split statements.
The retired module, canonical implementation, and two adapted modules contain
no sorry. This delivery completes interface retirement and pruning rather than
claiming an additional mathematical proof.

All three delivered modules compile together with lcompile.py --all.
The canonical theorem's explicit #print axioms audit succeeds and reports only
propext, Classical.choice, and Quot.sound. The delivery dry run prints OK pending
the independent second reading; nothing is pushed. Its generic appended axiom
probe cannot run on the empty retired module because it has no Lean.Elab.Command
import; there are no declarations there to audit. The delivered callers pass
the tool's probes.

## No longer needed

Sheaf.ConstructibleSheaf.TorsorEquivariantPresheafSheaf is pruned from the targets'
import closure: both of its remaining importers now use the canonical module.
Its public import of Sheaf.ConstructibleSheaf.TorsorEquivariantModuleIsSheaf is
removed. Both callers remove the historical proof import and replace it with the
canonical one. No mathematical dependency or DAG node is pruned: the node's
statement and its retained implementation remain needed.

## Where the brief, the DAG or earlier work was wrong

The duplicate proof itself was removed by the landed R4 repair. The remaining
work was to re-point historical importers and retire the compatibility interface.
The previous unchanged sandbox could not pass the delivery guard; this delivery
makes the remaining interface retirement concrete. The item's generic claim
that it contains sorry is inapplicable to this repair.

## Forced adaptations

Sheaf.ConstructibleSheaf.TorsorInvariantSections, unclaimed: the original module
fails against the retired interface at line 78: error(lean.invalidField): Invalid
field `equivariantModulePresheaf_isSheaf`: The environment does not contain
`AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_isSheaf`.
Replace only its import at line 9 with the canonical module import. It compiles.

Sheaf.ConstructibleSheaf.TorsorSectionEvaluationBijective, unclaimed: the original
module fails against the retired interface at line 69 with the same
lean.invalidField diagnostic for `equivariantModulePresheaf_isSheaf`.
Replace only its import at line 11 with the canonical module import. It compiles.

Both original failures are tested using the compiled retired module as a sandbox
overlay. The original statements, visibility, definitions, and proofs are kept
verbatim. The delivery tool independently repeats the counterfactual checks.

## Second reading by M1

1. PASS. Independently diffed all three delivered modules against the repository.
   The item removes only its public re-export and replaces its module documentation;
   it had no declarations. Each caller changes exactly one plain proof import.
   All declaration signatures, definitions, visibility, docstrings, and proof bodies
   in both callers are byte for byte unchanged. The public interface retirement is
   explicitly documented in retire-equivariant-sheaf-compatibility.md; it changes
   no target statement or definition used by a target.
2. PASS. Independently compiled the three files with lcompile.py --all: no errors
   or warnings. Searched the delivered Lean sources for sorry, axiom, unsafe,
   opaque, implemented_by, extern, and sorryAx: none. A fresh scratch audit using
   the sandbox compiled overlay printed axioms for equivariantModulePresheaf_isSheaf,
   equivariantModulePresheaf_trivial, and sectionEvaluation_bijective: each uses
   exactly propext, Classical.choice, and Quot.sound. The empty retired module has
   no constants to audit and no data construction. No arbitrary existence witness
   or hollow definition is introduced.
3. PASS (no split statements). No new declarations, holes, or nodes are delivered.
   Source search confirms the existing canonical theorem is the sole implementation;
   the two adaptations use it directly rather than adding any restatement.
4. PASS. Read the retained continuous-function/subfunctor proof and both callers.
   This retirement uses the existing proved theorem by the shortest direct import.
   Only the two adapted files import the historical module in library sources;
   the third theorem caller already imports the canonical module. The replacement
   imports are proof-only, correctly plain import. No old proof dependency node
   is removed: the mathematical proof route is unchanged. Read sk-thm-p1.json,
   including realized: every unit statement and step remains intact, and the
   retired helper is not itself a realized unit step. The report lists the removed
   public import and the module pruned from the target import closure.
5. PASS. Read lem-weil-pbc-torsor-equivariant-presheaf-sheaf.json and the retained
   Lean implementation. Its lean record already names TorsorEquivariantModuleIsSheaf;
   proof, proof_deps, and proof_origin describe its actual continuous-function sheaf,
   local-equivariance subfunctor, and forgetful-functor reflection argument. No DAG
   edit is needed because the declaration and its proof are retained unchanged.

Second reading changed only this report by adding the independent review and fresh
validation evidence; no Lean repair was necessary. The delivery dry run also checks
both original callers against the baseline and the retired-module overlay, so the
forced import adaptations are independently verified before push.

## Forced adaptations

### Sheaf.ConstructibleSheaf.TorsorInvariantSections
Original against changed dependencies failed:
```
/tmp/forced-adaptation-teb24y_y/lean/Sheaf/ConstructibleSheaf/TorsorInvariantSections.lean:78:6: error(lean.invalidField): Invalid field `equivariantModulePresheaf_isSheaf`: The environment does not contain `AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_isSheaf`, so it is not possible to project the field `equivariantModulePresheaf_isSheaf` from an expression
  c
of type
  GaloisCover (ULift.{u + 1, u} P) V

(with the modules compiled into /tmp/forced-adaptation-teb24y_y/.lbuild) [6.6 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.ConstructibleSheaf.TorsorSectionEvaluationBijective
Original against changed dependencies failed:
```
/tmp/forced-adaptation-jy6el916/lean/Sheaf/ConstructibleSheaf/TorsorSectionEvaluationBijective.lean:69:8: error(lean.invalidField): Invalid field `equivariantModulePresheaf_isSheaf`: The environment does not contain `AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_isSheaf`, so it is not possible to project the field `equivariantModulePresheaf_isSheaf` from an expression
  c
of type
  GaloisCover (ULift.{u + 1, u} P) V

(with the modules compiled into /tmp/forced-adaptation-jy6el916/.lbuild) [3.0 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
