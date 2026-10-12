## What changed

Replaced the proof of `AlgebraicGeometry.Scheme.GaloisCover.exists_sectionEvaluation`
with a reduction to ordinary linear evaluation and its forced deck equivariance.
The proof corestricts each linear map to the equivariant submodule, proves naturality
by pointwise extensionality, and retains the diagonal normalization. The existing
signature and definitions are unchanged.

Added `Sheaf.ConstructibleSheaf.TorsorOrdinaryEvaluation` and
`Sheaf.ConstructibleSheaf.TorsorOrdinaryEvaluationEquivariant`, each containing one
named open theorem. Their imports are public because their signatures use the
section representation and etale inverse-image definitions. The target imports
these modules privately for its proof. Removed its redundant direct import of
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, which both new modules import.
Updated the target node's proof, proof_deps and proof_origin to the actual reduction.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.GaloisCover.exists_sectionEvaluation` (1 of 1 original holes).
Its checked Lean proof still rests on the following two added holes:

- `AlgebraicGeometry.Scheme.GaloisCover.exists_ordinarySectionEvaluation`, node
  `lem-weil-pbc-torsor-ordinary-evaluation`, in TorsorOrdinaryEvaluation.lean.
- `AlgebraicGeometry.Scheme.GaloisCover.ordinarySectionEvaluation_equivariant`, node
  `lem-weil-pbc-torsor-ordinary-evaluation-equivariant`, in
  TorsorOrdinaryEvaluationEquivariant.lean.

This is a decomposition, not an axiom-free proof or positive net hole progress:
one hole closed, two added (net -1 in the affected closure). There are no other
new holes, no hollow definitions, and no arbitrary objects chosen from an unproved
existence theorem. The existential beta is used within a theorem proof only.
Each lower theorem has a source and a complete proof in words in its docstring.

## No longer needed

Removed the target's direct import of
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`; the module remains needed
through the new statements. No module is pruned from the import closure.

The old target proof_deps `def-weil-connected-scheme`,
`def-weil-pbc-constant-sheaf` and `def-weil-pbc-inverse-image` are no longer direct
proof dependencies: they are retained below both new nodes. The fourth old dependency,
`def-weil-pbc-torsor-section-representation`, remains directly used in the corestriction.
No unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The first report described obsolete SectionEvaluationMap, SectionEvaluationPointwise
and SectionEvaluationNormalization modules. These are not delivered. It omitted nodes
for the two actual split-off statements, omitted the target node update, and did not
state the decomposition's hole count. The second reading repairs these omissions.
The construction for arbitrary modules is a fixed-cover extension of the finite-module
Stacks discussion: constant sheafification and local sections provide the argument;
we do not apply the finite-monodromy equivalence to an infinite coefficient module.

## Second reading by F2

1. Compared every delivered module with the repository. The target is the sole
   existing module changed, and its theorem signature is byte-for-byte identical.
   Its public import and existing docstring stay unchanged; no existing definition
   changes. The other two modules are new. Verdict: unchanged mathematical interface.
2. Compiled all three modules in import order with lcompile.py; each compiles without
   errors or warnings. Explicit #print axioms checks on a temporary copy show only
   propext, Classical.choice, Quot.sound and sorryAx for all three theorems. Only the
   two named lower theorems contain sorry, each exactly `:= by sorry`. There are no
   forbidden declarations or definition holes. Verdict: valid conditional proof,
   with both open obligations reported.
3. Read both lower statements and their proofs in words. Ordinary evaluation omits
   deck equivariance; the second theorem deduces equivariance for an arbitrary natural,
   diagonally normalized ordinary evaluation. Each is strictly a part of the argument.
   Checked empty etale objects (unique zero function / vacuous equality), zero modules,
   and the identity torsor. Nonempty connected Y identifies its constant global
   sections with A; no finiteness of A is used. Searched again using LeanFinder for
   sections of constant etale sheaves, Loogle for locally constant values on connected
   spaces, and grep for ordinary evaluation / deck equivariance; LeanSearch was
   unavailable. Inspected the returned interfaces and searched project Lean sources:
   no duplicate or independent shortcut was found. Verdict: true, needed decomposition.
4. Checked the top-down reduction, its imports and all old proof_deps. Removed the
   redundant target import; retained both lower imports and the representation import.
   Checked dag/units/sk-thm-p1.json realized: this helper is below the fixed unit steps,
   and the existing target node continues to carry the same step of the torsor argument.
   Verdict: unit route kept; pruning inventory complete.
5. Added complete nodes for both new theorem modules, with verbatim Lean signatures,
   sources, proof steps, search records, creation records and inherited chapter/unit.
   Updated only the existing node's proof, proof_deps and proof_origin. Its proof now
   follows obtain beta, obtain equivariance, construct alpha, and retain normalization.
   Verdict: DAG agrees with the delivered Lean.

Changed during second reading: repaired the stale report and hole accounting, added
both missing nodes and the target proof metadata, clarified local-section and inverse deck action arguments in the new docstrings, removed the redundant direct import, and restored the original target namespace-opening
command after the dry run flagged its unnecessary change.
No extra lower hole was closed in this reading.

## New nodes

`lem-weil-pbc-torsor-ordinary-evaluation` states existence of the ordinary linear,
natural and diagonally normalized evaluation in its own new module. Its open proof
constructs locally constant values using restriction of the constant trivialization.

`lem-weil-pbc-torsor-ordinary-evaluation-equivariant` states the missing deck
compatibility of any such evaluation in its own new module. Its open proof uses local
presentations of sections by global sections over Y, naturality on their graphs and
inverse deck restriction. No change records are needed: no existing statement or
definition changed.
