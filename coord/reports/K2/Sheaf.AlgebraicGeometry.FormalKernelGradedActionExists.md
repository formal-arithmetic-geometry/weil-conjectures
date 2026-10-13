## What changed

Replaced the sole hole in `Sheaf.AlgebraicGeometry.FormalKernelGradedActionExists`
with the construction of a `GradedSheafModule` from a natural bilinear family. The
original signature and docstring stay unchanged; both new imports are proof-only.

Added `Sheaf.AlgebraicGeometry.FormalKernelBilinearActionExists`, which isolates the
construction and lift formula without requiring a graded algebra or its module laws.
Added `Sheaf.AlgebraicGeometry.FormalKernelBilinearActionAssociative`, with a complete
Lean proof of associativity for any natural bilinear family satisfying that formula.
The latter proves transition epimorphy by induction from the defining quotient
isomorphisms, simultaneous local lifting using Mathlib, the representative calculation,
sectionwise cancellation of kernel inclusions, and gluing. The unit law is proved
in the original module directly from the formula with coefficient 1 and the identity
transition, including explicit transport along `0 + n = n`.

Updated the parent node's proof, proof dependencies and proof origin to match this
route. No existing definition, theorem signature, visibility or public import changed.
No forced adaptations are needed. The unit `sk-thm-p1` and its realized steps are kept.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.formalKernel_graded_action_exists`
(node `lem-weil-pbc-formal-kernel-graded-action-exists`). Its proof has no internal holes.

Also proved, without any nonstandard axioms:
`AlgebraicGeometry.formalKernel_bilinear_action_associative`
(node `lem-weil-pbc-formal-kernel-bilinear-action-associative`).
`#print axioms` returned exactly `propext`, `Classical.choice`, `Quot.sound`.
All its private helpers are fully proved.

Added one hole, the complete proof `:= by sorry` of
`AlgebraicGeometry.formalKernel_bilinear_action_exists`
(node `lem-weil-pbc-formal-kernel-bilinear-action-exists`). This is the only remaining
sorry in the delivered files. It has the source and complete local-lift construction
in its docstring and DAG node. It asserts only bilinear maps, restriction compatibility
and their formula, with no algebra parameter, associativity or unit law. No witness
is chosen in a definition: existential elimination occurs only in the parent proof.

Hole accounting: one original hole closed, one strictly lower construction hole added;
this is a decomposition, net zero holes closed. Associativity and the unit law are
actual proofs, rather than additional assumptions or repackaged conclusions.

All three modules compiled together with no warnings. Edge cases checked against the
proof: degree zero uses an identity kernel inclusion; identity transitions handle
`m = 0`; empty opens use the empty-cover sheaf uniqueness argument; zero modules use
the same injectivity and uniqueness proofs. Local epimorphy is never upgraded to
surjectivity on sections of an arbitrary open.

## No longer needed

No existing imports, nodes or modules are pruned. The two original public imports
are required by the original statement. The original construction dependencies remain
needed in the new lower node; their redirection is not counted as pruning.

Removed the unused `GradedSheafStructures` import from the new bilinear-construction
module, whose signature does not mention an algebra or graded-module structure.
Removed a redundant direct `Mathlib.CategoryTheory.ConcreteCategory.EpiMono` import
from the new associativity module: `Mathlib.Algebra.Category.Grp.EpiMono` supplies it.
The retained proof imports provide preservation of sheaf epimorphisms, the abelian
sheaf instance and the concrete surjective/injective factorization instances.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found in the original statement or plan. The original plan's
nontrivial bilinear-map construction is not already supplied by its definition nodes;
it remains the one construction obligation. The rest of the plan now has an explicit
Lean proof.

The repository literature source is absent on this machine. Read Stacks Tags 087Z, 087W
and 0EHN at their official online pages and obtained the source in the sandbox
scratchpad. Verified the label `lemma-finite-over-rees-algebra` for Tag 087Z; the new construction proof expands the local
argument already supplied by the parent node and identifies the kernel with the
appropriate ideal-power subquotient. No use of the full affine-completion equivalence
is needed in the associativity proof.

LeanSearch returned Internal Server Error, recorded as unavailable, not as an absence
verdict. LeanFinder returned algebraic filtration and completion lemmas, none matching
the sheaf-level statement; Mathlib grep had no match. Blueprint searches for formal
kernel bilinearity, associativity and 087Z had no duplicate. The ancestor utility returned
None because the parent's `created.item` names a module; the new nodes inherit the
parent's explicit blueprint ancestor `thm-weil-pbc-finite-etale-lifting` instead.

## New nodes

`lem-weil-pbc-formal-kernel-bilinear-action-exists` is the remaining construction
step in `FormalKernelBilinearActionExists.lean`. It is strictly a part of the parent
argument and carries no graded algebra or module laws.

`lem-weil-pbc-formal-kernel-bilinear-action-associative` is the proved law in
`FormalKernelBilinearActionAssociative.lean`. Its premise is an arbitrary already-given
natural bilinear family with the lift formula; its sole conclusion is associativity.
Both nodes have source citations, proof steps, three recorded search kinds, complete
Lean records and the parent's chapter, unit and blueprint ancestry. No change records
are needed because all existing interfaces stay identical.

## Second reading by K2

1. I compared the delivered parent module with the repository version. The theorem
   signature and all existing declarations are unchanged byte for byte; only proof-only
   imports, the proof, and the transparency option were added. Verdict: pass.
2. I compiled all three delivered modules with `lcompile.py`, searched for forbidden
   constructs, and checked the remaining `sorry` is exactly the named construction
   theorem. The associativity theorem has no nonstandard axioms; the construction hole
   is documented and has a matching node. Verdict: pass.
3. I checked both split-off statements against their Lean declarations and source
   arguments. They are strictly below the parent, retain all hypotheses needed by the
   proof, and are not duplicates found by the recorded searches. Verdict: pass.
4. I checked the proof route from the top downward. The parent uses the bilinear
   construction, the proved associativity lemma, and a direct unit argument; the unit's
   realized route is retained. The bilinear module has only its needed public import,
   and proof-only imports are private. Verdict: pass.
5. I checked the DAG nodes' statements, proof steps, dependencies, origins, Lean
   records, chapter and unit against the delivered declarations. The parent and both
   new nodes agree, and the `realized` route is unchanged. Verdict: pass.

I changed only this report section during second reading; no Lean declarations or DAG
statements required repair.
