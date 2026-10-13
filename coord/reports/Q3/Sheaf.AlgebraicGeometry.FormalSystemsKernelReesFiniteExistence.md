## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.FormalSystemsKernelReesFiniteExistence`
by a compiling proof assembling three strictly smaller constituent theorems:

- `FormalAssociatedGradedAlgebraExists` constructs only the algebra of ideal quotients,
  independently of F and without a Noetherian hypothesis.
- `FormalKernelGradedActionExists` constructs only the kernel action over a given algebra
  satisfying the unit and representative multiplication formulas.
- `FormalKernelGradedActionLocalGenerators` proves only local finite generation for an
  already given action. Its hypothesis uses the representative formula solely in module
  degree zero; the main proof specializes the full formula to obtain that hypothesis.

Added these three proof-only imports and three modules with sourced proof docstrings
and matching new nodes. Updated only proof, proof_deps and proof_origin of the existing
node. All existing declarations, signatures, public imports and docstrings are unchanged.
There are no new definitions, no arbitrary witness chosen in a definition, and no forced
adaptations. The unit record `sk-thm-p1` was read; none of its realized nodes is bypassed.

The source checked was Stacks 087Z and its affine equivalence 087W. Searches covered the
library, DAG, Mathlib graded algebras, Rees algebras and filtrations. LeanFinder returned
algebraic filtrations and Proj structure sheaves, not these homogeneous quotient sheaf
operations. Loogle did not know GradedSheafAlgebra. LeanSearch was attempted for each
constituent and returned Internal Server Error, recorded without a no-match verdict.

Validation: all four delivered modules compile through lcompile.py in import order;
the target proof contains no sorry. Edge cases checked in the mathematical statements:
zero and unit ideals, zero modules, empty scheme and opens, m=0 and n=0. The zero-degree
specialization compiles with exactly the existing natural-number indexing and kernel
inclusion conventions. For a unit ideal all formal terms vanish by annihilation; for a
zero ideal the transitions are isomorphisms and positive kernel pieces vanish.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.formalSystems_kernel_rees_finite_exists`
(node `lem-weil-pbc-formal-systems-kernel-rees-finite-existence`).
Its proof is complete from the three new named statements. This is a decomposition,
not a sorry-free proof of the mathematical construction: one upper hole is closed and
three strictly smaller lower holes are added (net minus two before the ledger's closure
calculation). No sorry remains in the item module.

Every added sorry, one in each new module:

- `AlgebraicGeometry.formalAssociatedGraded_algebra_exists`
  (`lem-weil-pbc-formal-associated-graded-algebra-exists`).
- `AlgebraicGeometry.formalKernel_graded_action_exists`
  (`lem-weil-pbc-formal-kernel-graded-action-exists`).
- `AlgebraicGeometry.formalKernel_graded_action_local_generators`
  (`lem-weil-pbc-formal-kernel-graded-action-local-generators`).

## No longer needed

No existing import was removed, and no module or unit step is claimed pruned.
The following old direct proof dependencies are no longer applied in the parent Lean
proof; they are retained in the plans of the three constituents, not pruned:

- `def-weil-pbc-coherent-formal-module`
- `def-weil-sheaf-of-modules-category`
- `lem-weil-pbc-coherent-formal-modules-affine`
- `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`
- `lem-weil-pbc-affine-tilde-gamma-adjunction`
- `lem-weil-pbc-spec-module-tilde-sections`
- `lem-weil-pbc-completed-module-associated-graded-generators`

Their union is retained transitively in the new DAG proof plans. The new parent
proof directly uses precisely the three new constituent theorem nodes.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect found. The parent plan's first step groups the
independent algebra construction with the formal-system action, and its last steps group
the action with generation. The split makes those three tasks independent and isolates
the smaller degree-zero hypothesis actually used for generation. No change to their
mathematical route is claimed. LeanSearch was unavailable; the other searches worked.

## New nodes

`lem-weil-pbc-formal-associated-graded-algebra-exists` in
`dag/nodes/sec-proper-base-change/` states only the ideal quotient algebra, its quotient
unit and representative multiplication. Its own docstring gives affine descent and
checks the algebra laws and the existence of c on arbitrary opens.

`lem-weil-pbc-formal-kernel-graded-action-exists` in the same directory states the graded
action with its lift formula over any algebra satisfying the stated identities, with
no local finite generation conclusion. Its proof explains iterated reductions, local
lifts, annihilation of errors, sheaf gluing and module laws.

`lem-weil-pbc-formal-kernel-graded-action-local-generators` in the same directory states
finite generation for an already given action using only its degree-zero lift formula.
Its proof uses the finite completion module, quotient generators, tilde epimorphisms
and local coefficient lifts to obtain exactly the local finite-sum predicate.

No change record is required: no existing statement, definition or public interface
changed. There are no adapted modules.


## Second reading by Q3

1. Interfaces: PASS. Read the entire four-module delivery and diffed the original
   module against the repository. Its theorem signature, docstring, universes and
   public imports are byte for byte unchanged. Only three plain proof imports and
   the proof replacing its sorry were added. There are no changed definitions or
   adapted modules, so no change record is needed.
2. Proof and axioms: PASS as a decomposition. Compiled all four modules in import
   order with lcompile.py without errors or warnings. Scratch copies with
   #print axioms for each of the four declarations show exactly propext,
   Classical.choice, Quot.sound and sorryAx. The parent has no syntactic sorry;
   the three new public, named theorems each have one whole-proof sorry. No new
   definition, arbitrary data witness, axiom, unsafe, opaque, implemented_by or
   extern occurs. The existential witnesses are eliminated only inside a theorem
   proof; no public definition chooses an undetermined object.
3. Split statements: PASS. Matched every new signature against its node record
   and checked the docstring arguments against Stacks 087Z and 087W. The algebra
   lemma has no formal system or finiteness conclusion; the action lemma assumes
   the given algebra and proves only the action; the generator lemma assumes the
   action and proves only generation. None is a restatement of the parent.
   Quotient projections need only local, not global, surjectivity. The degree-zero
   formula suffices for generation because on an affine neighbourhood the finite
   completion module projects surjectively to every formal level and its kernel
   is the corresponding ideal power. Compare completedModule_associatedGraded_generators
   for precisely the coefficient congruence used in that argument.
   Checked I=0 (constant system, positive pieces zero), I=O_X (all terms zero),
   zero formal modules, empty schemes and opens, and both zero degree indices.
   In particular the n=0 kernel inclusion is the identity, and the parent
   specialization hact n 0 compiles with the stated natural-number indexing.
   Repeated LeanFinder searches separately with the phrases multiplication
   descending to homogeneous quotients, compatible quotient maps inducing
   bilinear kernel maps, and quotient generators yielding degree-zero generators.
   Results concern Proj sections, algebraic adic lifts, and ordinary finite-type
   sheaf generators, respectively, not these graded quotient-sheaf statements.
   A new msearch grep for quotient bilinear maps and graded filtrations found
   algebraic filtration structures only. Searched lean/Sheaf and lean/WeilConjectures
   for formalKernel, formalAssociatedGraded and both graded sheaf structures;
   existing polynomial-cover and polynomial-action statements require the parent
   construction and do not supply any of the three missing statements. No short
   existing-library proof of a constituent was found. Searches are recorded in
   searches.jsonl.
4. Route and pruning: PASS after reporting correction. All three new proof
   imports are used, and the public imports supply signature types. Read
   dag/units/sk-thm-p1.json, including its realized statement and four step lists.
   None of those nodes is replaced or bypassed; the split stays below the unit
   route in the graded-kernel tool. The seven old direct proof dependencies are
   all retained in constituent plans. Listed each under No longer needed to
   distinguish direct-parent replacement from actual pruning. No module is
   claimed pruned. One original hole closed, three added: a decomposition with
   net minus two holes before import-closure ledger accounting.
5. Nodes: PASS. Parsed all four node files and checked proof_deps equals the
   union of step uses. The existing node changes only proof, proof_deps and
   proof_origin, and its plan follows the Lean assembly and degree-zero
   specialization exactly. Each new node has the required source, proof steps,
   creation, blueprint ancestry, chapter, unit, search records and verbatim Lean
   statement; each remaining sorry has its own sourced proof docstring and node.

Second reading changed only this report: completed the enumeration of old direct
proof dependencies and added this independent review. No Lean proof or statement
needed repair. All three split construction/descent arguments require substantial
formalization, so none was represented as closed by this reading.
