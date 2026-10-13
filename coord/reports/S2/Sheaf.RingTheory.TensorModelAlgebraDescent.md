## What changed

The signature of `AlgebraicGeometry.exists_tensor_model_algebra_tail` is unchanged.
Its proof now obtains one finite-stage pushout square, defines each tail map as the
transition tensor map composed with the finite-stage Q-map, and proves both compatibility
conditions using cocone naturality, functoriality, and tensor induction. Pushout preservation
supplies the last clause at every later stage. There is no choice of data inside a definition.

Added two modules, each with one public theorem:

- `Sheaf.RingTheory.TensorModelAlgebraStage`: the finite-stage descent step, still sorry.
- `Sheaf.RingTheory.TensorModelPushoutBaseChange`: a fully proved general base-change lemma.

The base-change proof constructs the new P-algebra structure explicitly through the tensor
transition and checks its agreement with the Q-structure. Cancellation of tensor base change
provides two pushout squares. Two applications of Mathlib's pushout pasting equivalence give
the required square. Every scalar tower used in these applications is proved explicitly.
The imports of the two new modules in the original module are proof-only imports.

All three modules compile together through `lcompile.py --all`, without warnings. The general
base-change theorem includes zero rings, arbitrary algebra maps, and arbitrary universes; its
Lean proof has no finite-presentation or flatness hypothesis. For the new finite-stage lemma,
a singleton diagram reduces to transporting the canonical tensor pushout along e. Empty I is
already excluded by the given i, not by a new hypothesis. For zero rings, eventual equalities
of finite presentations still descend; no transition map needs to be injective. Empty sets of
presentation generators or relations cause no extra condition in the stated argument.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.exists_tensor_model_algebra_tail`
(node `lem-pc-tensor-model-algebra-descent`). This is a decomposition, not a net hole reduction:
one original hole is closed and one strictly smaller finite-stage hole is added.

Proved without sorry:
`AlgebraicGeometry.tensor_model_pushout_base_change`
(node `lem-pc-tensor-model-pushout-base-change`). It uses only Mathlib.
The private tensor composition helper in the original module is also completely proved.

The only sorry in the delivery is:
`AlgebraicGeometry.exists_tensor_model_algebra_stage`
(node `lem-pc-tensor-model-algebra-stage`). Its conclusion is one stage and one square; it says
nothing about the maps on a tail or their transition compatibility. Its source and complete
natural-language proof are in both its docstring and its node. It retains the original planned
factorization and inverse-descent dependencies rather than assuming the desired tail family.

## No longer needed

No original imports were removed: all three supply types or classes in the original signature.
No modules are claimed pruned from the targets' closure.

The original five proof dependencies are no longer direct dependencies of the tail theorem:
`lem-weil-pbc-directed-colimit-base-change-elementwise`,
`lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit`,
`lem-weil-pbc-finite-presentation-over-finite-type-algebra`,
`lem-weil-pbc-finite-presentation-base-change-composition`, and
`lem-weil-pbc-colimit-category-fp-algebras`.
They remain dependencies of the finite-stage descent node, so they are still needed there.
The tail construction itself needs no new finite-presentation facts once the square exists.
Tag 05N7 is not used in this algebra-only reduction; it concerns modules.

## Where the brief, the DAG or earlier work was wrong

The earlier abandonment treated the absence of a complete existing tail construction as an
obstacle. The finite-stage conclusion can be stated in Lean, and the remaining tail construction
and pushout preservation can be proved. The existing ColimitCategoryFpAlgebras declaration does
supply map and equality descent, but in the right-tensor convention and for the selected colimit;
using it for the finite-stage square still requires the tensor-tail colimit constructions and
transport of the inverse comparison. These tasks are recorded in the new finite-stage node.

The local source file `literature/stacks-project/algebra.tex` is absent on this machine. Read
Stacks Tags 02JO, 05N9, and 05N7 on their official pages. The finite-stage step follows 02JO's
algebra comparison paragraph and 05N9's map and equality descent. The preserved unit has no
realized node for this lower-level lemma, and no unit statement or route is bypassed.

Mathlib searches were run through `msearch.py` (LeanFinder, Loogle, grep). LeanSearch returned
an internal server error and is recorded as unavailable. Relevant results are factorization
through a filtered colimit, tensor cancellation, and pushout composition; no exact finite-stage
model declaration was found. Blueprint searches for tensor model and pushout found no duplicate
of either new statement. The ancestry tool returned no ancestor for this newly created item;
the new records retain the explicit blueprint ancestor and chain in the item's own record.

## New nodes

`lem-pc-tensor-model-algebra-stage` in
`dag/nodes/sec-picard-framework/lem-pc-tensor-model-algebra-stage.json` states only the initial
finite-stage square and its prescribed image in the colimit. Its numbered proof retains the
original descent plan and existing dependencies. Its Lean module is
`Sheaf.RingTheory.TensorModelAlgebraStage`.

`lem-pc-tensor-model-pushout-base-change` in
`dag/nodes/sec-picard-framework/lem-pc-tensor-model-pushout-base-change.json` records the
fully proved generic preservation step, without a directed diagram or any finite-presentation
hypotheses. Its Lean module is `Sheaf.RingTheory.TensorModelPushoutBaseChange`. The existing
Mathlib-leaf node `lem-weil-pbc-tensor-cancel-base-change` is used as a generic tool from another
unit: it is the tensor identification needed for the pushout proof, not a replacement for a unit
route. There is no change record because no existing statement or definition was changed.

## Second reading by S2

1. **Interface comparison: pass.** Read the diff against the repository's
   `TensorModelAlgebraDescent.lean`: the existing public declaration, its docstring,
   universes, hypotheses and three conclusion clauses are byte-for-byte unchanged.
   The additions are two plain proof imports, a private proved composition helper,
   and the replacement proof. Neither another existing module nor a definition changes.
   The existing node changes only `proof`, `proof_deps`, and `proof_origin`.

2. **Proof and trust: pass.** Compiled all three modules with `lcompile.py --all`.
   Read the tail construction: `q j hkj` is the actual composite of the tensor
   transition with `qk`; `c.w` proves its colimit compatibility and `F.map_comp`
   proves its transition compatibility. The final application instantiates the
   general preservation theorem with exactly F(i), F(k), F(j), A, B, P and Q.
   Read every scalar tower and both pasting applications in the base-change proof.
   Scratch-copy `#print axioms` checks show only propext, Classical.choice and
   Quot.sound for base-change and the private helper; the stage and tail theorems
   additionally use sorryAx, precisely from the reported finite-stage hole.
   There is no axiom, unsafe/opaque declaration, external implementation or hollow
   definition. The existential stage data are used inside a theorem proof, and
   all subsequent maps are explicit composites.

3. **Split statement: pass as decomposition.** Read Stacks
   [02JO](https://stacks.math.columbia.edu/tag/02JO), final comparison paragraph,
   [00QO](https://stacks.math.columbia.edu/tag/00QO), factorization of finite
   presentations, and [05N9](https://stacks.math.columbia.edu/tag/05N9), clauses
   (2) and (3). The stage statement retains every input of the item and asks only
   for one compatible square, omitting the tail family and both family identities.
   It is a strict part of the argument; the delivered proof actually constructs
   that family and establishes its properties. For the stage proof, P finite
   presentation descends its map, Q finite presentation descends its map over P,
   finite type of A plus finite presentation of B over F(i) gives B finite
   presentation over A, and 05N9 descends the inverse and its identities over the
   A-stage diagram. Read the statements of all five cited nodes: they supply
   these facts, including the elementwise tensor colimit and map/equality descent.
   Transport from the chosen colimit and tensor commutation is still work for
   the remaining Lean proof; it is not claimed completed here.

   Edge cases: the given i excludes an empty index type; a singleton diagram
   gives the square by transporting the canonical tensor pushout along e.
   A zero target colimit is allowed: any needed relation 1=0 descends just like
   other finite relations. Empty generator or relation lists require only a
   common upper bound with the starting stage. No step uses injectivity or
   flatness. The base-change lemma permits zero rings and identity transitions
   and has no finite-presentation restriction. Its statement matches the actual
   constructed P-map and Q-map, including the required scalar-tower compatibility.

   Independently searched with msearch LeanFinder for descent of isomorphisms of
   finitely presented algebras, Loogle for tensor-map composition, and grep for
   finite-presentation/isomorphism/colimit combinations. Also searched lean/Sheaf
   and the upstream WeilConjectures sources for tensor-model and pushout-model
   declarations. No replacement for the finite-stage statement was found.
   `ColimitCategoryFpAlgebras` supplies components, rather than the whole square.
   The stage docstring gives the four-step mathematical argument and its node.
   Closing this remaining hole requires those tensor diagrams and transports;
   it is not a few-minute direct application.

4. **Route and pruning: pass.** Read `sk-thm-picard-semicon.json`: its realized
   statement is empty and its realized steps are `[[]]`; this lower-level lemma
   is not a realized unit step being bypassed. The original five dependencies
   listed under No longer needed move to the finite-stage node, while the tail
   uses that node and base-change. All three original public Mathlib imports
   supply signature notions; both new imports are proof-only. The preservation
   module imports only IsTensorProduct. No module is claimed pruned. The shortest
   route found improves the private helper via Mathlib's `map_comp`.

5. **DAG agreement: pass after metadata repairs.** The tail node records the
   finite-stage application, explicit transition identities, and preservation.
   The stage node records the five original descent dependencies; their union
   equals its proof_deps. The preservation node records tensor cancellation and
   the two explicit Mathlib pasting applications. New nodes have sources,
   searches, provenance, blueprint ancestry, creation and Lean records. Corrected
   their Lean statement records to the verbatim multiline signatures and removed
   doubled TeX backslashes. Removed the irrelevant module-descent Tag 05N7 from
   new-node source places; retained existing-node interface fields unchanged.

Changes made by this reading: replaced the private tensor-induction proof by the
Mathlib tensor-map composition equality, repaired new-node statement formatting
and source references, and added this review. The mathematical interfaces and
remaining hole are unchanged. One original hole closed, one new stage hole added:
net zero; base-change is fully proved; no modules pruned.
