## What changed

Completed `AlgebraicGeometry.Scheme.Modules.exists_cupShiftedUnitChainTensor` without
changing its statement or public imports. Repaired the earlier sandbox construction.
The three proved private helpers establish that every off-support tensor summand is
zero, that every off-support total term is zero, and that the support summand
inclusion is an isomorphism. Its inverse is the actual coproduct descendent, selecting
only the (p,q) summand. Inverse multiplication (the module left unitor), transported
through the two single-complex identifications, gives the support component. Mathlib's
`mkHomFromSingle` constructs the chain map and `Hom.isIso_of_components` proves it
invertible. The generator equation follows by component normalization and concrete
composition, with the final tensor/unitor calculation definitionally equal.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.exists_cupShiftedUnitChainTensor`
(node `lem-sc-module-cup-shifted-unit-chain-tensor`). Proved 1 of 1 original sorries;
0 holes added and no sorries remain in the delivered module. The private helpers
`tensor_term_zero`, `tensor_support_zero`, and `tensor_support_iso` are complete;
no data is selected from an unproved existence theorem.

## No longer needed

None. All original imports remain: the representability module supplies
`cupSingleModule`; the homotopy monoidal infrastructure supplies ordinary complex
tensor constructions; ModuleCat's monoidal closed structure supplies the tensor
existence/preservation instances and free-module unitor. The proof uses only the
single-complex definition from the representability interface, not its existence
theorem. The original node's support/multiplication proof route is retained, and no
unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt had the complete mathematical construction but did not compile:
its support inverse identity required simplification followed by definitional equality;
its zero-object isomorphism omitted the inequality argument; the component isomorphism
lemma is `HomologicalComplex.Hom.isIso_of_components`; and the concrete generator
calculation required exposing composition before definitional congruence. These are
proof repairs, with no change to the mathematical statement. The construction covers
all integer degrees, including zero and negative degrees, and the zero ring, since
neither the support argument nor the unitor requires nontriviality.


## Second reading by V4

1. **Unchanged interface: pass.** Compared the full sandbox module with the repository
   version. The existing theorem signature, universe and ring parameters, visibility,
   docstring and all public imports are byte for byte unchanged. Only its proof and
   three private, fully proved support helpers were added. No change record is needed.
2. **Proof and trust: pass.** Independently compiled the delivered module through
   lcompile.py without errors or warnings. A scratch copy with `#print axioms
   AlgebraicGeometry.Scheme.Modules.exists_cupShiftedUnitChainTensor` reports exactly
   `propext`, `Classical.choice`, `Quot.sound`. No sorry or forbidden declaration occurs
   in the delivered source. The support inverse is explicitly constructed by
   mapBifunctorDesc; no arbitrary witness of an unproved existence result is selected.
3. **Split statements: pass, none.** No statements or holes are split off. Checked the
   off-support disjunction, the support inclusion inverse identities, the outgoing
   differential degree, and normalization at 1. They hold also for negative p and q,
   p+q=0, and the zero ring. Independent LeanFinder search for a complex supported at
   one integer degree found `CochainComplex.exists_iso_single`; it supplies neither the
   normalized summand component nor its generator equation, and is no shorter than the
   existing mkHomFromSingle/component-isomorphism assembly. Searched library and
   Mathlib sources for single/tensor comparisons: existing BifunctorSingle comparisons
   specialize one degree to zero and do not replace this arbitrary-degree construction.
4. **Route and pruning: pass.** Each import supplies statement-level data or instances:
   representability defines cupSingleModule; the homotopy infrastructure supplies the
   ordinary complex tensor; ModuleCat.Monoidal.Closed supplies module tensor and
   preservation instances. Scratch removal checks for each tensor import fail already
   during elaboration. No proof-only public import was added. The original proof_deps
   contains only the representability node, whose single-complex definition is used;
   no old dependency is omitted. The unit sk-prop-av-cube has empty realized lists in
   the repository; this delivery does not change that pre-existing bookkeeping and
   bypasses no unit statement or step. The support/multiplication route is retained.
5. **DAG agreement: pass after metadata update.** Updated the existing node's proof
   and proof_origin to record the concrete coproduct inverse, mkHomFromSingle,
   componentwise isomorphism, and definitional generator normalization. Its statement,
   stmt_deps, proof_deps, lean statement, unit and chapter are unchanged. There are no
   new nodes.

Second reading changed only the existing node's proof metadata and this report. The
Lean proof was correct as submitted and is retained. The sole original hole is closed;
zero holes are added. No import or module is pruned.
