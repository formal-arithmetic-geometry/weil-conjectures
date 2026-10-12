## What changed

Proved `RingHom.exists_finite_tensorProductMap_of_colimit` in
`Sheaf.RingTheory.FiniteMapColimitDescent`, with its statement unchanged. A private,
proved tensor-generation lemma implements step 1 by algebra-adjoin induction and
induction on tensors. Mathlib handles finite-implies-integral and finiteness of the
adjoin of finitely many integral elements.

Added `Sheaf.RingTheory.IntegralElementsColimitDescent`, containing the fully proved
`RingHom.exists_integral_tensor_generators_of_colimit`. Its private generic stage lemma
lifts the lower coefficients of one monic polynomial, reconstructs a monic polynomial,
and uses eventual zero to descend its evaluation. The public proof supplies the tensor
transition maps, checks their commuting squares, and transports the finite family to
one common upper bound. Both clauses of the existing elementwise colimit theorem are used.

Updated the item's DAG proof and dependencies and added the node of the new, proved
lemma. Only proof imports changed in the original module; its public imports, exported
statement and definitions are unchanged. Both modules compile locally without warnings.

## Proved and sorry left

- `RingHom.exists_finite_tensorProductMap_of_colimit`
  (`lem-weil-pbc-colimit-finite-ring-map`): proved; the original one sorry is removed.
- `RingHom.exists_integral_tensor_generators_of_colimit`
  (`lem-weil-pbc-integral-tensor-generators-colimit-descent`): proved in full.
- Private helpers `RingHom.adjoin_tensor_generators` and `RingHom.integral_at_stage`:
  proved in full.

No sorry remains in either delivered module; none was split off. The existing elementwise
colimit dependency is already proved. The required delivery dry run checks compiled
axioms of the declarations.

## No longer needed

Replaced the original direct proof import
`Sheaf.Paper.DirectedColimitBaseChangeElementwise` in the item with
`Sheaf.RingTheory.IntegralElementsColimitDescent`. The elementwise theorem remains needed
through that proved helper: no planned node or mathematical dependency is pruned.
Removed redundant trial proof imports `Mathlib.Algebra.Polynomial.Monic` and
`Mathlib.Data.Finset.Order` from the new module after confirming that it compiles using
its other imports. No abandoned helper modules are delivered.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The original proof plan is valid and all its steps
are implemented; no unit-level route is bypassed. The step-2 suggestion to multiply a
constant monic polynomial by X is unnecessary: `Polynomial.Monic.as_sum` and the strict
degree bound on the lower terms work also at natural degree zero and over zero rings.
The finite family may be empty; bounds are chosen inside the nonempty upper tail above i₀.

The referenced local `literature/stacks-project/algebra.tex` is absent on this machine.
The source proof was read directly at https://stacks.math.columbia.edu/tag/07RG.
The LeanSearch service returned Internal Server Error, recorded as unavailable rather
than as a negative search. LeanFinder, Loogle and local Mathlib/library searches worked.

## New nodes

`lem-weil-pbc-integral-tensor-generators-colimit-descent`, in
`dag/nodes/sec-proper-base-change/`, records the finite-family integral-element descent
lemma and its fully implemented coefficient-lifting, evaluation and finite-bound proof.
Its module is `Sheaf.RingTheory.IntegralElementsColimitDescent`. It assumes neither finite
type nor module finiteness, so it is only the integral-equation step of the original
argument, not a restatement of the item. No change record is required: no existing
statement, definition or public import was changed.

## Second reading by U2

1. **Unchanged interface — pass.** Compared the original module with the repository
   version using `diff -u` and the declaration parser. The existing theorem signature
   and docstring are byte for byte unchanged; its public imports are unchanged. The
   only existing-node fields changed are `proof`, `proof_deps`, and `proof_origin`.
   The second module and its public theorem are new. No existing definition or target
   statement changes, so no change record is required.
2. **Proof and axioms — pass.** Compiled both delivery files in import order through
   `lcompile.py`, without errors or warnings. Neither contains `sorry`, an axiom,
   unsafe code, opaque declarations, external implementations, or a hollow definition.
   Compiled scratch copies with `#print axioms` for the two public theorems and both
   private helpers: all four use exactly `propext`, `Classical.choice`, and `Quot.sound`,
   with no `sorryAx`, including transitively through the elementwise colimit theorem.
3. **New statements — pass.** No statement is split off with a hole. The proved new
   theorem is strictly the integral-equation descent step, with no finite-type or
   module-finiteness assumption, and its docstring and new node give the full argument.
   Checked empty generator/coefficient families (the upper tail contains i₀), constant
   monic polynomials, zero rings, arbitrary preorders, and noninjective transition maps.
   Only eventual vanishing is needed, not injectivity. Independent LeanFinder, Loogle,
   and Mathlib/library grep searches found no existing integral-descent theorem.
   Mathlib's `Algebra.TensorProduct.adjoin_one_tmul_image_eq_top` assumes generation
   over the tensor base R, whereas here C is generated over B through φ and the tensor
   base is R; it is not a direct replacement for the private tensor-generation proof.
4. **Route and pruning — pass.** Read Stacks Tag 07RG and the unit's `realized` record.
   The original five mathematical steps remain implemented, with coefficient lifting
   and eventual zero packaged together. No unit realization is bypassed. All proof
   imports provide facts actually used; the public imports supply the signatures.
   The only old `proof_deps` absent from the item's new direct list is
   `lem-weil-pbc-directed-colimit-base-change-elementwise`: it remains used through
   the new helper and its node, so no node or module is pruned from the closure.
   Mathlib's monic polynomial lifting lemmas were also inspected; using them would
   still require the same common-stage coefficient argument and additional imports.
5. **DAG agreement — pass.** Checked each node's proof steps against the Lean and
   verified that the union of their `uses` equals `proof_deps`. The new node has the
   required source, proof origin, searches, creation, blueprint, chapter/unit, and
   Lean records. Its statement is the proved finite-family integrality theorem;
   the existing node retains the finite-map statement and records the actual route.

Second reading changed only this report: added the independent checks and clarified
why the removed direct elementwise dependency remains needed transitively. No proof,
statement, definition, import, or node repair was necessary. One original hole is
closed, zero holes are added; this is a proof, not a decomposition.
