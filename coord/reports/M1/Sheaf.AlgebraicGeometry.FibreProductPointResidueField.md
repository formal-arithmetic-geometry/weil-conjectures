## What changed

Proved `AlgebraicGeometry.Scheme.Pullback.exists_residueField_equiv_ofPointTensor`
using the private, fully proved helper `residueField_equiv_ofPointTensor_core`.
The existing field-spectrum extension map has a right inverse obtained from
`Triplet.SpecTensorTo`, so it is bijective. The field-quotient clause follows by
composing with the fraction-field equivalence. Existing signatures and imports are unchanged.
The node now records the precise Lean realization of its existing six-step proof.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.Pullback.exists_residueField_equiv_ofPointTensor`
(node `lem-weil-pbc-fibre-product-point-residue-field`).
Added zero holes; split off zero statements. No `sorry` remains in the delivery.
The private helper is fully proved. The target's axiom check reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

None. Both imports are needed: `Mathlib.AlgebraicGeometry.PullbackCarrier` supplies
signature data and the canonical tensor morphisms; the plain proof import
`Sheaf.AlgebraicGeometry.SpecFieldPointResidueField` supplies the field extension lemma.
All six old proof dependencies remain used, either by the explicit extension lemma
or by Mathlib's constructions and naturality/full-faithfulness results implementing
the existing node's steps. No module or unit realization is pruned.

## Where the brief, the DAG or earlier work was wrong

The six-step plan is valid. Mathlib already implements steps 1--3 and the naturality
and cancellation facts needed in step 5, so these do not need to be reproved.
The first report omitted declaration-by-declaration hole counts, the second reading,
and the exact Lean realization in the DAG; those omissions are repaired here.

## New nodes

None. No statement or definition change record is required.

## Second reading by M1

1. Compared the entire sandbox module with the repository using `diff` and read both.
   PASS: the existing public theorem signature is byte-for-byte unchanged; no definition,
   import, or other module changed. The only new declaration is a private proved helper.
2. Compiled the delivered file with `lcompile.py`: no errors or warnings.
   PASS: no `sorry`, axiom, unsafe, opaque, implemented_by, extern, or hollow definition.
   A scratch copy with `#print axioms` for the target reports exactly `propext`,
   `Classical.choice`, and `Quot.sound`. The obtained extension map comes from a proved
   theorem and is uniquely determined by its extension equation; no data is selected
   from an unproved mere-existence theorem.
3. PASS: no split-off or new public statements. Read the field-spectrum extension theorem
   and the right-inverse argument; the helper proves the first conjunct of the unchanged
   target. The zero tensor ring cannot occur at a point z, since psi maps it to a field;
   the quotient clause uses exactly its stated IsField hypothesis, including the
   nontriviality it entails. No extra geometric or finiteness hypothesis is used.
4. PASS: searched Mathlib PullbackCarrier by residueField/iso and read its tensor-composite
   lemmas, and searched lean/Sheaf and lean/WeilConjectures by ofPointTensor and the
   equivalence name. No existing theorem directly replaces the field equivalence proof.
   Both imports are necessary and correctly public/plain. No old proof dependency is
   unused. Read dag/units/sk-thm-p1.json realized: this auxiliary node is below the unit
   steps, and the unit's statement and route are preserved.
5. PASS after metadata repair: read the node's six steps, proof_deps, and proof_origin
   against the actual Lean proof. Their mathematical route already agrees; annotated
   the six steps with the exact Lean declarations and recorded the stage-3 realization
   in proof_origin. No new node is necessary.

Second reading changed only the report and the existing node's proof-route metadata;
the Lean proof required no repair.
