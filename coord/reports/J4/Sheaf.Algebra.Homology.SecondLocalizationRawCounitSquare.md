## What changed

Completed `RingTensorCohomology.secondLocalization_raw_counit_square` in
`Sheaf.Algebra.Homology.SecondLocalizationRawCounitSquare`, preserving its signature,
visibility, docstring and sole public import. Three completely proved private helpers
handle adjoint homology, the ordinary-complex factorization of
`flatDerivedHomologyIso`, and scalar-map equality transport on unit tensors.
All elaboration options are scoped to individual declarations.

The proof follows the existing node route: universal counit factorization;
flat derived/ordinary homology compatibility; scalar adjunction and generator
identification. The node proof and proof origin now record the actual Lean argument.
The short-complex adjunction helper reuses the private proof argument in
`Sheaf.Algebra.Homology.FlatIteratedScalarExtensionHomologySquare`; that module is
not imported. Mathlib semantic, name and text searches found the generic adjunction,
`leftDerived_fac_app` and exact-homology naturality APIs, but no theorem of this
whole raw counit square.

## Proved and sorry left

Closed the sole original hole:
`RingTensorCohomology.secondLocalization_raw_counit_square`
(node `lem-pc-second-localization-raw-counit-square`).

No `sorry` remains in the item. No holes were added, and none were split off.
The private helpers `adjoint_homology`, `flat_homology_factor`, and
`extendScalars_eq_one_tmul` are proved. A single-file compile with lcompile.py
completed without errors or warnings. The delivery dry run checks axioms and
compilation again.

## No longer needed

None. The existing public import `Sheaf.Algebra.Homology.SecondLocalizationMap`
is necessary for the statement and proof. Both existing proof dependencies,
`def-pc-base-derived-tensor-cohomology-model` and
`lem-pc-second-localization-map`, remain used. No modules or nodes are pruned.
No ordinary comparison, cohomologyIso, localizedComparison or model-existence
lemma is invoked by this proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface correction was necessary. The DAG's proposed argument
works with the stated hypotheses. In the generator step, extension hom extensionality
reduces the check to b=1; the full generator hypothesis is preserved unchanged.
The unit route is unchanged. No definitions, statements or other modules were adapted.

## Second reading by J4

1. Compared the delivered module and node with the repository versions. The public
   theorem signature, visibility, docstring, and target statement are unchanged;
   the node edits record only the implemented proof route and its origin. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds without errors or warnings.
   Searched for forbidden declarations and `sorry`; none remain. The private helpers
   are fully proved, and the theorem uses only the permitted existing assumptions.
   Verdict: pass.
3. Checked the proof route against the imported declarations and searched Mathlib and
   `lean/Sheaf` for an existing theorem of the same statement. No duplicate or split-off
   statement was added, and the existing node remains the exact target statement.
   Verdict: pass.
4. Checked pruning and imports. The sole public import is needed by the statement and
   proof, both declared proof dependencies are used, and no unit step is bypassed.
   Verdict: pass.
5. Checked that the node proof steps, `proof_deps`, and `proof_origin` match the Lean
   proof and that the unit's realized route is retained. Verdict: pass.

I changed only this report by adding the second-reading record; no Lean statements,
definitions, or imports were changed during review.
