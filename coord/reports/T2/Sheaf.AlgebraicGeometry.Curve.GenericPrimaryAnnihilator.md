## What changed

Proved `AlgebraicGeometry.IsConnectedCurve.exists_primary_annihilator` in
`Sheaf.AlgebraicGeometry.Curve.GenericPrimaryAnnihilator`, preserving its entire signature.
Added proof-only imports of
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint` and
`WeilConjectures.CategoryTheory.Sites.Point.Linear`.
A uniform exponent from Mathlib kills the stalk; scalar compatibility and joint
faithfulness of the single geometric point lift the equality to the sheaf.
The universe-lift comparison is explicit. Updated the node's proof, proof dependencies,
and proof origin to this route. Added module/source documentation and disabled the
unused-variable linter locally: primality is unnecessary for the proof but its binder stays.

## Proved and sorry left

Closed the single hole in `AlgebraicGeometry.IsConnectedCurve.exists_primary_annihilator`
(node `lem-sc-generic-primary-annihilator`). No holes remain and none were added.
This is a proof, not a decomposition. Single-file compilation passes; the delivery dry run
checks the axiom probe. The trivial group is included in Mathlib's uniform-exponent theorem.

## No longer needed

The previous proof dependencies are unnecessary for this annihilator:

- `lem-exc-abelian-sheaves-gmodules`, module
  `Sheaf.AlgebraicGeometry.AbelianSheavesGModules`.
- `lem-exc-etale-open-subgroup-fixed-field`, module
  `Sheaf.FieldTheory.OpenSubgroupFixedField`.
- `lem-sc-sylow-module-filtration`, module
  `Sheaf.RepresentationTheory.SylowModuleFiltration`.

These were not imported by the starting module, so no existing import line was removed.
The second reader removed the redundant added proof-only import
`Mathlib.GroupTheory.PGroup`; its exponent theorem is already available transitively.
They can remain necessary elsewhere; this report prunes only this node's dependency edges.
All three existing public imports remain because they support the unchanged statement.
No unit step is bypassed: `sk-prop-cd-affine` has empty realized lists, and this auxiliary
annihilator is below the unit level.

## Where the brief, the DAG or earlier work was wrong

The previous DAG step described the whole generic-cover/filtration construction rather
than the annihilator alone. Fixed fields and Sylow filtrations are irrelevant here.
The docstring's finite maximum and faithful stalk argument was correct; Mathlib already
provides the finite maximum theorem, and conservative geometric points provide faithfulness
without using the Galois-module equivalence. The chosen point must be universe-lifted to
apply joint faithfulness for `AddCommGrpCat.{u + 1}`; `uliftSheafFiberIso` bridges the stalks.
The cited blueprint source file is absent from this local checkout, so the argument was
checked against the recorded node, its existing docstring, the parent filtration-data
and trace-retraction docstrings, and the Mathlib/source-library declarations.


## Second reading by T2

1. Compared the complete delivered module with the repository version. The existing
   theorem signature is byte-for-byte identical. No definition or public import changed;
   the additions are documentation, proof-only imports, a scoped linter option, and proof.
2. Compiled the delivered file locally. A scratch copy with `#print axioms` reports exactly
   `propext`, `Classical.choice`, and `Quot.sound`. No sorry or prohibited declaration is
   present. Read the finite exponent, scalar compatibility, conservative-point, and
   universe-lift comparison arguments: they prove the unchanged conclusion.
3. No split-off theorem or new node was added. The finite-group exponent theorem includes
   the trivial stalk (exponent zero is allowed); faithfulness applies because Spec of the
   function field is a singleton and the algebraic closure is a nonempty geometric point.
   No arbitrary witness is used to define data.
4. Checked the shorter route against Mathlib and the source-library lemmas, and checked
   the unit record `sk-prop-cd-affine`: this is an auxiliary node below its steps, whose
   realized lists are empty. All three former proof dependencies are listed above.
   Removed the redundant added import `Mathlib.GroupTheory.PGroup`; tested that removing
   either remaining proof-only import fails at its corresponding source-library lemma.
   The three original public imports support the unchanged interface and are preserved.
5. Compared the old and delivered node files. Only proof, proof_deps, and proof_origin
   change; their three steps match the exponent, scalar-map, and faithful-fibre proof.
   The unchanged Lean record matches the theorem signature. No change record is needed.

Second reading changed only the redundant proof-only import and this report; the proof
body and statement were accepted unchanged. One existing hole is closed and zero are added.
