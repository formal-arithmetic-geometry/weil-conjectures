## What changed

Added `Sheaf.AlgebraicGeometry.DiagonalConormalDerivationCore` with the strictly lower-level
intermediate theorem `exists_diagonalConormalDerivation_core` (left as a documented sorry), and
proved `AlgebraicGeometry.exists_diagonalConormalMorphism` from it using the universal property
`relativeDifferentialsHomEquiv`. Added the proof-only import of the core module.

## Proved and sorry left

Proved `AlgebraicGeometry.exists_diagonalConormalMorphism`. The new theorem
`AlgebraicGeometry.exists_diagonalConormalDerivation_core` remains sorry; its node is
`lem-sc-diagonal-conormal-derivation-core-exists`.

## No longer needed

None; all original imports remain needed for the statement or the universal-property proof.

## Where the brief, the DAG or earlier work was wrong

The original DAG plan describes construction of the difference derivation but provides no
independent Lean declaration for that construction. It was split into the lower-level theorem
above so the morphism proof is a genuine application of the relative-differentials universal
property.

## New nodes

`lem-sc-diagonal-conormal-derivation-core-exists`: documented intermediate derivation existence
statement, in `dag/nodes/sec-picard-framework/lem-sc-diagonal-conormal-derivation-core-exists.json`.

## Earlier second reading (a previous round; superseded)

Pending independent second reading; the proof has been compiled with `lcompile.py --all` and the
new statement is strictly the derivation-level component needed by the morphism construction.

## Second reading by G3

1. Compared the delivered item module with the repository version. The existing theorem signature and all declarations are byte for byte unchanged; only its proof and a proof-only import were added. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`; compilation succeeds. The item theorem has no `sorry`, while the only remaining `sorry` is the named, documented split theorem `exists_diagonalConormalDerivation_core`; no forbidden declarations or hollow definitions were introduced. Verdict: pass.
3. Checked the split-off statement against the local formula and searched the library for declarations. It is a strictly lower-level derivation existence statement needed to apply the relative-differentials universal property, with a matching documented node; it is not the item morphism statement. Verdict: pass.
4. The proof uses the universal-property lemma `relativeDifferentialsHomEquiv_symm_app_d` and the core derivation theorem, and retains the unit route through the diagonal conormal and tensor-pullback structures. No unused imports were found. Verdict: pass.
5. The new node records the exact Lean statement, source, proof step, proof dependencies, module, and split status; the item node's proof is updated only to reflect the new application route. The unit remains the same (`sk-thm-picard-duality`). Verdict: pass.

Changed the item proof to obtain the lower-level derivation and transport it through `relativeDifferentialsHomEquiv`; added the documented core theorem and its DAG node; added the proof-only import and this second-reading report.
