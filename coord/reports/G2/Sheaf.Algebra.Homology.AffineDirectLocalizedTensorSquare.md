## What changed

Added `Sheaf.Algebra.Homology.AffineDirectLocalizedTensorSquareCore`, whose fixed-prime
core theorem isolates the derived localization and stalk-comparison glue. The parent
module now proves its target theorem by introducing the prime and applying this core
statement. The ring-map compatibility lemma remains proved.

## Proved and sorry left

Proved: `AlgebraicGeometry.affineDirectLocalizedTensorSquare_hφ`.

The parent theorem `AlgebraicGeometry.exists_affineDirectLocalizedTensorSquare` is
proved from the new core statement. Sorry remains only in
`AlgebraicGeometry.affineDirectLocalizedTensorSquare_core`, node
`new-affine-direct-localized-tensor-square-core`; it is the unresolved fixed-prime
derived localization/stalk glue step.

## No longer needed

The parent proof no longer directly imports
`Sheaf.Algebra.Homology.DerivedTensorFirstLocalizationModels`,
`Sheaf.Algebra.Homology.DerivedTensorBaseSecondLocalizationModels`, or
`Sheaf.Algebra.Homology.AffineStalkScalarExtensionCoordinates`; those are used by
the core module instead.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt stopped before expressing the glue step. It can be stated as a
strictly smaller fixed-prime core theorem and used to close the parent theorem.

## New nodes

`new-affine-direct-localized-tensor-square-core`: fixed-prime form of the derived
localization and stalk-comparison glue, with the same explicit comparison data as the
parent but the outer prime quantifier discharged. No change record is needed.

## Second reading by G2

1. I compared the delivered parent module with the repository version. The existing
   target declaration has the same signature; only its proof and proof-only imports
   changed. The compatibility proof remains local to the target proof.
   Verdict: pass.
2. I compiled both delivered modules with `lcompile.py --all`. They compile; the only
   diagnostic is the pre-existing unused section-variable warning on the private helper.
   There are no axioms, unsafe declarations, or hollow definitions. The only remaining
   `sorry` is `AlgebraicGeometry.affineDirectLocalizedTensorSquare_core`, and its
   declaration and node agree. Verdict: pass.
3. The fixed-prime core statement is a genuine specialization of the parent with the
   outer prime introduced, and its source, proof description, dependencies, and Lean
   record are present in node `new-affine-direct-localized-tensor-square-core`. It is
   strictly smaller and is exactly the unresolved derived-localization glue. Verdict:
   pass.
4. The parent proof follows the unit route by introducing the prime and applying the
   fixed-prime core. The three former proof-only dependencies are retained by the core;
   the parent no longer imports them directly. Verdict: pass.
5. The parent node proof and `proof_deps` cite the new core node, and the new node cites
   the localization dependencies used by its module. No old dependency is needed by
   the parent proof directly. Verdict: pass.

I kept the compatibility argument local to the target proof, avoiding an untracked
public statement, and added this second-reading audit. No mathematical statement or
target was changed.
