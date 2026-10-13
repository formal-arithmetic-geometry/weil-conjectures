## What changed

Proved `Algebra.exists_popescu_reduction_factor` by applying a finite-presentation
factorization theorem, quotienting the resulting stage by the image of `I`, and
constructing the induced `(R ⧸ I)`-algebra maps. The import cycle in the previous
attempt was removed by introducing the lower module
`Sheaf.RingTheory.PopescuStandardReductionFactorCore` for the finite-presentation
factorization statement. The target node proof dependencies were updated.

## Proved and sorry left

`Algebra.exists_popescu_reduction_factor` is proved. The new intermediate
`Algebra.exists_standardSmooth_reduction_factorization_core` remains `sorry`
(node `new-lem-popescu-reduction-factor-core`).

## No longer needed

The import of `Sheaf.RingTheory.PopescuStandardReductionFactor` is no longer
needed and was replaced by the lower core module to avoid its cycle through the
presentation modules.

## Where the brief, the DAG or earlier work was wrong

The prior route imported `PopescuStandardReductionFactor`, but that module imports
`PopescuReductionPresentation`, which imports this module, creating an import
cycle. The finite-presentation factorization step must therefore be split into a
lower intermediate theorem. The earlier concern about constructing an
`R ⧸ I`-algebra is resolved by taking the quotient of the factor stage.

## New nodes

`new-lem-popescu-reduction-factor-core`: finite-presentation factorization
through a standard smooth reduction, stated in
`Sheaf.RingTheory.PopescuStandardReductionFactorCore`.

## Second reading by W3

1. Compared `PopescuReductionPresentationCore.lean` with the repository version:
   the existing declaration signatures and `reducedAlgHom` definition are unchanged;
   only the target proof and its proof-only import were added.
2. Compiled every delivered module with `lcompile.py`; the target compiles without
   errors and has no remaining `sorry`. The only remaining sorry is the named split
   theorem `exists_standardSmooth_reduction_factorization_core`, and no forbidden
   declarations occur. Its dependency is the stated finite-presentation factorization
   node, so the target's proof uses only the permitted axioms plus that open theorem.
3. Checked the quotient construction on the edge case `I = ⊥`: the quotient maps and
   induced algebra structures reduce to the ordinary factorization maps. The target
   statement and the split core statement are unchanged and have the required source
   and proof descriptions; no duplicate library declaration was found.
4. The proof follows the node route: obtain the finite-presentation standard-smooth
   stage, quotient by the image of `I`, induce both quotient algebra maps, and verify
   their composite by quotient induction. The import of the lower core module is
   plain (proof-only), and the DAG proof dependency is updated to
   `new-lem-popescu-reduction-factor-core`.
5. The unit route is preserved: this node remains the reduced-factor step used by the
   presentation route, and the new core node supplies only its strictly simpler
   finite-presentation factorization ingredient.

Changed the target proof, corrected its DAG proof dependency to the new core node,
and split the final two-goal proof with bullets to remove the multi-goal linter warning.
