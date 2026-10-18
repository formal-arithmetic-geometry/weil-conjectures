## What changed

Proved `DerivedCategory.isColimit_mapCocone_grothendieckSum` in
`Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit`, with its signature unchanged.
The existing generic `CategoryTheory.derivedCoproductCofan` supplies a coproduct of
`Q(K i)` with the canonical images of the complex coprojections. Its identity-representative
specialization shows that `Q` preserves this discrete colimit. Applying that preservation
to `HomologicalComplex.isColimitCoconeOfHasColimitEval` proves the assertion about the
exact termwise cocone in the statement. The argument applies unchanged to the empty family
and to unbounded complexes, with all four universes independent.

Added a proof-only `import all Sheaf.CategoryTheory.GrothendieckDerivedCoproducts` to
access that existing private helper. The original public import remains to preserve the
module's exported interface. Wrapped one pre-existing overlong module-docstring line.
Updated the item's DAG proof and dependencies to record this reuse. No definitions,
statements, visibility, or other modules changed. No consumer adaptation is required.

Validation: the theorem compiles via `lcompile.py`; delivery preflight checks the complete
module and its axiom probe. The import-direction check permits the dependency. The unit
has no realized steps changed by this proof; the existing K-injective/termwise-sum argument
is reused in full.

## Proved and sorry left

Closed 1 of 1 original holes: `DerivedCategory.isColimit_mapCocone_grothendieckSum`
(node `lem-kun-grothendieck-derived-coproducts`). Added 0 holes and split off 0 statements.
There are no remaining `sorry` declarations in the delivered module.

## No longer needed

Removed the direct proof imports
`Mathlib.Algebra.Homology.DerivedCategory.KInjective` and
`WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`.
Their APIs remain available through the existing generic coproduct module; neither module
is claimed to leave the targets' import closure.

`lem-sc-kinjective-quasi-iso-comparison` is no longer a direct proof dependency of this
node: its Hom-bijection argument is already implemented inside the generic cofan proof.
It remains a transitive ingredient, so no global pruning of that comparison is claimed.
The degreewise assembly, homotopy assembly, and target-isomorphism transport need no
new modules or nodes, because that entire argument was already proved. All other original
node dependencies remain used. No library module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The statement and original mathematical plan are correct. The plan did not point out that
`Sheaf.CategoryTheory.GrothendieckDerivedCoproducts` already proves the required generic
cofan universal property in its private helper `derivedCoproductCofan`. Reusing it avoids
repeating the K-injective and homotopy calculations while preserving the specified
coprojections and all edge cases. No statement repair or new node is necessary.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
