## What changed

Proved `AlgebraicGeometry.ProEtale.supported_finite_image_classical_origin` in
`Sheaf.Paper.SupportedFiniteImageClassicalOrigin`, with its signature unchanged.
Five proved private helpers descend local models, descend images by full faithfulness,
transport classicality inductively through the actual tree, and identify the underlying
abelian sheaf of the normalized encoding. All added imports are private proof imports.
`import all` reuses the already proved private normalized pushforward and open-shriek
comparisons; it makes no declarations or imports public to consumers.

The node copy now describes this implementation. The closed edge uses the existing
underived source comparison directly. The final torsion proof uses the ordinary etale
module structure sectionwise and Mathlib's `IsAddTorsion.module_of_finite`.

Sources read: Bhatt--Scholze Lemmas 5.1.2 and 5.1.4, Definition 5.1.3, and Corollary
5.1.9; HRS Section 8, proof of Lemma 8.6; the current blueprint's compactification
coherence unit. The existing normalized encoding and comparison declarations were read
before implementation. LeanFinder, Loogle and grep searches through msearch found no
more direct sheaf descent theorem. Mathlib supplies preservation of images and the
finite-scalar torsion theorem. The proof introduces no additional assumptions and
retains the unit route.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.supported_finite_image_classical_origin`
(node `lem-sfb-supported-finite-image-classical-origin`).

Added 0 holes, split off 0 statements, and left 0 holes in the delivered module.
All five new private helpers are proved. Existing imported obligations remain the
project's existing items; this delivery does not claim they are closed.

Validation: the final module compiled remotely in 15.3 seconds with exit code 0,
no errors and no warnings. The earlier unused-section-variable warnings were
repaired by `omit`. Every new proof dependency was checked not to reach the item
in the DAG; the unchanged statement and all edge cases remain covered.

## No longer needed

No original public import was removed. The proof does not need the planned standalone
weak-Serre theorem (`det-pe-classical-derived-weak-serre`, module
`Sheaf.AlgebraicGeometry.ClassicalModuleWeakSerre`): full faithfulness and exactness
transport the actual image directly. It also does not need the large umbrella theorem
`sk-thm-pe-classical-sheaves` / `Sheaf.AlgebraicGeometry.ProEtaleClassicalSheaves`:
its module and essential-image clauses are used directly from their existing detail
modules. The umbrella `lem-sf-module-object-ordinary-coefficient-equivalence` /
`Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence` is replaced by normalized encoding and
its constructibility and operation comparisons.

`sk-thm-pe-direct-image-comparison` / `Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison`
is unnecessary here: the source underived comparison in
`WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar` suffices.
`lem-sfb-internal-module-operations-transport` /
`Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport` is replaced by the existing
normalized fixed-coefficient comparisons. The scalar-model theorem
`lem-pe-finite-discrete-scalar-constant-models` remains a transitive dependency of
`encoding_constructibility`; the ringed-open-closed interface remains in the public
tree imports. Neither is claimed globally pruned.

An initially added proof import of
`Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison` was reduced to the source
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison`,
which already defines the exact natural isomorphism used. An unused proof import of
`WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar` was also removed.
These are proof-local dependency reductions; no module is withdrawn and no claim is
made that these dependencies are unused by other target branches.

## Where the brief, the DAG or earlier work was wrong

The planned proof was mathematically applicable, but its derived and weak-Serre
interfaces were stronger than needed. Existing exact full faithfulness gives the image
argument directly, the source has an underived qcqs pushforward comparison, and the
finite ordinary module structure makes the torsion proof immediate sectionwise.
There is no statement or definition repair and no change record is required.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
