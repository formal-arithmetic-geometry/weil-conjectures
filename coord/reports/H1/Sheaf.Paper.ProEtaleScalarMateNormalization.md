## What changed

Proved all three original holes, using existing stated general results and the published
representative tensor/pullback normalization. The ordinary and derived existence-and-uniqueness
helpers specialize `AlgebraicGeometry.Scheme.DerivedScalarMate.ordinaryTensorIso_existsUnique`
and `AlgebraicGeometry.Scheme.DerivedScalarMate.derivedTensorIso_existsUnique` to the actual
constant-ring map. Their statements, including the chosen ordinary normalization, agree
definitionally. The final theorem transposes the scalar mate with
`proEtaleRingSheafChangeAdjunction`, applies the tensor/pullback equality, uses naturality of h
and tensor functoriality, then transposes back using the existing projection-map formula.
The second conjunct is Mathlib `mateEquiv_counit`.

Validation: the server compiled all four packet modules in import order, followed by the
final theorem after its last proof edits (15.6 seconds, exit 0, no warnings). The original
final theorem signature is verbatim unchanged; all delivered Lean lines are at most
100 characters. Delivery preflight performs the independent packet and consumer checks.

Moved the shared definitions and the two now-proved helpers into
`Sheaf.Paper.ProEtaleScalarMateIdentifications`, publicly re-exported by the original module.
All declaration names, public types and definition bodies are retained. This removes the
import cycle when the original theorem imports the strictly simpler
`Sheaf.SecSmoothPurity.ProEtaleScalarTensorNormalization`. That theorem now imports the shared
definitions directly, and its unused prime, primality and primary-torsion hypotheses are
removed: its ordinary balancing and K-flat descent argument works for arbitrary finite rings.
The sole explicit call in `Sheaf.Paper.DirectImageChangeRingTranspose` drops those arguments.
The adapted modules were unclaimed when checked. No source-library module is edited.

Change records:
`coord/changes/H1-scalar-mate-identification-module.md` and
`coord/changes/H1-scalar-tensor-arbitrary-finite-rings.md`.

## Proved and sorry left

Closed three original holes:
- `AlgebraicGeometry.ProEtale.scalarMateOrdinaryTensorIso_existsUnique`
  (definition node `def-sp-proetale-scalar-mate-identifications`), by specialization.
- `AlgebraicGeometry.ProEtale.scalarMateDerivedTensorIso_existsUnique`
  (same definition node), by specialization.
- `AlgebraicGeometry.ProEtale.proEtaleScalarMateNormalization`
  (`lem-fix-proetale-scalar-mate-normalization`), by the complete adjunction calculation.

Added zero holes and zero split-off statements. No `sorry` remains in the item or shared
identification module. Existing obligations retained unchanged as obligations in adapted files:
- `AlgebraicGeometry.ProEtale.proEtaleScalarTensorNormalization`
  (`lem-sp-proetale-scalar-tensor-normalization`): one existing hole, with its finite-ring
  generalization justified in the change record; no new obligation.
- No sorry occurs in the adapted `DirectImageChangeRingTranspose` module.

These proofs use existing declarations that themselves depend on `sorry`; this report counts
closed local proof holes, not an axiom-free closure. In particular the two comparison helpers
reuse the two existing generic comparison holes rather than introducing copies under new names.

## No longer needed

Removed unused private proof imports from the shared definitions:
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`,
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
`Sheaf.CategoryTheory.ModulePullbackTensorIso`,
`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`, and
`Sheaf.Algebra.Homology.KFlatIndependentCoefficients`.
The theorem module itself needs only the public shared-identification import and private
representative-normalization import. The old public imports remain available through the
publicly re-exported identification module; none is withdrawn from consumers.

The final mate proof no longer directly uses the following old planned dependencies:
`lem-pur-change-of-rings-tensor-comparison`, `def-pur-sheaf-tensor-product`,
`lem-pur-derived-change-of-rings`, `lem-weil-pbc-ringed-projection-mate-exact`,
`lem-pur-sheaf-ring-derived-coefficient-adjunction`, `lem-pc-kflat-resolution`,
`def-weil-pbc-proetale-operations`, `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`lem-weil-pbc-ringed-topoi-module-pullback-tensor`,
`lem-weil-pbc-site-derived-tensor-descent`, `def-pc-kflat-complex`, and
`def-pc-tensor-complex-sheaves`. These are encapsulated by the existing general comparisons
and tensor-normalization theorem. They may remain needed transitively; no module is withdrawn
or claimed globally pruned. Obsolete direct tool-use entries are removed from the item's node. The generalized tensor
normalization statement no longer needs `def-weil-pbc-adic-coefficient-datum` as a statement
dependency, since the prime-primary binders are removed.
The generic arbitrary-ring-sheaf comparison is used as a tool from another unit: it is the
existing general construction whose constant-ring specialization is needed here; neither
relevant unit supplies a distinct construction. This new tool use is reported for independent
review, with no worker-added tool approval. No unit-level statement or proof step is bypassed
(both relevant unit records have empty `realized` entries).

## Where the brief, the DAG or earlier work was wrong

The ordinary and derived normalized scalar/tensor helpers were duplicates of the existing
arbitrary-ring-sheaf interfaces in `DerivedScalarMateThickLocus`; specialization suffices.
The existing tensor normalization was unnecessarily restricted to rings killed by powers of
one prime, whereas the item applies to arbitrary finite rings. The primary-torsion binders
are unused by its balanced-tensor and K-flat argument. Products such as Z/6Z show why one
cannot supply the old hypotheses from mere finiteness. The theorem is strengthened rather
than weakening this item's statement. The helper definitions originally shared the final
theorem's module, preventing direct reuse of their normalization theorem by an import cycle;
separating the shared declarations repairs that structure.

Sources read: Stacks `sites-cohomology.tex`, equation-projection-formula-map (Tag 0B56),
and the current blueprint's two relevant unit section files. The counit-defined map agrees
with the displayed Stacks map, and the representative normalization resolves the coefficient
as well as the first factor, so no flatness of B/A is assumed. Zero rings, zero complexes,
nonflat coefficient maps, empty schemes and mixed-prime finite rings require no extra
hypothesis in the categorical proof.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
