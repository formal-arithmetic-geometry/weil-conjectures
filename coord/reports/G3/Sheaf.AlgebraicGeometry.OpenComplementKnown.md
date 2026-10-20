## What changed

Repaired the overlapping-landing return by taking the current repository version of
`Sheaf.AlgebraicGeometry.OpenComplementKnown` and replacing its sole sorry with the
complete proof of
`AlgebraicGeometry.Scheme.hasOpenComplementCondition_of_isAlgClosure_finite_and_lowDimension`.
The complete signature, all public imports and all three conclusions are preserved.

The general bound combines the stated direct-image finiteness input for constructibility
with the existing torsion direct-image dimension theorem for vanishing. Independently,
dimension zero uses the canonical clopen comparison with exact extension by zero and
computes the derived image of a single sheaf. Dimension one uses the stated curve
theorems. Proof-only imports and the node's proof route are pruned accordingly.
There are no new declarations, definitions, statement changes, or consumer adaptations.

Validation: the initial fresh single-file compile passed in 36.8 seconds and the first
dry run passed. The subsequent delivery compile exceeded 60 seconds without pushing.
Profiling identified kernel checking and module linting as the expense, rather than tactics.
Kept the proved clopen and derived-single comparison isomorphisms behind Nonempty statements
and destructured those statements at their uses, avoiding repeated unfolding of their data.
This preserves the same proof route and adds no declaration or hole. The profiled proof
compiled in 28.0 seconds (20.8 seconds kernel checking). All profiling options were removed
before the final compile, dry run and delivery.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.hasOpenComplementCondition_of_isAlgClosure_finite_and_lowDimension`
(node `lem-exc-open-complement-known`). There are zero sorry declarations left in the item and
zero holes added, zero split-off statements, and zero new modules. This is a proof from existing
declarations, not a decomposition. The existing finiteness-input and curve theorems remain
stated dependencies; their proofs are outside this delivery. The dimension-zero argument does
not use them.

## No longer needed

Removed proof-only imports (public imports and the exported interface are retained):

- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `Mathlib.CategoryTheory.Sites.Sheaf`
- `Mathlib.CategoryTheory.Sites.Sheafification`
- `Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf`
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`
- `Sheaf.AlgebraicGeometry.DerivedCategories`
- `Sheaf.AlgebraicGeometry.Dimension`
- `Sheaf.AlgebraicGeometry.DirectImageFinitenessInput`
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison`
- `WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`
- `WeilConjectures.AlgebraicGeometry.EtaleSheafClopenProduct`
- `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`
- `WeilConjectures.CategoryTheory.Abelian.ExactFunctorHigherDerivedVanishing`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`
- `WeilConjectures.RingTheory.Etale.LocalDimension`
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

The following old direct proof dependencies are unnecessary for this proof; they are removed
from proof_deps and, where present, tool_uses. This does not claim they are unused elsewhere:

- `def-weil-open-immersion`
- `lem-pqf-finite-affine-cover-qc-open`
- `lem-weil-pbc-lft-affine-pairs`
- `lem-weil-pbc-module-sheaves-grothendieck-abelian`
- `def-weil-pbc-constructible-complexes`
- `def-weil-etale-morphism`
- `def-sbc-locally-finite-presentation`
- `lem-weil-pbc-affine-scheme-qcqs`
- `lem-weil-pbc-affine-open-stalk-localization`
- `lem-sc-etale-local-dimension`
- `lem-pc-scheme-dimension-local-rings`
- `lem-weil-pbc-open-immersion-base-change`
- `lem-pc-quasi-compact-base-change`
- `lem-weil-pbc-etale-base-change-finite-limits`
- `lem-weil-pbc-etale-inverse-image-restriction`
- `sbc-lem-higher-direct-image-presheaf`
- `lem-weil-pbc-affine-etale-essentially-small-cover`
- `def-weil-pbc-abelian-etale-sheaves`
- `def-weil-pbc-sheafification`
- `lem-sbc-higher-direct-image-forget-comparison`
- `lem-weil-pbc-etale-sheaf-clopen-product`
- `lem-weil-pbc-module-sheaves-enough-injectives`
- `lem-sc-exact-functor-higher-derived-vanishing`

The affine-cover, etale-local dimension, sheafification and module/abelian comparison work is
already packaged in the existing relative torsion direct-image bound. The clopen-product
argument and the classical higher-derived vanishing lemma are replaced by the canonical
clopen comparison and exact-functor derived single-object isomorphism. Grothendieck and
injective instances come from the existing source-library infrastructure. No module is
withdrawn, and no new dependency theorem is introduced.

## Where the brief, the DAG or earlier work was wrong

The returned packet overlapped a later landing in this module. Rebuilt the sandbox module
from the current shared file, preserving its complete theorem signature and public imports,
and reapplied the complete retained proof. The current shared file still has one sorry;
no existing proof is overwritten. Refreshed the node from current metadata, changing only
proof, proof_deps, proof_origin and removal of obsolete tool_uses.

The current library uses the source-library constructibility comparison
`WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison`;
the proof imports it directly. The old expanded affine-etale vanishing argument and
clopen-product proof are unnecessary because proved source-library APIs package them.

Checked empty source, empty target, the zero ring, and annihilator exponent zero. The
inducing-map dimension bound and torsion theorem have no nonemptiness hypotheses;
the discrete-target argument includes the empty scheme; increasing the annihilator
exponent handles exponent zero. No statement is disputed and no consumer adaptation
or definition change is needed. The unit's realized statement and step lists are empty;
no realized unit route is bypassed.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
