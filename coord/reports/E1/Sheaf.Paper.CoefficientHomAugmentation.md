## What changed

Replaced the hole in `CategoryTheory.exists_coefficientHom_augmentation` by a categorical
construction from the coefficient-ring unit. For a coefficient-Hom bifunctor `F`, the
proof sets `G = F(L,-)` and constructs the natural transformation as the composite of
its unit at `B[0]`, postcomposition with `eta`, and precomposition with `delta`.
Naturality of the restriction comparison, the augmentation square, and the existing
naturality of evaluation at one prove the required identity. The equation is isolated
in proved private helpers over arbitrary categories to avoid unfolding large sheaf
and Hom-complex definitions during rewriting.

Added `Sheaf.Paper.CoefficientHomUnit` for the remaining normalized unit at `B[0]`.
Its docstring and node give the complete product-projection argument, its source, and
edge-case checks. Updated the assigned node's proof and proof dependencies to match
this factorization. The assigned theorem's signature and public imports are unchanged.
No existing definition or consumer interface changes.

## Proved and sorry left

Closed the original hole in `CategoryTheory.exists_coefficientHom_augmentation`
(`lem-weil-pbc-coefficient-hom-augmentation`) from the new unit statement.
The private helpers `augmentationFactorization` and `coefficientAugmentation` are
proved without holes.

Added one hole: `CategoryTheory.exists_coefficientHom_unit`
(`lem-weil-pbc-coefficient-hom-unit`), the whole proof of the public theorem in its own
new module. The assigned module has zero remaining holes. This is a decomposition:
one upper hole closed, one strictly smaller unit-construction hole added, net zero.
The remaining statement has no arbitrary `K`, `epsilon`, `L`, `delta`, `u`, `T`, or
`eta`; its source complex is only the ring in degree zero. The written upper proof
provides all augmentation and natural-transformation assembly.

## No longer needed

Removed direct proof imports of `Sheaf.Paper.RestrictedCoefficientHomComplex`,
`Sheaf.Algebra.Homology.BilinearHomComplex`,
`WeilConjectures.Algebra.Homology.HomComplexProjections`, and
`Sheaf.Paper.RestrictedCoefficientHom` from the assigned module. The upper argument
uses the unit lemma and `HomComplexUnitEvaluationNaturality` instead.

The corresponding four construction nodes remain dependencies of the new unit lemma;
none of these modules or nodes is claimed globally unnecessary. The general-source
product-projection chain-map calculation is replaced by functorial precomposition
with the augmentation. No module is withdrawn, and no unit or chapter route is changed.

## Where the brief, the DAG or earlier work was wrong

The existing coefficient-Hom-complex existence theorem provides a natural restriction
comparison but does not expose its normalized product-projection equations in its public
conclusion. Its existence alone therefore does not supply the unit compatibility needed
here. The new unit lemma retains exactly this missing compatibility, only for `B[0]`.
No statement is disputed. The zero-ring, empty-site, zero-complex, zero-eta and identity
augmentation cases satisfy the proposed construction and the categorical factorization.

## New nodes

`lem-weil-pbc-coefficient-hom-unit`, in the assigned node's chapter and unit, states the
normalized coefficient-Hom unit for the ring concentrated in degree zero. It cites the
existing coefficient bifunctor, product Hom-complex construction, projection theorem,
and specified evaluation-at-one isomorphism. Its three proof steps describe the
normalized comparison, the unit with only a zero-index component, and its restriction
identity. Search found ordinary module coextension and the scheme-specific
sheaf coinduction counit, but no generic small-site normalized complex unit. This is a
proper construction step; it does not restate the arbitrary-augmentation theorem.

The original theorem and its public imports are preserved verbatim. Its sole direct
consumer is `Sheaf.Paper.FlatRingedIdealCompleteEquivalence`, which requires no adaptation.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
