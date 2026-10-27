## What changed

Proved `CategoryTheory.RegularScalarQuotient.regularScalarQuotient_exactRow`
from the module presentation, the exact row of quotient modules, and the normalized
chain tensor comparison. The statement, universes and maps are preserved; the unused
inequality binder is named `_hm`.

The parent proof now contains the actual cone argument. It constructs the augmentation
with `mappingCone.descShortComplex`, proves its quotient normalization, obtains its
quasi-isomorphism from the short exact presentation, proves the two rank-one term
isomorphisms and vanishing elsewhere, and proves K-flatness using the existing
independent-coefficient bounded-flat theorem. In the quotient-linear part it constructs
the augmentation from the exact row's zero composite and combines this with the two
normalized tensor-coordinate equations. Exactness of that two-arrow complex is not
misused as short exactness.

Moved the twenty existing notation declarations, with identical names, signatures and
bodies, into `Sheaf.Algebra.Homology.RegularScalarQuotientNotation`, publicly re-exported
by the original module. This allows the smaller proof items to use them without an
import cycle. No object is chosen from an unproved existence theorem. The only change
record is `coord/changes/regular-scalar-quotient-notation-relocation.md`; no existing
consumer module needs adaptation (`tools/downstream.py` reported zero).

The separate presentation lemma is proved by descending sectionwise quotient
factorizations through the locally bijective ring-sheafification unit. Its cokernel
universal property retains the canonical projection. Repeated cancellation proves
monicity of the scalar power. The implementation follows the local quotient and
sheafification comparison used in the already proved
`SuccessiveQuotientFlatTensorSequence`, with private helpers for this presentation.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.RegularScalarQuotient.regularScalarQuotient_exactRow`
(node `lem-sp-regular-scalar-quotient-exact-row`).

Also proved the new
`CategoryTheory.RegularScalarQuotient.regularScalarQuotient_presentation`
(node `lem-sp-regular-scalar-quotient-presentation`).

Added two holes, each in its own module with its complete source and proof in words:

- `CategoryTheory.RegularScalarQuotient.regularScalarQuotient_moduleRow`
  (`lem-sp-regular-scalar-quotient-module-row`): the module-sheaf exactness calculation,
  with no complexes, tensor comparison or resolutions.
- `CategoryTheory.RegularScalarQuotient.regularScalarQuotient_tensorComparison`
  (`lem-sp-regular-scalar-quotient-tensor-comparison`): the normalized chain isomorphism,
  independent of regularity and index ordering, with no exactness claim.

This is a decomposition of the original hole into two strictly smaller obligations,
not a claim that the target import closure is free of `sorry`. The original module,
the notation module and the presentation module contain no holes.

The new statements include `n=m`, a unit scalar and the zero ring. A finite
representative enumeration checked the quotient row over the integers for scalars
1, 2, 3 and -2 and all `0 ≤ m ≤ n ≤ 4`: injectivity, both kernels/images,
the complementary-power ideal and every diagonal identity agreed. For `n=m`, the
module row is the identity, zero, identity row. In the tensor comparison only the
first tensor factor's degree zero survives, so the differential sign is positive.
The presentation uses local sheafification, without claiming that the sheaf quotient
map is surjective on every section.

All five modules compiled through `lcompile.py --all`; the final remaining unused-section
variable warning was repaired by omitting that unnecessary instance from the private lemma.

## No longer needed

No modules are withdrawn. The original item's parent DAG argument still needs it,
even though it currently has no Lean importers. The unit route is retained.

The direct proof import
`Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat` and its node
`lem-pc-bounded-above-flat-kflat-site` are replaced for this proof by the already
proved `Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients`
(`lem-weil-pbc-independent-bounded-flat-kflat`), whose universes fit the statement.
The old specialized bounded-flat module is not needed by this proof.

The original public construction imports are re-exported through the common notation
module. The direct imports of `FlatOnSite`, `PreservesSheafification` and module
presheaf `Sheafification` leave the parent: flatness remains available through the
bounded-flat API, while quotient sheafification belongs to the lower module
calculations. Their mathematical roles are retained where needed, not declared
pruned from the project.

## Where the brief, the DAG or earlier work was wrong

The original DAG's bounded-flat declaration uses one site/coefficient universe and
the live K-flat predicate. The item's statement has independent object, morphism and
coefficient universes. The existing independent-coefficient bounded-flat criterion
resolves this interface mismatch without changing the theorem's hypotheses.

The declaration's reference to sectionwise quotients must be distinguished from
surjectivity of the final sheaf quotient on sections. The presentation proof uses a
locally bijective sheafification unit and its universal factorization, preserving
this distinction. No mathematical statement is disputed or weakened.

## New nodes

`def-sp-regular-scalar-quotient-notation` owns the unchanged notation relocated from
the parent module. It introduces no new quotient or tensor construction.

`lem-sp-regular-scalar-quotient-presentation` is the canonical short exact module
presentation used for the Koszul resolution (original proof step 1).

`lem-sp-regular-scalar-quotient-module-row` is the remaining quotient-module algebra
and sheafification from original steps 4–6. Its source and proof retain both quotient
ring linearity and the local representative formulas.

`lem-sp-regular-scalar-quotient-tensor-comparison` is original step 3, without the
augmentation (constructed in the parent) and without unnecessary regularity or
ordering hypotheses. Each new node has its Lean attachment, actual Mathlib search
records, and the same blueprint ancestor and unit as the parent. The imported
blueprint was searched for regular scalar, coefficient tensor and power quotient.

Change record: `coord/changes/regular-scalar-quotient-notation-relocation.md`.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
