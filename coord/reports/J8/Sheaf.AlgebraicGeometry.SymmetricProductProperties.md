## What changed

Proved `AlgebraicGeometry.symmetricProduct_properties` with its original signature.
The proof expands the coefficient polynomials, verifies multidegree through monomial
supports, proves invertibility, obtains the coordinate morphism from generating
sections, constructs the permutation automorphism by the product universal property,
and proves invariance using section compatibility and the uniqueness of the integral
morphism. All existing statements and definitions retain their signatures and visibility.
No consumer adaptations or definition repairs are needed. In the permutation module,
`tensorPullback` is locally irreducible during elaboration, and proved private helpers
normalize the existing tensor/composition identities to global sections. This avoids
unfolding the sheafification construction during conversions; the shared definition
and all its consumers are unchanged.

Repair of the return at 695c86a4d: removed the duplicate private declarations
`factorSection_eval` and `unitHomEquiv_sum_eval` from the nonvanishing module.
Their proved versions in the permutation module are now public, and the nonvanishing
proof imports and uses those versions. Both have explicit scheme and index binders;
there is now exactly one declaration of each. No new theorem or hole is introduced
by this repair.

Rebased the retained proof on the current public import interface: preserve the landed
public import of `WeilConjectures.AlgebraicGeometry.Ample`, and directly import
`InvertibleGeneratingSectionsFibre` and `ProjectiveSpaceFunctorOfPoints` for the proof,
since `ProjectiveSpaceHomOfGeneratingSections` no longer re-exports them.
Validation after the repair: `lcompile.py --all` compiled permutation (13.7 s),
nonvanishing (4.6 s), and main properties (12.1 s), with no diagnostics.
No profiling or heartbeat-limit changes remain.

Two new modules give proved supporting theorems:
`Sheaf.AlgebraicGeometry.SymmetricProductSectionsNonvanishing` and
`Sheaf.AlgebraicGeometry.SymmetricProductSectionsPermutation`.
The former works for any family of maps to the projective line. At a point, let J be
the factors where the second coordinate vanishes. The J term of F_|J| is nonvanishing;
every other term of that cardinality vanishes. The latter constructs the actual tensor
isomorphism and its pure-section formula from pullback tensor/composition comparisons,
list permutation induction, associators, braidings, and unitors. It then reindexes the
finite sums by J ↦ π(J). These are conceptual parts of the original proof, both proved
in this delivery. The existing node's proof and proof dependencies now describe this route.

Edge cases: m = 0 uses the one-factor tensor comparison. In the nonvanishing proof,
J = ∅ and J = univ are included, and the conclusion over an empty source is vacuous.
The permutation theorem needs neither invertibility of the endomorphism nor a product
universal property: projection compatibility alone identifies the pulled factors.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.symmetricProduct_properties`
(node `lem-weil-pbc-symmetric-product-properties`).

Also proved `AlgebraicGeometry.symmetricProduct_sections_nonvanishing`
(node `lem-weil-pbc-symmetric-product-sections-nonvanishing`) and
`AlgebraicGeometry.symmetricProduct_sections_permutation`
(node `lem-weil-pbc-symmetric-product-sections-permutation`). The shared evaluation lemmas and all private helpers are proved.

Original holes: 1. Closed: 1. Added: 0. Split off with sorry: 0.
No sorry remains in any delivered module. The proof uses the already stated
projective-space functor-of-points and morphism-by-generating-sections theorems;
their existing obligations are not changed by this delivery.

## No longer needed

Removed these redundant proof imports from the item:

- `Sheaf.AlgebraicGeometry.Modules.InvertiblePullbackTensor`: the proof uses the source
  theorem directly from `WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace` and
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`: their declarations are
  already publicly available through the statement imports and remain used.

The separate fibre-basis choice and nonzero polynomial argument in original proof
steps 2–3 is unnecessary. The unique nonzero summand argument proves the same
nonvanishing statement using the existing tensor-section locus and coordinate-cover
lemmas. The product-linear-forms coefficient leaf remains needed for the polynomial
coefficient formula; it is not pruned. The projective-space base-change definition
remains a statement dependency, but is no longer a separate proof dependency.
No existing node or module is withdrawn. The blueprint unit's statement and proof
steps remain represented; none is bypassed.

## Where the brief, the DAG or earlier work was wrong

The returned delivery copied two elementary evaluation lemmas into both supporting
modules. They are now proved once and imported, as the return requests. Its old
report also relied on a public re-export subsequently removed by the landed
`ProjectiveSpaceHomGeneratingImports` change; the direct imports now reflect that change.

No false statement or incorrect definition was found. The planned abstract tensor
permutation isomorphism alone does not supply the necessary formula on sections;
that formula is proved explicitly here. The original plan's fibre-basis argument
can be shortened as described above. No launcher or project tool was changed.

## New nodes

`lem-weil-pbc-symmetric-product-sections-nonvanishing` states the no-common-zero part
for arbitrary families of maps to P¹. It realizes original proof steps 2–3, using the
existing standard-chart nonvanishing and tensor-section locus theorems. Its module is
`lean/Sheaf/AlgebraicGeometry/SymmetricProductSectionsNonvanishing.lean`; the theorem
is proved, so it creates no remaining proof task.

`lem-weil-pbc-symmetric-product-sections-permutation` states the section-preserving
pullback isomorphism under compatible reindexing of the projections. It realizes the
tensor portion of original proof step 5. Its module is
`lean/Sheaf/AlgebraicGeometry/SymmetricProductSectionsPermutation.lean`; the theorem
is proved, so it creates no remaining proof task. Both nodes record their source,
proof, searches, and precise attachment. No change record is required because no
existing statement or definition changed.

## Second reading by J8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
