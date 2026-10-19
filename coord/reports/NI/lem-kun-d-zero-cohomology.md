## Worker report

The node is an existing-declaration item.  The upstream declaration
`DerivedCategory.isZero_iff` in
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
has the signature recorded in the node.  No module is added.  The declaration
is sorry-free and its proof uses only the standard derived-category result.

The node has no `stmt_deps`; its proof dependency is
`def-weil-pbc-derived-categories`, which supplies the meaning of
`D(T_{\Et})` and `\mathcal H^q`.  The existing theorem supplies the generic
abelian-category statement needed after specializing to the sheaf category.

Searches made:

- `msearch.py NI lem-kun-d-zero-cohomology leanfinder "complex in derived category is zero iff all cohomology objects vanish"`: eight hits, including the related Mathlib `DerivedCategory.isLE_iff` and `isGE_iff`; the exact theorem was found in the upstream source.
- `msearch.py NI lem-kun-d-zero-cohomology loogle "DerivedCategory.isZero_iff"`: no hit because this declaration is in the upstream WeilConjectures extension rather than Mathlib's index.
- `rg` over `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, the project's `lean/Sheaf`, and Mathlib: the exact declaration occurs only in the upstream extension; no competing Sheaf declaration exists.

## Second reading by NI

I read the node `dag/nodes/sec-smooth-purity/lem-kun-d-zero-cohomology.json`,
the source place named there (the blueprint node and its proof paragraph), and
the complete upstream declaration at lines 28--38 of
`WeilConjectures/Mathlib/Algebra/Homology/DerivedCategory/HomologySequence.lean`.
The item-by-item correspondence is:

1. The node's object `E ∈ D(T_{\Et})` is the specialization of the theorem's
   object `K : DerivedCategory C` with `C` the abelian category of sheaves of
   abelian groups on `T_{\Et}`.  The theorem's implicit
   `[Category C] [Abelian C] [HasDerivedCategory C]` are structural instances
   required to form this derived category, not extra mathematical hypotheses
   on `T` or `E`.
2. The first conclusion clause `E = 0` is rendered by `IsZero K`, the standard
   categorical zero-object predicate.  This is the category-theoretic meaning
   of vanishing used by the derived-category definition and does not choose a
   special representative for `E`.
3. The second clause `\mathcal H^q(E)=0` for every integer `q` is rendered by
   `∀ n : ℤ, IsZero ((homologyFunctor C n).obj K)`, with `n` exactly the node's
   `q` and `homologyFunctor` exactly the derived cohomology functor.
4. The biconditional is preserved in both directions.  There are no hypotheses
   in the node beyond membership in the indicated derived category, and the
   generic theorem adds no boundedness, Noetherian, finiteness, coefficient,
   characteristic, or nonemptiness assumption.

Edge cases were checked explicitly: all negative, zero, and positive integer
degrees are included; the zero object satisfies both sides; no index-set
nonemptiness issue occurs because the quantifier is over `ℤ`; arbitrary
universes are allowed by the theorem's universe parameters; and neither an
empty scheme nor any characteristic is excluded by the statement.  No mismatch
was found, so no Lean or node statement change was needed.
