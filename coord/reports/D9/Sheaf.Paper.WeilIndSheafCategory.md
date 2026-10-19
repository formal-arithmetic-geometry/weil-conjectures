## What changed

Completed fourteen existing proofs in `lean/Sheaf/Paper/WeilIndSheafCategory.lean`.
The representative formula uses the recorded common-stage and rational formulas.
Frobenius naturality uses the pullback projections. T-exactness supplies all three
heart-preservation clauses; explicit subsingleton equalities align the prime-invertibility
structures without unfolding chosen inverses. Full subcategory and `AsSmall` lifts give
the two uniquely normalized squares. Abelianity transfers to the small presentation.
The Kan existence and invertible unit use Mathlib. The upstream fixed-pair Grothendieck
theorem and equivalence transport handle every quantified abelian structure.
A private, explicit functor constructs small Weil pairs, proves their uniqueness, and
supplies their fully faithful embedding using the upstream transport theorem and Yoneda.
The right-adjoint direct image is additive by preservation of binary products.

Added two proof-only imports: `Mathlib.CategoryTheory.Functor.KanExtension.Pointwise`
and `WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraFullyFaithful`.
Existing public signatures, definitions and public imports are unchanged. The private
`zlWeilSmallPairsModel` is an explicit construction, with every law proved.
Validation: the complete module compiled with no warnings or errors in 21.0 seconds on the resumed session.

## Proved and sorry left

Closed 14 of 22 original holes; added zero holes and zero split-offs.
Closed declarations:

- `WeilConjectures.zlStagePull_eq`
- `WeilConjectures.zlFrobenius_naturality`
- `WeilConjectures.zlWeilPull_mem`
- `WeilConjectures.zlPull_mem`
- `WeilConjectures.zlHeartFrobenius_mem`
- `WeilConjectures.zlHeartSquare_existsUnique`
- `WeilConjectures.zlSmallHeart_abelian`
- `WeilConjectures.zlIndMap_hasLeftKanExtension`
- `WeilConjectures.zlIndMap_unit_isIso`
- `WeilConjectures.zlSmallSquare_existsUnique`
- `WeilConjectures.zlIndWeilHeart_grothendieck`
- `WeilConjectures.zlWeilSmallPairs_existsUnique`
- `WeilConjectures.zlIndWeilPush_additive`
- `WeilConjectures.zlWeilIndEmbedding_full_faithful`

Eight original holes remain, all attached to `def-zl-weil-ind-sheaf-category`:

- `WeilConjectures.zlPullComp_existsUnique`
- `WeilConjectures.zlWeilHeart_abelian`
- `WeilConjectures.zlIndSquare_existsUnique`
- `WeilConjectures.zlIndFrobenius_exact`
- `WeilConjectures.zlIndWeilPull_isLeftAdjoint`
- `WeilConjectures.zlIndWeilPull_isRightAdjoint`
- `WeilConjectures.zlIndWeilPull_exact`
- `WeilConjectures.zlIndWeilOpenShriek_exact`

The closed proofs use the existing stated dependencies, some of which retain their
original holes. No claim is made that the entire import closure is axiom-free.

## No longer needed

None. No existing import, node or module was removed. The completed proofs follow
the existing theorem docstrings and definition-node route; no new nodes are added.

## Where the brief, the DAG or earlier work was wrong

The definition node has no numbered proof steps; the existing theorem docstrings give
the relevant plans. The module originally contains twenty-two holes. The earlier attempt
left three heart-preservation proofs open because of expensive definitional comparison
of subsingleton invertibility structures; rewriting their equality resolves it. Its
Grothendieck concern about arbitrary abelian structures is resolved by equivalence
transport. The resumed session independently recompiled the retained module successfully within
the required limit and checked its diff against the current shared source.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
