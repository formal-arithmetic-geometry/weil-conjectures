## What changed

Updated `lean/Sheaf/Paper/WeilIndSheafCategory.lean` with four proofs.

- `WeilConjectures.zlWeilHeart_abelian`: use the exact heart functor supplied by
  `constructible_pullback_t_exact`, transport through the small presentation, and
  transfer abelianness from the category of invertible endofunctor pairs along
  the explicit fully faithful, essentially surjective small-pair model.
- `WeilConjectures.zlIndSquare_existsUnique`: characterize both composite
  ind-extensions by their left Kan universal properties. Compare their units
  using the prescribed square on representables; the same universal property
  proves the required normalization and uniqueness.
- `WeilConjectures.zlIndWeilPull_isLeftAdjoint`: identify the underlying
  ind-extension inside presheaves with left Kan extension along the opposite
  heart functor. Its presheaf right adjoint restricts to ind-objects because
  inverse image preserves finite colimits. Lift the adjunction to invertible
  Frobenius pairs using the normalized square and its mate.
- `WeilConjectures.zlIndWeilPull_exact`: finite-limit preservation follows from
  the presheaf Kan-extension model; finite-colimit preservation follows from
  the underlying adjunction. Both lift to Frobenius pairs, and preservation of
  binary products gives additivity with the recorded abelian structures.

Added only proved private helpers and private proof imports for preservation
of Kan extensions, the presheaf colimit formula, restriction of adjunctions,
and the existing adjunction construction on invertible endofunctor pairs.
Moved the Weil-heart abelianness theorem and its unchanged instance after the
explicit small-pair model so the proof can use that model. Public statements,
public imports, and the bodies of definitions and instances are preserved.

Validation: the complete module compiled through `lcompile.py` without errors
or warnings in 28.3 seconds. Scoped transparency settings avoid expensive
unfolding while elaborating the composition signature and the new proofs.

## Proved and sorry left

Closed four of the eight original holes, by declaration name:

- `WeilConjectures.zlWeilHeart_abelian`.
- `WeilConjectures.zlIndSquare_existsUnique`.
- `WeilConjectures.zlIndWeilPull_isLeftAdjoint`.
- `WeilConjectures.zlIndWeilPull_exact`.

Four original holes remain, unchanged:

- `WeilConjectures.zlPullComp_existsUnique`.
- `WeilConjectures.zlIndFrobenius_exact`.
- `WeilConjectures.zlIndWeilPull_isRightAdjoint`.
- `WeilConjectures.zlIndWeilOpenShriek_exact`.

All eight belong to `def-zl-weil-ind-sheaf-category`. No holes added, none
split off. The proofs use existing stated dependencies, including the retained
Frobenius exactness theorem; they do not assert that its proof is closed.

## No longer needed

None. No imports, declarations, modules, or nodes are withdrawn. The unit route
is preserved. Abelianness of the finite Weil heart needs only exactness of the
underlying Frobenius functor, so its proof does not require an independent proof
that Frobenius is an equivalence.

## Where the brief, the DAG or earlier work was wrong

The first preflight requested a change record for added proof-inference
commands. `coord/changes/G7-weil-ind-proof-inference.md` documents temporary
instance removal and restoration, local irreducibility, and scoped omissions.
These leave existing public signatures and exported registrations unchanged.

No statement defect found. The node is a definition node with no recorded proof
steps; this delivery preserves its construction and public declarations.
The remaining normalized common-stage composition and open-extension results
still require their separate descent and extension-by-zero arguments.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
