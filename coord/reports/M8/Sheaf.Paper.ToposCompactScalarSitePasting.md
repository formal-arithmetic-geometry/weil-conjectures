## What changed

Changed `lean/Sheaf/Paper/ToposCompactScalarSitePasting.lean` and the proof record
of its existing node `lem-pur-topos-compact-scalar-site-pasting`.

Proved the ordinary restriction cube by applying the faithful underlying-sheaf
functor on ordinary module sheaves. The calculation uses the specified scalar
restriction normalizations, ordinary site normalizations, and naturality. It
then descends the cube with `Functor.mapDerivedCategory_exactCube`. A generic
mate calculation identifies its scalar mates with the supplied comparisons.
`exchangeMate_cube` gives the direct constituent; a second scalar-mate cube
with the four open adjunctions gives the open constituent. Conjugation uses
only the supplied isomorphisms, never an inverse of a coefficient comparison.

Proved `word_mixed` from these constituents. Mixed compatibility and site
invertibility are separate inductions. The latter tracks arbitrary independent
A- and B-inputs, as required by the concatenation constructor. The former uses
naturality to interchange the middle coefficient and site transformations.
The factorization theorem is its two-letter specialization. Its signature and
original docstring are unchanged; it was moved below `word_mixed`.

Proved `transfer_scalar_square` by applying the two word identities, inserting
the site squares and untilde scalar square, and cancelling the mapped A-site
isomorphism and the target word's image of the scalar/pullback isomorphism.
Proved `scalar_square_conjugation` by naturality of the two transformations
forming the scalar square. Proved `paste_transfer` by applying `paste_site`
then the transfer theorem. None of these calculations assumes faithfulness on
derived morphisms.

Private helpers contain complete proofs. The scalar-square cancellation is
proved for arbitrary `Value` records before specialization to words, avoiding
repeated unfolding of `Word.value`. The ordinary cube is an instance of a
generic morphism-chain identity, avoiding repeated elaboration of large sheaf
functor expressions. All public signatures, definitions,
attributes and public imports are preserved. No other module is adapted.

## Proved and sorry left

Closed five of seven original holes, adding no holes:

- `CategoryTheory.CompactScalarSite.topos_compact_scalar_site_pasting`
- `CategoryTheory.CompactScalarSite.word_mixed`
- `CategoryTheory.CompactScalarSite.transfer_scalar_square`
- `CategoryTheory.CompactScalarSite.scalar_square_conjugation`
- `CategoryTheory.CompactScalarSite.paste_transfer`

Two original holes remain, both attached to the existing node
`lem-pur-topos-compact-scalar-site-pasting`:

- `CategoryTheory.CompactScalarSite.tilde_coefficient_transpose`
- `CategoryTheory.CompactScalarSite.paste_site`

They retain their original whole-proof form and proof docstrings. There are
no split-off theorem holes, definition holes, or new axioms. The word and
factorization proofs do not use either retained theorem. `paste_transfer`
still uses `paste_site`, as its statement intends.

Validation uses remote single-file compilation through `lcompile.py` and the
required compile and axiom probes performed by `deliver3.py`.

## No longer needed

Replaced the private import `Sheaf.CategoryTheory.DerivedExactSquareComposition`
with `Sheaf.CategoryTheory.DerivedExactCube`: the completed argument needs a
six-face cube, rather than the stated two-square composition formula. The
cube theorem is already proved and is pure exact-functor localization.
`Sheaf.CategoryTheory.ExchangeMateCube` remains used.

The finite-free constituent theorem is not needed for `word_mixed` or its
factorization specialization. Its planned role remains for the original
transpose theorem. The exact-square composition node is no longer cited by the updated proof:
the completed cube argument uses exact-cube descent, and the retained generator
steps cite mate pasting and exchange-mate compatibility. No unit step, declaration, public import, node
or module is withdrawn. No claim is made that an imported module is globally
unreachable.

The proof record adds `lem-fix-site-open-exchange-localization` as the actual
cube-descent dependency. Although recorded under another unit, its theorem
quantifies only over abelian categories, exact functors and six natural
isomorphisms; it has no trace, purity, or perfectness assumptions. The obsolete exact-square composition entry is removed from `tool_uses`; the
exchange-mate approval is preserved. Workers do not add maintainer approvals.
The reader/maintainer should review this new generic localization-tool use.

## Where the brief, the DAG or earlier work was wrong

The factorization equation is already the two-letter instance of the word
identity. Also, the mixed identities themselves need no finite-freeness or
site invertibility beyond the normalized comparison data supplied in the
structures; site invertibility is needed for the separate invertibility and
transfer assertions. The ordinary restriction cube avoids a tensor-generator
calculation and any use of faithfulness after localization.

The stated finite-free constituent dependency has a different interface:
`ToposFiniteFreeCompact.ScalarSite`, `Geometric` and `Open` retain ordinary
pushforward/extension models and their localized adjunctions. The assigned
module instead supplies `CompactScalarSite.DirectModel` and `OpenModel`
adjunctions directly on derived categories. The retained transpose proof
therefore still needs construction and transport between these presentations;
simply applying `finiteFreeCompactConstituents` to the factorization is not a
well-typed step. This is an interface issue, not an objection to using a
dependency whose own proof contains sorry.

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
