## Worker report

The module `lean/Sheaf/AlgebraicGeometry/EtaleOpenProjectionExchange.lean` states
`AlgebraicGeometry.Etale.ordinaryOpenProjectionExchange_forward`.  It specializes the
published derived open-immersion projection/base-change comparison to the ordinary constant
coefficient category `ModuleCat C`, with `C : Type (u + 1)` commutative, an open immersion
`j : U ⟶ Z`, its canonical pullback `pullback j a`, and an arbitrary map `a : Z' ⟶ Z`.
The proof is `sorry`, as required for a stage-2 statement.

The Lean signature renders every clause of the node as follows.  `C` and `[CommRing C]`
are the commutative coefficient ring.  `j` and `[IsOpenImmersion j]` are the open immersion;
`a` is arbitrary, with no flatness, finiteness, constructibility, characteristic, or
boundedness hypothesis.  The objects `E` and `N` are arbitrary objects of the unbounded
small-etale derived categories of sheaves of `ModuleCat C` on `U` and `Z`.  The canonical
fiber product is `pullback j a`, with projections `pullback.fst j a` and
`pullback.snd j a`; `IsPullback.of_hasPullback j a` supplies its Cartesian square and the
base-changed open-immersion instance.

The left side first applies the inverse of the open projection comparison on `j` (the node's
`gamma_{j;E,N}`), then the inverse of the canonical extension-by-zero base-change mate (the
node's `beta`), then the tensor comparison for the pullback projection and the inverse-image
composition comparison.  The two `D((pullback.snd j a)_!open[ModuleCat C]).map` factors are
exactly `d_{E,N}`: the first is the derived tensor map induced by the square comparison, and
the second is the canonical pullback tensor comparison.  The right side applies the canonical
tensor comparison for `a`, tensors the inverse base-change map for `E` with the identity on
`a^*N`, and applies the inverse open projection comparison for `pullback.snd j a`.  Thus the
composition order is right-to-left exactly as in the node's displayed equality.  The maps are
components of the recorded natural transformations, so the equality is natural in `E,N`.

The published source declaration used for the construction is
`AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionIso_inv_baseChange` in
`WeilConjectures/SixFunctors/Etale/Derived/OpenImmersionLowerShriekProjectionBaseChange.lean`.
Its inverse normal form supplies the same canonical factors; the forward signature in this
module expands the inverse tensor/base-change comparisons into the node's `d`, `beta`, and
`gamma` directions.  The source declaration is generic in an abelian monoidal coefficient
category, while this statement fixes `ModuleCat C`, as required by the node.

Dependencies used by the module are the published declarations in
`WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange` and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat`: `derivedTensor`,
`leftDerivedUpperStarTensorIso`, `derivedSquareUpperStarIso`,
`derivedOpenImmersionLowerShriekProjectionIso`, `derivedOpenImmersionLowerShriekBaseChangeIso`,
`openImmersionLowerShriek`, and the `upperStarPreservesFlat_moduleCat` instance.  The DAG
statement dependencies provide the underlying notions: `AlgebraicGeometry.IsOpenImmersion`,
`CategoryTheory.Limits.pullback`, the constant-coefficient derived-category encoding,
exact inverse image, extension by zero, derived tensor, inverse-image monoidality and
pullback-composition coherence, the extension-by-zero base-change comparison, and the
open derived tensor projection comparison.

Edge cases checked before writing include the identity square (`a = 𝟙 Z`), the identity open
immersion (`j = 𝟙 Z`), empty opens (where extension by zero gives zero objects), zero objects,
and the zero coefficient ring.  The statement imposes no assumptions that exclude these
cases, and the canonical pullback projections retain the required scheme universes.

Searches made:

- `msearch.py Q60 lem-asd-open-projection-exchange leanfinder "ordinary etale derived open projection base change equality"`: returned only generic scheme stability and map-application declarations; no match.
- `msearch.py Q60 lem-asd-open-projection-exchange loogle "derivedOpenImmersionLowerShriekProjectionIso_inv_baseChange"`: unknown identifier; no Mathlib match.
- `msearch.py Q60 lem-asd-open-projection-exchange grep "derivedOpenImmersionLowerShriekProjectionIso_inv_baseChange" WeilConjectures`: no Mathlib hits.
- `rg` in `WeilConjectures/` found the published source declaration and its compact-support consumer; no constant-coefficient declaration with this node's forward signature.
- `rg` in `lean/Sheaf` found no existing declaration for this node; nearby compact-support projection modules state different proper-map comparisons.

The module compiled cleanly with
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q60 lem-asd-open-projection-exchange`
(the expected `declaration uses sorry` warning is the only permitted warning).  No
`STATEMENT-DISPUTED` flag or node fault was found.

## Second reading by Q60

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
