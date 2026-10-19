## Worker report

The module `Sheaf/AlgebraicGeometry/InfiniteProductSurjective.lean` states
`AlgebraicGeometry.infinite_product_surjective`.  It uses the Mathlib notions
`Scheme`, `Over`, `Cone`, `IsLimit`, `IsAffineHom`, and `Surjective`, and the
project declaration `AlgebraicGeometry.exists_affine_infinite_product`.

The binders render the node statement as follows:

- `(S : Scheme.{u})` is the scheme `S` from [def-pc-scheme].
- `(J : Type u)` is a small index set in the scheme universe, implementing the
  size convention [def-weil-size-convention].
- `T : J → Scheme.{u}` and `g : ∀ j, T j ⟶ S` are the family of schemes and
  morphisms `g_j : T_j → S`.
- `h_affine : ∀ j, IsAffineHom (g j)` renders that every `g_j` is affine
  [pqf-def-affine-morphism].
- `h_surjective : ∀ j, Surjective (g j)` renders that every `g_j` is surjective
  [def-weil-surjective-morphism].
- The existential cone `c` has exactly the finite-subproduct diagram used by
  [lem-trf-affine-infinite-product-existence].  `Nonempty (IsLimit c)` says its
  vertex is the product in schemes over `S`; the next conjunct records that all
  finite projections are affine; the following universal-property conjunct
  gives the unique map from every `Y : Over S` compatible with the singleton
  projections.  These are the product data supplied by the dependency node.
- `Surjective c.pt.hom` is the conclusion that the product projection to `S`
  is surjective.  The structure morphism is `c.pt.hom` because `c.pt : Over S`.

The proof is `sorry`, with its full source-based proof plan in the declaration
 docstring: choose points over a fixed point of `S`, embed all residue fields in
 a common extension field, use the product universal property, and evaluate at
 the unique point of its spectrum.  The empty index family is covered by the
 same universal property of the terminal object over `S`; an empty `S` makes
 surjectivity vacuous.

Dependencies used in the module:

- `Sheaf.AlgebraicGeometry.AffineInfiniteProductExistence`,
  `AlgebraicGeometry.exists_affine_infinite_product`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`,
  `AlgebraicGeometry.Surjective`.
- `Mathlib.AlgebraicGeometry.Scheme` (through the affine-product import),
  including `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `AlgebraicGeometry.IsAffineHom` from
  `Mathlib.AlgebraicGeometry.Morphisms.Affine` (through the affine-product
  import).
- `def-weil-size-convention` is a metatheoretic universe convention and has no
  Lean declaration; its effect is the explicit common universe `u` for `S`,
  `J`, and all `T j`.

Edge cases checked: `J = Empty` leaves no affine or surjectivity hypotheses to
choose and the product is the terminal object over `S`; `S` with no points makes
`Surjective c.pt.hom` vacuous; singleton and finite `J` are included by the same
cone and universal property.  The shared dependency's `J : Type u` ensures the
index universe is not independent of the scheme universe.

Searches made before writing:

- `msearch.py ... leanfinder` for arbitrary products of surjective affine scheme
  morphisms: only `pointsPi_surjective_of_isAffine` and related partial results;
  no exact theorem.
- `msearch.py ... loogle` for `AlgebraicGeometry.Surjective,
  CategoryTheory.Limits`: no exact product theorem (one query also reported an
  unknown identifier in the service).
- `msearch.py ... grep` for `infinite-product-surjective|product.*surjective`:
  no declaration of the arbitrary scheme-product result.
- `rg` over `WeilConjectures/` and `lean/Sheaf/` for the item and product
  surjectivity names: no existing exact statement; only the product-existence
  dependency and unrelated `pointsPi`/function-surjectivity results.
- Direct source inspection confirmed `exists_affine_infinite_product` has the
  cone, finite-affine-projection, and universal-property signature used here;
  Mathlib `AlgebraicGeometry.Surjective` is the exact underlying-point notion,
  and `AlgebraicGeometry.IsAffineHom` is the exact affine-morphism notion.

## Repair self-check

The returned packet required the stage-2 fix layout to use the module basename, the
item lean-record sidecar, and the item report basename.  I retained the delivered
module and statement, verified the lean record date against `date -u +%F` (2026-10-17), and added the
matching `lem-trf-infinite-product-surjective.lean-record.json` sidecar.  The item
node's mathematical fields and statement are unchanged.  The delivery tool
retains the maintainer-owned `created` metadata and excludes local edits to it.

## Second reading by Q118

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
