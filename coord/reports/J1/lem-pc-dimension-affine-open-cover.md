## Worker report

The module states `AlgebraicGeometry.Scheme.dim_eq_iSup_ringKrullDim_of_affineOpenCover`.
It says that the dimension defined by local-ring Krull dimensions is the supremum of the
Krull dimensions of the rings of an arbitrary affine open cover. Its proof is `sorry`.

Statement correspondence:

- The nonempty scheme `X` is `(X : Scheme.{u}) [Nonempty X]`. `Scheme` is the Mathlib
  locally ringed scheme of `def-pc-scheme`.
- An arbitrary family indexed by `I` is `{I : Type v} (U : I → X.Opens)`. Each `U i` is an
  open subscheme by the `Scheme.Opens.toScheme` coercion.
- The cover `X = ⋃ i, U i` is `(hcover : ⨆ i, U i = ⊤)` in the lattice of opens.
- The commutative rings are `(A : I → CommRingCat.{u})`; the scheme isomorphisms to their
  spectra are `(hiso : ∀ i, (U i : Scheme.{u}) ≅ Spec (A i))`.
- The node's `dim X`, the supremum of local-ring Krull dimensions, is `X.dim` from
  `Sheaf.AlgebraicGeometry.Dimension`.
- The equality and every summand of its right side are
  `X.dim = ⨆ i, ringKrullDim (A i)`. Both sides have type `WithBot ℕ∞`, covering bottom,
  finite values, and infinity. `ringKrullDim` is the Mathlib declaration for
  `def-weil-pbc-krull-dimension-ring`.

Dependency declarations read and used: `AlgebraicGeometry.Scheme` in
`Mathlib.AlgebraicGeometry.Scheme` (`def-pc-scheme`);
`AlgebraicGeometry.Spec` in `Mathlib.AlgebraicGeometry.Scheme`
(`def-weil-affine-spectrum`); `AlgebraicGeometry.Scheme.dim` in
`Sheaf.AlgebraicGeometry.Dimension` (`def-pc-dimension`); and `ringKrullDim` in
`Mathlib.RingTheory.KrullDimension.Basic` (`def-weil-pbc-krull-dimension-ring`).

Edge cases: `I` is any type, including the empty type; `hcover` excludes an empty cover
of a nonempty scheme. An individual `U i` may be empty, for which an isomorphism to
`Spec (A i)` forces the zero ring and `ringKrullDim (A i) = ⊥`. The theorem imposes no
finite dimension, Noetherian, reducedness, characteristic, or finite-index restriction.
The source hypotheses do not ask for such restrictions. The official Stacks text at
Tags 04MU, 01HV, and 00KG was checked; the local `literature/stacks-project/` checkout
is absent on this machine.

Searches for an existing exact declaration:

- `msearch.py ... leanfinder "dimension of a scheme equals supremum of Krull dimensions
  of rings of an affine open cover"`: eight hits, including affine-cover declarations and
  the dimension of a single prime spectrum; no equality over a cover.
- `msearch.py ... loogle "Scheme.dim, ringKrullDim, IsAffineOpen"`: zero hits; `Scheme.dim`
  is project-local and unknown to the remote Loogle index.
- `msearch.py ... grep "ringKrullDim|topologicalKrullDim" AlgebraicGeometry`: nine hits,
  including `ringKrullDim_stalk_eq_coheight`; none states this cover equality.
- `rg` in `WeilConjectures` and `lean/Sheaf` for `affine.*[Dd]im`, `dim.*affine`,
  `iSup.*ringKrullDim`, and `ringKrullDim.*iSup`: found the dimension of one affine open
  and topological dimension bounds, but not this statement using `Scheme.dim`.
- `grep -rn "lem-pc-dimension-affine-open-cover"` in `WeilConjectures`: no hit.
- Exact-name `rg` in Mathlib and `WeilConjectures`: no hit.

The server compiler accepted the file without errors or warnings.

## Second reading by J1

I read the node and the Lean file independently, with the dependency signatures and Stacks
Tags 04MU, 01HV, and 00KG open. Item-by-item correspondence:

- A nonempty scheme `X`: `(X : Scheme.{u}) [Nonempty X]`. Mathlib's `Scheme` is the
  locally ringed scheme of `def-pc-scheme`; the instance is exactly the node's
  nonemptiness hypothesis. Verdict: exact.
- An arbitrary indexing set `I` and family of open subschemes `U_i`: `{I : Type v}`
  and `(U : I → X.Opens)`, with `(U i : Scheme.{u})` the open subscheme. Verdict: exact;
  `Type v` allows any small index type, without a finiteness or inhabitedness condition.
- The union equals `X`: `(hcover : ⨆ i, U i = ⊤)`. Supremum in `X.Opens` is union of
  opens. Verdict: exact.
- Commutative rings `A_i` and isomorphisms `U_i ≅ Spec A_i`:
  `(A : I → CommRingCat.{u})` and
  `(hiso : ∀ i, (U i : Scheme.{u}) ≅ Spec (A i))`. `CommRingCat` permits the zero
  ring. `Spec` is the declaration cited by `def-weil-affine-spectrum`. Verdict: exact.
- The left-hand `dim X`: `X.dim` unfolds by `def-pc-dimension` to
  `⨆ x : X, ringKrullDim (X.presheaf.stalk x)` in `WithBot ℕ∞`. Verdict: exact.
- The right-hand supremum and equality:
  `X.dim = ⨆ i, ringKrullDim (A i)`. The cited ring-dimension node records
  Mathlib's `ringKrullDim`, also valued in `WithBot ℕ∞`. Verdict: exact; there is
  one equality and no other conclusion clause.

Edge cases: `I` can be empty, although `hcover` and `[Nonempty X]` then cannot both
hold. Individual `U i` can be empty; `hiso` then forces its spectrum to be empty,
so its ring is zero and its summand is bottom. The empty scheme is excluded exactly
as the node requests. Zero-dimensional rings, unbounded dimension, and every ring
characteristic remain possible. `u` and `v` are independent universes; the syntax
does not impose finite covers or Noetherian, reduced, or finite-dimension hypotheses.

Independent searches: LeanFinder for "dimension of scheme from arbitrary affine open
covering supremum of Krull dimensions" returned cover constructions but no dimension
equality. Loogle for `ringKrullDim, IsAffineOpen` returned zero hits (unknown
`IsAffineOpen`). The launcher grep for `dim.*affine.*cover|iSup.*ringKrullDim`
returned no relevant theorem. Direct `rg` of Mathlib's AlgebraicGeometry sources,
`WeilConjectures`, and `lean/Sheaf` for `dim_eq_iSup`, `iSup.*dim`, and
`ringKrullDim.*cover` found no exact declaration; the nearby source result concerns
topological dimension bounds. The dependencies' recorded declarations are usable,
and there are no new definition nodes or dependency modules. I found no mismatch
and made no change to the theorem or node.
