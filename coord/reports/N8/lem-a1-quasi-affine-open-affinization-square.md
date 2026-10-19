## Worker report

This stage-2 delivery adds the module
`Sheaf.AlgebraicGeometry.QuasiAffineOpenAffinizationSquare` and the statement
`AlgebraicGeometry.Scheme.isPullback_toSpecΓ_of_isOpenImmersion`. The theorem has
one postponed proof (`sorry`), as required for a statement node; no definitions
with postponed data are introduced. The copied DAG node is unchanged except for
its `lean` record.

The node's hypotheses and clauses render as follows:

- The schemes are explicit `{U V : Scheme.{u}}`, with the universe `u` bound.
- The morphism is `(u : U ⟶ V)`, and its open-immersion hypothesis is the typeclass
  `[IsOpenImmersion u]`, using Mathlib's `AlgebraicGeometry.IsOpenImmersion`.
- Quasi-affineness of both schemes is `[U.IsQuasiAffine] [V.IsQuasiAffine]`, the
  Mathlib notion of quasi-compact immersion into the spectrum of global sections,
  equivalent here to the quasi-affine condition in the node.
- The top arrow `j_U` is `U.toSpecΓ`.
- The left arrow `id_U` is `(𝟙 U)`.
- Restriction `r : Γ(V, O_V) → Γ(U, O_U)` is `u.appTop`, and the right arrow
  `Spec r` is `Spec.map u.appTop`.
- The bottom arrow `j_V ∘ u` is `u ≫ V.toSpecΓ` (Lean category composition).
- The cartesian assertion is exactly
  `IsPullback U.toSpecΓ (𝟙 U) (Spec.map u.appTop) (u ≫ V.toSpecΓ)`.
  This is the four-arrow categorical formulation of the node's equivalent
  inverse-image-open and identity-on-
  `U` formulation; no extra conclusion or hypothesis is added.

The recorded statement dependencies were read as follows and the corresponding
interfaces were used:

- `def-weil-open-immersion`: Mathlib module
  `Mathlib.AlgebraicGeometry.OpenImmersion`, declaration
  `AlgebraicGeometry.IsOpenImmersion`.
- `def-pc-scheme`: Mathlib module `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `lem-weil-pbc-morphism-into-affine-scheme`: Mathlib's
  `AlgebraicGeometry.ΓSpec.adjunction`/`ΓSpec.homEquiv` interface, together with
  the canonical global-section map `Scheme.Hom.appTop` (this dependency has no
  separate Lean record because its node is recorded as a Mathlib leaf).
- `def-weil-affine-spectrum`: Mathlib module `Mathlib.AlgebraicGeometry.Scheme`,
  declarations `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`.
- `def-pc-fibre-product`: Mathlib module
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, declaration
  `CategoryTheory.Limits.pullback`; the theorem uses its `IsPullback` API.

The module imports `Mathlib.AlgebraicGeometry.QuasiAffine`, which supplies the
quasi-affine canonical map, open-immersion instance, spectrum map, and pullback
interfaces. Every variable and universe is explicit; there are no local
notations, private copies, `let` binders, or extra assumptions.

Before writing the statement I checked the empty scheme, the identity open
immersion `U = V`, and the empty open immersion. The formulation has no
nonemptiness, separatedness, finite-type, or characteristic hypothesis beyond
the recorded quasi-affine and open-immersion classes, so those edge cases remain
included. The restriction map is the canonical `appTop`, including the identity
case; it is not replaced by an arbitrary ring map.

Searches made:

- `msearch.py ... leanfinder "Cartesian square for open immersion between quasi affine schemes"`:
  hits included `Scheme.isPullback_toSpecΓ_toSpecΓ` and
  `Scheme.instIsOpenImmersionToSpecΓOfIsQuasiAffine`, but the former requires an
  affine morphism and has a different square, so it is not this statement.
- `msearch.py ... loogle "IsOpenImmersion, toSpecΓ"`: only the canonical
  quasi-affine open-immersion instance; no matching open-subscheme square.
- `msearch.py ... leansearch "An open immersion between quasi affine schemes induces a cartesian square with U and its two affinizations"`:
  generic immersion and pullback hits, but no exact theorem.
- `msearch.py ... grep "isPullback_toSpecΓ_toSpecΓ|preimage_opensRange_toSpecΓ" AlgebraicGeometry`:
  the Mathlib quasi-affine theorem was found and rejected as a mismatch because it
  assumes `IsAffineHom` and uses the affine-morphism pullback square.
- `rg` over `WeilConjectures/` and shared `lean/Sheaf` found no declaration for
  this node or an equivalent open-immersion affinization square. The exact node id
  was also absent from the upstream source.

No new definition nodes, dependency repairs, statement correction, or
`STATEMENT-DISPUTED` flag is needed.

## Second reading by N8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
