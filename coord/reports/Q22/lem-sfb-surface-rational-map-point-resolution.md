## Worker report

Q22 stage 2: `Sheaf.AlgebraicGeometry.SurfaceRationalMapPointResolution` states
`AlgebraicGeometry.exists_surface_rational_map_point_resolution`, with its proof `sorry`.
Source read: Stacks resolve.tex, Tag 0C5H, lemma-extend-rational-map-blowing-up and its
proof; the regularity input is Tag 0AGR, as in the node's reviewed ten-step proof.
The source statement and the node's statement are unchanged. This is a stage-2 delivery;
the already reviewed Q41 stage-1 split is retained verbatim.

Hypothesis and conclusion correspondence:

- The base and schemes are `(S X Y : Scheme.{u})`. The two structural morphisms are
  `sX : X ⟶ S` and `sY : Y ⟶ S`.
- Integral X is `[IsIntegral X]`. Regular X is `hX : IsRegularScheme X`, which is the
  recorded locally Noetherian, stalkwise-regular predicate, with no separation condition.
- Noetherian X is `[IsNoetherian X]`: Mathlib's class extends `IsLocallyNoetherian X`
  and `CompactSpace X`, exactly the node's locally Noetherian and quasi-compact convention.
- Dimension two is `hdim : topologicalKrullDim X = 2`.
- The proper relative target is `[IsProper sY]`; neither S nor sX has an extra property.
- The specified dense open is `U : X.Opens`, `hU : Dense (U : Set X)`.
  `U.toScheme` and `U.ι` are its open subscheme and inclusion.
- The given morphism is `f : U.toScheme ⟶ Y`, and its S-morphism condition is
  `hf : f ≫ sY = U.ι ≫ sX`, using exactly the commuting-triangle meaning of
  `Scheme.Hom.IsOver` from the recorded over-base interface.
- The existential `A : OrdinaryBlowupTower X` supplies a natural length, all intermediate
  schemes, an identification of level zero with X, all transition morphisms and their
  composition laws, and the specified blowup isomorphisms over each previous level.
  No rational-input or characteristic-zero condition is used: that is a separate
  structure in the same existing module.
- At each `i : Fin A.length`, the existential point `p` has closed singleton `hp`, and
  `A.center i = Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩`. Mathlib's docstring
  explicitly identifies this ideal's quotient with the reduced induced subscheme.
  `A.toBase i.castSucc p ∉ U` places every centre outside the inverse image of U.
- The universal quantifier over `Fin (A.length + 1)` states integrality, regularity,
  Noetherianity and dimension two separately at every level, including both endpoints.
- `A.toBase (Fin.last A.length)` is exactly the composite p of the tower, as defined
  by the recorded `OrdinaryBlowupTower.toBase`. `IsProper` gives properness of p.
- `IsIso (A.toBase (Fin.last A.length) ∣_ U)` says p is an isomorphism over U.
- The existential g has source the last level. Its S-morphism equation is
  `g ≫ sY = A.toBase (Fin.last A.length) ≫ sX`, with each intermediate S-structure
  given by composition of its toBase map with sX.
- The final equality compares morphisms on the entire inverse image of the original U:
  `(p ⁻¹ᵁ U).ι ≫ g = (p ∣_ U) ≫ f`. It does not shrink the agreement domain.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- Mathlib.AlgebraicGeometry.Noetherian: `IsLocallyNoetherian`, `IsNoetherian`.
- Mathlib.AlgebraicGeometry.Properties: `IsIntegral`.
- Sheaf.AlgebraicGeometry.IsRegularScheme: `AlgebraicGeometry.IsRegularScheme`.
- Mathlib.Topology.KrullDimension: `topologicalKrullDim`.
- Mathlib.AlgebraicGeometry.Morphisms.Proper: `IsProper`.
- Mathlib.AlgebraicGeometry.OpenImmersion: `IsOpenImmersion`; the given open is
  represented by Mathlib's existing `Scheme.Opens`, `toScheme` and `ι`.
- WeilConjectures.Blowup.Gluing: `Scheme.IdealSheafData.blowup`, `blowupMap`.
- Mathlib.AlgebraicGeometry.Over: `Scheme.Over`, `Scheme.Hom.IsOver` and its
  commuting-triangle signature. Structural maps and triangles are written explicitly.
- Sheaf.AlgebraicGeometry.OrdinaryResolutionRule: `OrdinaryBlowupTower` and
  `OrdinaryBlowupTower.toBase`; the landed owning node
  `def-trf-ordinary-resolution-rule` is added to stmt_deps to reuse these declarations.
  There is no new definition and no dependency-interface replacement.
- Mathlib.AlgebraicGeometry.IdealSheaf.Basic: `Scheme.IdealSheafData.vanishingIdeal`.

All available recorded proof-dependency modules are imported privately, including
RegularPointBlowupGeometry, the regular-local DVR criterion, and the partial-section
scheme-image theorem. The valuation-point extension and point-blowup domination nodes
currently have no recorded Lean module, so no import can yet be named for them. Their
mathematical roles are preserved in the full ten-step proof docstring.

Edge cases checked before writing: U = X permits length zero and g = f; length zero
has a singleton level index and empty stage index, so none of the level assertions
vanishes. The empty scheme and empty dense domain cannot occur under integrality and
dimension two. Arbitrary residue fields and all characteristics are allowed. There is
no separation assumption on X or S, and no Noetherian assumption on S or Y. The tower
initial isomorphism expresses X_0 = X up to identification, consistently with the
existing common-surface-resolution consumer. The fixed universe is the same general
scheme universe used by the recorded blowup construction, without additional size
constraints. No disputed statement or source correction was needed.

Searches actually run:

- msearch.py leanfinder: "Extend a rational map from a regular Noetherian surface to a
  proper scheme by finitely many point blowups"; eight hits on rational maps and their
  representatives, no point-blowup resolution theorem.
- msearch.py loogle: `"RationalMap", "AlgebraicGeometry"`; twelve hits defining
  rational maps, representatives and the IsOver predicate, no resolution statement.
- msearch.py grep: `point.*blow|blow.*point|resolv.*rational`, AlgebraicGeometry;
  zero Mathlib hits.
- rg on lean/Sheaf and lean/WeilConjectures for
  `PointBlowup|pointBlowup|BlowupTower|blowupTower|blowup.*tower|blowup.*Tower|surface.*resolution|surface_rational`:
  found the existing ordinary tower and CommonRegularSurfaceResolution, whose theorem
  is a consumer rather than a statement of this item. No exact theorem was found.
- rg for this item's id in the two source roots found only its mention in the common
  resolution proof docstring. rg in dag/lean_names_upstream.json for the new theorem
  name and OrdinaryBlowupTower found no upstream duplicate.

Validation: every Lean file is checked with the required scompile.py server wrapper;
only the expected sorry warning is permitted. The delivery is checked by deliver2.py
--no-push before the push. Independent mathematical review is left to the maintainer,
as required by the dispatcher brief; no second-reader review is claimed here.

## Second reading by Q22

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
