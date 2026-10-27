## Worker report

The module `Sheaf.AlgebraicGeometry.CommonRegularSurfaceResolution` states
`AlgebraicGeometry.exists_common_regular_surface_resolution`, with its proof `sorry`.
No definition is introduced or changed. The source read is Stacks Project,
`literature/stacks-project/resolve.tex`, Tag 0C5S,
`lemma-birational-regular-surfaces`, including its proof starting from the specified
rational map. The module docstring records the four steps of the node's proof.

The previous worker's note concerned an already reviewed stage-1 split by NI.
The current node has that split and review but no `lean` record. This delivery adds
the missing stage-2 statement; it does not resubmit the split.

Hypotheses, individually:

- The base scheme is `S : Scheme.{u}`. `[IsNoetherian S]` means precisely
  locally Noetherian and quasi-compact: the Mathlib class extends
  `IsLocallyNoetherian S` and `CompactSpace S`.
- The two schemes are `T₁ T₂ : Scheme.{u}`. Their integrality is
  `[IsIntegral T₁] [IsIntegral T₂]`, including nonemptiness.
- Their structural maps are the explicit morphisms `s₁ : T₁ ⟶ S` and
  `s₂ : T₂ ⟶ S`. Their properness is `[IsProper s₁] [IsProper s₂]`.
  Explicit maps are useful here because the conclusion compares several maps over S.
- Regularity is `hT₁ : IsRegularScheme T₁` and `hT₂ : IsRegularScheme T₂`.
  This uses the dependency's locally Noetherian, stalkwise regular predicate.
- Dimension two is `hdim₁ : topologicalKrullDim T₁ = 2` and
  `hdim₂ : topologicalKrullDim T₂ = 2`, with dimension in `WithBot ℕ∞`.
- The open subschemes are `U₁ : T₁.Opens`, `U₂ : T₂.Opens`, represented by
  `U₁.toScheme`, `U₂.toScheme` and their canonical open immersions `U₁.ι`, `U₂.ι`.
  Density is exactly `hU₁ : Dense (U₁ : Set T₁)` and the analogous `hU₂`.
- The given isomorphism is `α : U₁.toScheme ≅ U₂.toScheme`.
  Its being over S is the equality
  `hα : α.hom ≫ U₂.ι ≫ s₂ = U₁.ι ≫ s₁`.

Conclusions, individually:

- `∃ (W : Scheme.{u}) (w : W ⟶ S)` supplies the common S-scheme.
- `IsRegularScheme W ∧ IsIntegral W` gives exactly its requested regularity
  and integrality. No dimension, properness, or extra conclusion about W is imposed.
- `q₁ : W ⟶ T₁`, `q₂ : W ⟶ T₂` are the two maps.
  `q₁ ≫ s₁ = w` and `q₂ ≫ s₂ = w` say both are over S.
- For each q there is an existing `OrdinaryBlowupTower Tᵢ` and an isomorphism
  `e : W ≅ A.level (Fin.last A.length)`. The equality
  `e.hom ≫ A.toBase (Fin.last A.length) = qᵢ` identifies the actual map with
  the tower composite, up to the required identification of its top.
  The tower's `initial` identifies its level zero with Tᵢ; `blowupIso` and
  `blowup_fac` identify each transition with the actual global blowup map.
- Every center satisfies
  `∃ (p : A.level i.castSucc) (hp : IsClosed ({p} : Set _)),
  A.center i = Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩`.
  This specifies the reduced closed point, not an arbitrary ideal supported at p.
  Mathlib's `vanishingIdeal` docstring explicitly identifies its quotient with
  the reduced induced closed subscheme.
- The finite towers are over S without extra data or assumptions: at every level
  use `A.toBase i ≫ sᵢ`. The tower's transition composition laws and the equalities
  for qᵢ make all maps and both top isomorphisms compatible with w.
- The final existential gives a dense open `V : W.Opens`, an inclusion
  `hV : V ≤ q₁ ⁻¹ᵁ U₁`, and the equality
  `q₁.resLE U₁ V hV ≫ α.hom ≫ U₂.ι = V.ι ≫ q₂`.
  This is precisely agreement with the supplied birational identification on a
  dense domain where it is defined. The tower composites are birational, so this
  equality identifies their induced birational map with α, not an unspecified map.

Dependency declarations read and used:

- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`, and its `IsNoetherian` class extending
  this class and `CompactSpace` (lines 57 and 280).
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsIntegral` (line 240), including its nonempty field.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper` (line 42).
- `def-weil-regular-scheme`: `Sheaf.AlgebraicGeometry.IsRegularScheme`,
  `AlgebraicGeometry.IsRegularScheme`, whose definition is
  `IsLocallyNoetherian X ∧ IsRegular X`. Also read the upstream `IsRegular` class
  in `WeilConjectures.AlgebraicGeometry.Regular`, with its stalkwise field.
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`,
  `topologicalKrullDim` (line 39).
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion` (line 38), used through canonical open
  subschemes and their immersions. The restriction equality uses the actual
  `Scheme.Hom.resLE` of `Mathlib.AlgebraicGeometry.Restrict` (line 775).
- `def-nagata-global-blowup`: `WeilConjectures.Blowup.Gluing`,
  `Scheme.IdealSheafData.blowup` and `blowupMap` (lines 255 and 260), used in
  the tower's definition. No new blowup construction is introduced.
- Added the already landed node `def-trf-ordinary-resolution-rule` to stmt_deps
  to use its auxiliary declaration `AlgebraicGeometry.OrdinaryBlowupTower`
  and `OrdinaryBlowupTower.toBase` in `Sheaf.AlgebraicGeometry.OrdinaryResolutionRule`
  (lines 48 and 63). Read the node's full record and the module's definitions.
  This tower is defined for every scheme; the rational-field restrictions on the
  separate `RationalResolutionInput` and `SmoothFunctorialOrdinaryResolution`
  are not used. Its transition data just express finite composition.
  Source: ILO VIII 2.1.4, as recorded in the existing definition node. A source-only
  dependency traversal found no path from this added dependency back to the item.

The proof-only dependencies for finite-type Noetherianity, proper composition,
and proper-over-separated are already supplied by the imported Mathlib Noetherian
and Proper modules. Their signatures were read. The two surface resolution and
factorization proof dependencies currently have no Lean records; their proof plans
remain in the theorem docstring. They are not needed to type this statement.
Every available statement/proof-dependency module is imported.

Edge cases checked before delivery:

- A zero-length tower has no centers, and its top is isomorphic to its base via
  `initial`; the composite condition therefore permits all isomorphisms, not only
  literal identity maps. In particular an already given global isomorphism allows
  two length-zero towers, including when the specified map is not the identity.
- An integral scheme is nonempty. A dense open of either input is therefore
  nonempty; the open V in integral W is likewise nonempty. Agreement is not vacuous.
- Empty S has no integral schemes mapping to it, just as in the source; it is not
  artificially excluded. Zero-dimensional and one-dimensional inputs are excluded
  exactly by the two dimension-two hypotheses.
- Fields of arbitrary characteristic and non-field bases are allowed. No smoothness,
  excellence, equal-characteristic or rational-field assumption is imposed.
- Universes are explicit (`universe u`, `Scheme.{u}`); the theorem introduces no test
  objects in an independently smaller universe. Both auto-implicit options are off.

Searches actually run for this item:

- `msearch.py ... leanfinder` with query “Two proper regular integral surfaces
  birational over a Noetherian base have a common resolution by blowups of reduced
  closed points”: eight hits on rational maps and normalization, no common resolution.
- `msearch.py ... loogle` with query `"AlgebraicGeometry", "blowup"`: zero hits.
- `msearch.py ... grep` with query
  `point.*[Bb]lowup|[Bb]lowup.*[Tt]ower|[Cc]ommon.*[Rr]esolution` in
  `AlgebraicGeometry`: zero Mathlib hits.
- `msearch.py ... leansearch` with query “Two proper regular integral surfaces have
  a common resolution of a specified birational map by blowups at closed points”:
  eight hits (proper composition, properness, rational maps), no common resolution.
- `rg` in `lean/WeilConjectures` for
  `common.*[Rr]esolution|regular.*surface|surface.*regular|OrdinaryBlowupTower`
  found unrelated derived resolutions and regular-local-surface results.
  A grep for the item's exact blueprint id found nothing there.
- `rg` in `lean/Sheaf` for the item id and common-resolution/point-blowup names found
  the separate regular point blowup geometry theorem, not this theorem.
  A further tower search found the reusable `OrdinaryBlowupTower`; its signature
  and docstrings were read instead of introducing a second tower definition.
- A DAG search for finite sequences of point blowups found the current item and
  separate factorization/resolution statements. `blueprint_refs.py search 'point blowup'`
  returned zero blueprint matches; `ancestor` reports inherited `from.node = None`.
- A final exact-name search in project Lean and `dag/lean_names_upstream.json` found
  no existing `exists_common_regular_surface_resolution` declaration.

No statement correction, disputed mathematical statement, new node, or dependency
module is needed. The inherited missing blueprint ancestor is unchanged. The only
node changes are `lean` and the addition of the existing tower node to `stmt_deps`.

Validation: `scompile.py Q22 lem-sfb-common-regular-surface-resolution` compiled
the module in sandbox and library modes on the server without errors or warnings.

## Second reading by Q22

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
