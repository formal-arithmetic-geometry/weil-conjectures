## Worker report

The new module `Sheaf.AlgebraicGeometry.SpaceEventuallyFlat` states
`AlgebraicGeometry.AlgebraicSpace.eventually_flat_of_isLimit`, with `sorry` as its
entire proof. It introduces no definition and proves nothing. The node's mathematical
statement and proof plan are unchanged. Its `lean` record is populated, and its
`stmt_deps` gains four already-landed definition owners needed by the signature:
`def-sfb-space-morphism-properties`, `def-sfb-proper-curve-moduli`,
`def-trf-scheme-algebraic-space`, and `def-sfb-space-sheaf-fibre-product`.
There are no new nodes, dependency repairs, or statement corrections.

Source read: `literature/stacks-project/spaces-limits.tex`, Situation 084W
(`situation-descent-property`, lines 1448–1457), and Tag 08K0
(`lemma-descend-flat`, lines 1751–1801). The last assertion descends flatness of a
locally finitely presented morphism; this node uses the stated finitely presented,
affine-base specialization. Its persistence clause is flat base-change stability
(03MO), already recorded in the node and the imported locality theorem.

The following gives every hypothesis and conclusion clause of the node its Lean
counterpart.

| Node clause | Lean rendering |
| --- | --- |
| Schemes and spaces over Spec Z | `D : Iᵒᵖ ⥤ Over (Spec (.of (ULift.{u} ℤ)))` and `X₀ : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))`. The lift puts the terminal integer spectrum in the same universe as the schemes; it does not change the base ring mathematically. |
| The size convention | Explicit `universe u`; `I : Type u`, schemes in `Scheme.{u}` and algebraic spaces with `Type u`-valued sheaves. The index is within the same smallness bound as the schemes, following the project's index-universe convention. All variables and universes are bound explicitly, with `autoImplicit false`. |
| Small nonempty directed set | `{I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]`. Antisymmetry, countability, and a least element are not assumed. |
| Inverse system of affine schemes | The functor `D` has opposite index category and `[∀ i : I, IsAffine (D.obj (op i)).left]`. |
| Affine transition morphisms | Every `(D.map a).left` is a morphism between affine schemes, hence affine by Mathlib's `isAffineHom_of_isAffine`. The condition follows from the affine-stage assumption and needs no separate redundant binder. No transition flatness, surjectivity, or injectivity is imposed. |
| T is the inverse limit, with its projections | `(c : Cone D) (hc : IsLimit c)`; `c.pt.left` is T, and `(c.π.app (op i)).left` is its projection. A limit cone in the category of schemes over the terminal integer spectrum is precisely the corresponding scheme limit with its unique structure morphism. Thus no separate choice of a base structure or limit is assumed. |
| Fixed stage i₀ | `(i₀ : I)`. |
| Algebraic space X₀ and morphism to Tᵢ₀ | `(X₀ : AlgebraicSpace ...) (f₀ : X₀ ⟶ schemeSpace (D.obj (op i₀)))`; `schemeSpace` is the actual represented sheaf of the stage scheme. |
| Finite presentation: local finite presentation on étale charts | The first conjunct `MapIsLocallyOfFinitePresentation f₀` of `hfp`. It uses Mathlib's scheme predicate on every compatible pair of étale scheme charts. |
| Finite presentation: quasi-compact | The second conjunct `MapIsQuasiCompact f₀.hom.hom` of `hfp`. This is the existing affine-scheme-test quasi-compactness predicate. |
| Finite presentation: quasi-separated, i.e. quasi-compact diagonal | The third conjunct `MapIsQuasiCompact (pullback.diagonal f₀.hom.hom)` of `hfp`, using the actual presheaf relative diagonal. |
| X and f are base change to T | `enlargedFibreProductFst (ObjectProperty.homMk ⟨yoneda.map (c.π.app (op i₀))⟩) f₀`, with an explicit type annotation for the map between represented schemes. This is the canonical projection from T ×_{Tᵢ₀} X₀ to T. The node writes the canonically symmetric fibre product X₀ ×_{Tᵢ₀} T; both represent the same compatible pairs, with the same projection to T. |
| Flatness tested on étale scheme charts; f flat | `hflat : MapIsFlat (...)`, where `MapIsFlat = MapIsLocally (@Flat)` uses the existing Mathlib scheme-flatness notion. |
| Some i ≥ i₀ | `∃ (i : I) (hi : i₀ ≤ i)`. |
| Every j ≥ i | `∀ (j : I) (hij : i ≤ j)`. Both the identity case and all later stages are included. |
| fⱼ is flat | `MapIsFlat (enlargedFibreProductFst (...) f₀)`, with the first map induced by `yoneda.map (D.map (homOfLE (le_trans hi hij)).op)`. Its domain is exactly `schemeSpace (D.obj (op j))`, and its codomain is the represented original stage. This is the specified canonical base change, not an arbitrary morphism with the same endpoints. |

Dependency declarations read and reused:

| Recorded node / role | Module and declarations |
| --- | --- |
| `def-pc-scheme`, `def-weil-affine-spectrum` | `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`; their signatures and docstrings were read. |
| `def-trf-algebraic-space` | `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`, the full subcategory with `IsAlgebraicSpace`; representability and étale atlas definitions were read. |
| `def-weil-size-convention` | This is explicitly recorded as a convention with no Lean declaration; the universes are bound in the theorem. |
| `def-pc-fibre-product` | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.fst`, `pullback.snd` and the relative diagonal. The existing space-fibre-product definition packages the sheaf pullback. |
| `def-sbc-locally-finite-presentation` | `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `AlgebraicGeometry.LocallyOfFinitePresentation`, through `MapIsLocallyOfFinitePresentation`. |
| `def-weil-flat-morphism` | `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, through `MapIsFlat`. |
| Added owner `def-sfb-space-morphism-properties` | `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`, `MapIsFlat`, `MapIsLocallyOfFinitePresentation`. |
| Added owner `def-sfb-proper-curve-moduli` | `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapIsQuasiCompact` on presheaf morphisms, including the relative diagonal. No curve-family condition is assumed. |
| Added owner `def-trf-scheme-algebraic-space` | `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`. |
| Added owner `def-sfb-space-sheaf-fibre-product` | The same module: `enlargedFibreProduct`, `enlargedFibreProductFst`; their data is the actual sheaf pullback and projection. |

The two modules providing the space predicates and canonical constructions are public
imports. Their public imports expose the other statement definitions; there is no local
replacement. The other public imports supply affine morphisms, preorder categories,
and limiting cones. All seven proof dependencies have their available modules imported
without `public`: the affine qcqs facts (Mathlib affine and quasi-separated modules),
`AlgebraicSpaceFlatProperFpLocality`, `QcMapAffineEtaleNeighbourhood`,
`AlgebraicSpaceFibreProductsEtaleCovers`, `LimitAffineTransition`, the affine-spectrum
fibre-product facts in Mathlib `Pullbacks`, and `DescendFlatFinitePresentation`.
The theorem docstring spells out all five steps of the node's proof, including the
field-valued lifting argument, scheme descent, and persistence.

Edge cases checked before writing: a singleton index (the conclusion is the given
flatness, transported through the identity pullback); a directed preorder without a
least element or antisymmetry (only the chosen i₀ and transitivity are used in the
signature); j = i (reflexive inequalities are permitted); an empty X₀ (all its base
changes are empty and flat); empty affine stages and an empty limit (no Nonempty
assumption is placed on any scheme or space); and arbitrary characteristic (the
integer base imposes none). Nonempty refers only to I. No stage flatness is assumed,
and finite presentation retains all three required conjuncts.

Searches for an existing statement (all through the prescribed search wrapper unless
otherwise stated):

- LeanSearch: `A finitely presented algebraic space flat after base change to an affine
  inverse limit is flat at some stage.` Result: 8 hits, including scheme/ring flat
  base-change stability and finite-presentation base change, but no algebraic-space
  inverse-limit statement.
- LeanFinder: `A finitely presented algebraic space flat over an affine inverse limit is
  flat at all sufficiently late stages`. Result: 8 hits about scheme flatness, affine
  local tests, universal openness and ring flatness; no exact statement.
- Loogle: `AlgebraicGeometry.Flat, AlgebraicGeometry.LocallyOfFinitePresentation`.
  Result: 12 hits, including universal openness and flat descent for schemes; none
  gives this statement for algebraic spaces.
- Mathlib wrapper grep: `eventually.*[Ff]lat|exists_flat_stage|algebraic.?[Ss]pace`
  in `AlgebraicGeometry`. Result: 0 hits.
- Direct `rg` in `lean/Sheaf/AlgebraicGeometry` and `lean/WeilConjectures` for
  `space.*(eventually|flat_stage)|eventually.*flat|MapIsFlat|MapIsLocallyOfFinitePresentation`.
  Result: the reusable space predicates, the analogous eventual-surjectivity and
  eventual-finiteness statements, and `AlgebraicGeometry.exists_flat_stage_of_limit`
  for schemes. The scheme statement does not cover a general algebraic-space source.
- `grep -rn 'lem-sfb-space-eventually-flat' lean/WeilConjectures`: no hits.
- Direct `rg` for `eventually_flat_of_isLimit` in Mathlib, `lean/WeilConjectures`,
  `lean/Sheaf` and `dag/lean_names_upstream.json`: no collision.
- The node records for the four added definition owners were read, and their recorded
  declaration docstrings and full signatures were opened in the existing Lean source.
  They supply exactly the notions needed, so no definition node is created.

No statement is disputed, and no node fault was found.

Validation: prescribed `scompile.py O4 lem-sfb-space-eventually-flat` compiled the
single delivered file as both sandbox and library module (1.6 seconds each), without
errors or warnings. All Lean lines have at most 87 characters. The only postponed
proof is the theorem named above. The prescribed `deliver2.py --no-push` dry run
reported OK: its commit passed the server preflight and compiled cleanly.

## Second reading by O4

Author's second reading, with the node and final Lean file reopened; the dispatch brief
prohibits starting another agent, and the maintainer supplies the independent review.
The base and index binders match the integer-base directed affine system. The cone's
universal property is in the over-category of the terminal base and therefore retains
the scheme limit. In particular there is no assumption that the algebraic-space
source itself is a scheme, and no transition flatness is introduced. The hfp conjunction
matches, in order, local finite presentation, quasi-compactness and quasi-compactness
of the relative diagonal. Reading the typed Yoneda maps verifies that the limit
pullback uses c.π at i₀ and the later pullback uses the map from j to i₀, with inequality
`le_trans hi hij`; the eventual quantifier covers every j ≥ i, including j = i.
The projections are actual sheaf fibre-product projections, in the opposite symmetric
order from the informal notation, with the base projection preserved. The definitions
are all reused and the four additional owner dependencies are recorded. No mismatch
was found and no mathematical statement was changed on this reading.
