## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleFinitePushforwardUnitEdgeCompatibility` states
`AlgebraicGeometry.Etale.cohomology_baseChange_unit_edge_compatibility`, with proof `sorry`.
It introduces no definitions. The item node is changed only in `lean`.

Source read: Stacks Project, Etale Cohomology, Tag 09ZE, label
`lemma-efface-cohomology-on-closed-by-finite-cover`, second paragraph of its proof:
the finite-pushforward cohomology identification followed by the choice of `Y' → Y`
and the morphism `f_* M → f'_* M`. The literature file is absent in this clone;
I read the local Stacks copy `c1-stacks-review/etale-cohomology.tex`, lines 14900–14965.
The node explicitly formulates the implicit compatibility for arbitrary morphisms;
the source's finiteness, constructibility and torsion assumptions concern the
surrounding effacement argument, not this formal compatibility.

Hypotheses and clauses, matched individually:

- Schemes and morphisms `f : Y → X`, `π : Y' → Y`, `i : Z → X`:
  `{X Y Y' Z YZ YZ' : Scheme.{u}}` and the explicit morphism binders.
  The composite `f' = f ∘ π` is written directly as `π ≫ f` throughout.
- The abelian sheaf `G` on the small étale site of `Y` is
  `G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}`.
- `YZ = Y ×_X Z`, with projections `iY, fZ`, is represented by
  `sq : IsPullback iY fZ f i`. Likewise `YZ' = Y' ×_X Z`, with projections
  `iY', fZ'`, is `sq' : IsPullback iY' fZ' (π ≫ f) i`.
  These binders permit every cartesian representative, including the chosen
  `pullback` from def-pc-fibre-product, with its specified comparison isomorphism.
  This is the same representation as the dependency's `cohomology_edgeMap_baseChange`.
- The induced `πZ` is the explicitly bound morphism `πZ : YZ' ⟶ YZ`.
  Its first projection equation is `sqπ : CommSq iY' πZ π iY`, whose `.w` is
  `iY' ≫ π = πZ ≫ iY`; its second is `hZ : πZ ≫ fZ = fZ'`.
  The universal property of `sq` says these two equations specify exactly the
  induced morphism `π ×_X id_Z`; no additional property of `πZ` is assumed.
- The comparison θ for each cartesian square is the recorded `squareUpperStarIso`
  built into `baseChangeMap` using `sq.toCommSq` and `sq'.toCommSq`.
  Its definition uses precisely the composition comparisons in the node.
- Each `Φ` is expanded, with no local notation or new definition: the innermost
  `Sheaf.H.map (baseChangeMap …).app … q` is `H^q(Ex^0)`; the next
  `cohomologyMap fZ … q` (or `fZ'`) is pullback of the pushed-forward sheaf;
  the outer `Sheaf.H.map (…counit.app …) q` completes the edge map.
  `AddMonoidHom.comp` follows the usual function-composition order.
- The sheaf morphism `u` is explicitly
  `(lowerStar … f).map ((upperStarLowerStarAdjunction … π).unit.app G) ≫
  (lowerStarComp … π f).hom.app ((upperStar … π).obj G)`.
  Upstream `lowerStarComp.hom` is the identification from `f_* π_*` to
  `(π ≫ f)_*`, that is the inverse of the node's `d`.
  Applying `(upperStar … i).map` and then `Sheaf.H.map … q` gives `H^q(i^{-1}u)`.
- κ is `(squareUpperStarIso … sqπ).hom.app G`. Its source is
  `πZ^{-1} iY^{-1} G` and its target is `iY'^{-1} π^{-1} G`.
  Upstream `upperStarComp` has direction opposite the node's `c`.
  Thus this square comparison is exactly `c_{π,iY'}^{-1} ∘ c_{iY,πZ}`,
  transporting across `sqπ.w`; the `.hom`, not `.inv`, has the required direction.
- For every `q ≥ 0`, the binder is `q : ℕ`. The displayed equality of additive
  homomorphisms is exactly `Φ₂.comp (H^q(i^{-1}u)) =
  (H^q(κ)).comp (πZ^*.comp Φ₁)`. Both maps have source
  `H^q(Z, i^{-1}f_*G)` and target `H^q(YZ', iY'^{-1}π^{-1}G)`.
- No finiteness hypothesis appears. The identity base change is not excluded.
  The parenthetical intended proof is represented by the declaration docstring's
  eight steps, following the node's actual split proof rather than adding a clause.

Dependency declarations read and used (all are supplied transitively by the one used
import `WeilConjectures.SixFunctors.BaseChange.Square`):

- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `Scheme.Hom`, lines 35–76.
- def-weil-pbc-abelian-etale-sheaves: `Mathlib.CategoryTheory.Sites.Sheaf`,
  `CategoryTheory.Sheaf`, lines 294–302, with `Scheme.smallEtaleTopology`.
- def-pc-fibre-product: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `pullback`, `pullback.fst`, `pullback.snd`, lines 93–116. Cartesian representatives
  are expressed by Mathlib `IsPullback`, as in the recorded edge-map dependency.
- def-weil-pbc-cartesian-square and def-weil-pbc-underived-exchange:
  `WeilConjectures.SixFunctors.BaseChange.Square`,
  `AlgebraicGeometry.Etale.squareUpperStarIso` and `baseChangeMap`, lines 73–89.
- def-weil-pbc-inverse-image, def-weil-pbc-direct-image,
  lem-weil-pbc-inverse-image-composition:
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
  `upperStar`, `lowerStar`, `upperStarLowerStarAdjunction`, `lowerStarComp`,
  `upperStarComp`, lines 156–163, 217–232, 249–254, 305–332;
  identity and unit coherence signatures were also read in `UpperLowerStar.Coherence`.
- def-weil-pbc-cohomology-pullback:
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`,
  `cohomologyMap`, full section binders and signature/docstring, lines 173–210.
- lem-weil-pbc-edge-map-base-change:
  `Sheaf.AlgebraicGeometry.EtaleEdgeMapBaseChange`,
  `cohomology_edgeMap_baseChange` and `bijective_edgeMap_baseChange` were read in full;
  their expanded edge-map expressions are used here. These theorem declarations are
  proof inputs for stage 3, not extra hypotheses or needed imports for this signature.
- lem-weil-pbc-cohomology-pullback-functorial:
  `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`,
  `cohomologyPullbackFunctorial` was read in full; naturality/composition are proof
  inputs, and the signature directly uses the same recorded `cohomologyMap`.

Edge cases checked before writing: `q = 0`; zero sheaf; empty schemes/fibre products;
`Z = X, i = id`; identity `π`; non-finite `f` or `π`. The identity remains meaningful
in each case. There is one explicitly bound scheme universe `u`, with abelian
coefficients in `u + 1` as in every recorded dependency. No auto-implicit variables,
local instances, private notions, `let` binders, or hollow data are introduced.
No mathematical counterexample or ambiguity requiring statement correction was found.

Searches actually run:

- msearch LeanFinder: "Base changed cohomology edge maps carry the direct image of the
  unit of a composite to cohomology pullback": eight group-cohomology functoriality
  hits, including `groupCohomology.H1π_comp_map`, none for étale sheaves or this identity.
- msearch Loogle: "Adjunction.unit, NatIso": zero hits, unknown identifier
  `Adjunction.unit` (query rejected; not evidence of absence).
- msearch LeanSearch: "cohomology edge map base change direct image adjunction unit
  compatibility": unavailable, Internal Server Error.
- msearch grep: "edgeMap|cohomologyMap|baseChangeMap" in `CategoryTheory`: zero hits.
- rg in upstream `WeilConjectures/SixFunctors` for
  `unit.*cohomology|cohomology.*unit|cohomologyMap.*comp|edgeMap`: found
  `cohomologyMap_eq_map_counit_comp`, `map_counit_cohomologyMap` and Gabber's
  functoriality lemmas. The former is the unit/edge factorization for one morphism,
  not the two-square compatibility stated by this node.
- rg by the exact item ID in upstream `WeilConjectures`: no match.
- rg for `cohomology_baseChange_unit_edge_compatibility|unit.*edge.*compatibility`
  in Mathlib, upstream and `lean/Sheaf`: no match on the base.
- rg for `cohomologyMap|baseChangeMap|upperStarComp` in `lean/Sheaf/AlgebraicGeometry/Etale*`:
  found the dependency modules and unrelated continuity/exchange statements;
  no declaration states this compatibility.
- `tools/lean_names_upstream.py show` for the item: no attached item declaration.

Validation: the server single-file compile passed in 3.5 seconds, with no warnings.
The first compile caught the reversed κ comparison; replacing `.inv` by `.hom`
restored the exact source and target required by the node. The theorem proof is `sorry`.

## Second reading by P1

I read the node statement clause by clause against
`Sheaf/AlgebraicGeometry/EtaleFinitePushforwardUnitEdgeCompatibility.lean`.

* Objects and hypotheses. The Lean binders `{X Y Y' Z YZ YZ' : Scheme.{u}}`,
  `f`, `π`, and `i` render the three scheme morphisms. `G :
  Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}` is exactly the abelian étale
  sheaf on `Y`. The four projections `iY`, `fZ`, `iY'`, `fZ'`, the induced map
  `πZ`, pullback witnesses `sq` and `sq'`, commutative-square witness `sqπ`, and
  equation `hZ` render the two cartesian squares and the two equations for
  `πZ`. The composite `π ≫ f` is used everywhere the node writes `f'`; no extra
  finiteness, separatedness, Noetherian, or characteristic assumption is present.

* Conclusion. The left nested composition is `Φ` for `sq'` with `π⁻¹G`,
  followed by `H.map` of `i⁻¹u`; the right nested composition is `H.map κ`,
  cohomological pullback along `πZ`, and `Φ` for `sq` with `G`. The displayed
  additive-hom equality has exactly the source and target in the node. `q : ℕ`
  covers every `q ≥ 0` (including `q = 0`). The unit is expanded as the
  `π` adjunction unit followed by `(lowerStarComp ... π f).hom`, and κ is
  `squareUpperStarIso sqπ).hom`, which has the node's direction
  `πZ⁻¹ iY⁻¹G ≅ iY'⁻¹π⁻¹G`.

* Edge cases. The statement remains typed for `q = 0`, zero sheaf, empty schemes
  and fibre products, identity `π`, and `Z = X` with `i = 𝟙 _`; no finiteness is
  imposed. The single universe `u` and coefficient universe `u + 1` match the
  dependency declarations and do not exclude the cases in the node.

* Existing-definition searches. I searched the upstream source and Mathlib with
  LeanFinder/Loogle/grep for the item name and for combinations of
  `cohomologyMap`, `edgeMap`, `baseChangeMap`, `unit`, and `compatibility`.
  Only generic pullback/pushforward composition and unrelated cohomology
  functoriality were found; no declaration states this theorem. The project
  `lean/Sheaf` search likewise found no duplicate.

No mismatch was found and no source or node correction was needed. The worker's
previous κ-direction repair (`.inv` to `.hom`) is correct and remains in the
module. The module contains no definitions, private notions, local notation,
extra hypotheses, or hollow data; the theorem proof is the permitted `sorry`.
The single-file server compile passed with no errors or warnings.
