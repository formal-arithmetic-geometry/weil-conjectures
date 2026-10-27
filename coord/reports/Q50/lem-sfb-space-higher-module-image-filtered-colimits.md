## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceHigherModuleImageFilteredColimits` defines
`AlgebraicGeometry.AlgebraicSpace.moduleHigherDirectImage` and states
`AlgebraicGeometry.AlgebraicSpace.isIso_moduleHigherDirectImage_filteredColimit`.
The theorem has exactly `sorry` as its proof. The definition has actual functor data.
No node statement is corrected, and there are no new nodes or dependency repairs.

Source read: `literature/stacks-project/spaces-cohomology.tex`, Tag 07U6,
`lemma-colimit-cohomology`, including its proof; and
`literature/stacks-project/sites-cohomology.tex`, Tag 03FD,
`lemma-cohomology-modules-abelian-agree`, including its proof. The former treats
abelian sheaves; the latter compares module and abelian cohomology naturally in
the coefficient, as required by the node's module formulation.

Clause-by-clause correspondence:

- Fixed sizes: `universe u`, `S : Scheme.{u}`, and `J : Type u` with
  `[SmallCategory J]`. The existing `SmallEtaleModel` is a small skeleton of the
  affine basis in precisely this universe. Module sections remain in `u` throughout.
  This follows the standing index-universe convention and imposes no equality on
  separately occurring site object and morphism universes: the original etale
  category remains in object universe `u+1` and morphism universe `u`.
- A scheme S, spaces X and Y over it, and their morphism are
  `{S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)`.
- Small etale structure sheaves and all their module sheaves are exactly `X.Modules`
  and `Y.Modules`, the recorded `ringedSiteModules`/`SheafOfModules` specialization.
- Quasi-compactness of f on every affine scheme test is
  `hqc : MapIsQuasiCompact f.hom.hom`. The definition literally asks for compactness
  of the point space of each affine-test fibre product.
- Quasi-separatedness is
  `hqs : MapIsQuasiCompact (pullback.diagonal f.hom.hom)`, using the relative diagonal.
- The small filtered category is `J`, `[SmallCategory J]`, `[IsFiltered J]`.
  Mathlib's `IsFiltered` includes nonemptiness, common upper objects and equalization
  of parallel arrows, equivalently the finite-diagram cocone condition.
- The diagram is `M : J ⥤ X.Modules`, without any quasi-coherence predicate.
- Every integer p >= 0 is encoded by `p : ℕ`, with no positivity assumption.
- Its colimit in all original module sheaves is `(c : Cocone M) (hc : IsColimit c)`.
  This is a universal-property presentation of the colimit the node says to take,
  not a restriction on M: these colimits exist by the small-model equivalence and
  small-site module colimits. Quantifying over arbitrary representatives includes
  the chosen colimit and does not privilege a different construction.
- The left-hand colimit is `(d : Cocone (M ⋙ moduleHigherDirectImage f p))`
  with `hd : IsColimit d`, again in the original module category on Y.
- The canonical map is exactly
  `hd.desc ((moduleHigherDirectImage f p).mapCocone c)`. Its source is `d.pt`
  and its target is `(moduleHigherDirectImage f p).obj c.pt`. By `IsColimit.fac`,
  precomposing with `d.ι.app j` gives
  `(moduleHigherDirectImage f p).map (c.ι.app j)`. Thus this is precisely the map
  induced by the colimit injections; no arbitrary map or unnormalized iso is supplied.
- The conclusion `IsIso (...)` asserts an isomorphism of O_Y-module sheaves.
- Injective-resolution computation is Mathlib `Functor.rightDerived` of the recorded
  `smallModuleDirectImage f`. `moduleHigherDirectImage` composes the actual source
  restriction, this functor, and the inverse target restriction equivalence.
  The explicit resolution instance is built from
  `SheafOfModules.isGrothendieckAbelian X.smallStructureRings` and
  `IsGrothendieckAbelian.enoughInjectives`. It adds no assumption. Equivalences
  preserve injectives, exactness, and cohomology, so this is the stated higher image
  in all original module sheaves. No abelian structure is selected by choice.
- There is no quasi-coherence condition, nor any compactness assumption on X or Y.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `structureSheaf`, `Modules`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently the existing Mathlib `SheafOfModules`.
- `def-weil-size-convention` is metatheoretic and has no declaration, as its record says.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleDirectImage`
  and its chart-limit characterization in `ModuleDirectImageModel`.
- `Mathlib.CategoryTheory.Limits.HasLimits`: colimit universal properties; the
  equivalent explicit representatives used here are `Cocone` and `IsColimit`,
  with `IsColimit.desc`/`fac` from `Limits.IsLimit`.
- `Mathlib.CategoryTheory.Filtered.Basic`: `CategoryTheory.IsFiltered`.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`: `Injective`;
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`: `InjectiveResolution`
  and `InjectiveResolution.instHasInjectiveResolutions`.
- `Mathlib.CategoryTheory.Abelian.RightDerived`: `Functor.rightDerived`, which
  applies the functor to injective resolutions and then takes degree-p cohomology.
- Added existing statement dependency `def-sfb-space-small-ringed-model`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`, `smallModuleRestriction`,
  `smallModuleEquivalence`, `SmallModules`, `smallStructureRings`.
- Added existing statement dependency `def-sfb-space-derived-module-calculus`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`, `smallModuleDirectImage`
  and `smallModuleDirectImage_additive`. No unbounded localization universe is needed.
- Added existing statement dependency `def-sfb-proper-curve-moduli`:
  `Sheaf.AlgebraicGeometry.ProperCurveModuli`, `MapIsQuasiCompact`; only this
  general affine-test property is used, with none of the proper-curve hypotheses.

These three dependencies already have landed Lean records. They expose existing
constructions needed to render the original statement, so they are added under
STMT_DEPS MAY GAIN LANDED NODES; the node's statement and proof are unchanged.
The helper higher-image functor belongs to the item's specified canonical map,
so it is listed in `lean.declarations` rather than introducing a duplicate notion node.

Available proof-dependency modules are imported without `public`, including the
current recorded enlarged-site module `SpaceCotangentRingMap`, the chart-limit
comparison, Grothendieck interface, scalar-forgetting colimits, chartwise permanence,
localization, module/abelian evaluation comparison, and affine etale cover.
Mathlib supplies the injectives, continuous adjunction, restriction, and
left-adjoint colimit facts. Three proof dependencies have no published declaration
and hence no module to import: `lem-trf-space-enlarged-site-scheme-density`,
`lem-sfb-space-cohomology-filtered-colimit`, and
`lem-sfb-ringed-site-higher-image-colimit-criterion`. They are proof obligations,
not prerequisites to typing this statement; their uses remain explicitly in its
complete six-step proof docstring.

Edge cases checked before writing: p=0 is included; identity morphisms and zero
diagrams give the usual comparison; empty X or Y requires no point or nonempty
space witness. Empty J is excluded precisely by filteredness, as in the statement.
A singleton diagram is included. X and Y may be non-quasi-compact: all finiteness
binders concern f and its relative diagonal. The diagonal is relative to f,
not to S. Arbitrary non-quasi-coherent modules are allowed. No assumption that
forgetting scalars preserves injectives is made: the proof uses the natural
cohomology comparison instead.

Searches actually run:

- `msearch.py ... leanfinder`, query "Higher direct images of module sheaves under
  quasi compact quasi separated algebraic space morphisms preserve filtered colimits":
  eight hits, including scheme module colimit existence and underived pushforward,
  condensed AB5, and affine-transition global sections; none states this result.
- `msearch.py ... loogle`, queries
  `CategoryTheory.Functor.rightDerived, CategoryTheory.Limits.colimit.post` and
  `CategoryTheory.Limits.colimit, CategoryTheory.Functor.rightDerived`: zero hits.
  A probe with `CategoryTheory.Limits.colimitComparison` reported unknown identifier;
  source inspection found the genuine chosen-colimit comparison `colimit.post`.
- `msearch.py ... grep`, query `rightDerived|colimitComparison`, subdirectory
  `CategoryTheory/Abelian`: six hits describing the general right-derived machinery;
  no algebraic-space continuity theorem.
- `rg` in `lean/WeilConjectures` for filtered/colimit and higher-image terms,
  and the item id: schemes and generic machinery occur, no exact statement.
- `rg` in `lean/Sheaf` for higher-image colimits, quasi-compactness, and derived
  functors found scheme/condensed results, the existing affine vanishing statement,
  the small ringed model, and the two existing quasi-compactness interfaces.
  `ProperCurveModuli.MapIsQuasiCompact` is the literal affine-test formulation
  used here. Existing `smallModuleDirectImage` is reused instead of redefined.
- `rg` in `lean/Sheaf`, `lean/WeilConjectures`, and `dag/lean_names_upstream.json`
  for the new declaration names found no collision. Related scheme higher-image
  declarations and algebraic-space affine vanishing have different statements.

No STATEMENT-DISPUTED flag or unresolved node fault.

## Second reading by Q50

This is a second pass by the same dispatcher-started worker; no independent worker
was started, as the assignment forbids it. The maintainer supplies the independent
review. I reopened the node and the Lean file and checked the following correspondence.
Both use a general base scheme and algebraic spaces over it. The two geometry binders
express affine-test quasi-compactness of f and its own relative diagonal, without
absolute compactness. The original module categories occur on both sides of the
higher functor, despite its internal small-model resolution. The diagram has no
quasi-coherence condition. Filteredness supplies exactly nonemptiness and the finite
cocone condition. The natural-number degree includes zero. `hc` and `hd` express
exactly the two colimits named by the node, and `hd.desc` of the image cocone has
the required coprojection formula by `IsColimit.fac`. It asserts an isomorphism
of modules, not merely an abelian or set-level bijection. No mismatch was found.
The second pass added the explicit proof imports for the current enlarged-site
record and the Mathlib slice-adjunction and restriction facts. The six proof steps
in the docstring retain the original DAG proof, including scalar-forgetting
colimits, slice restriction, the qcqs affine pullback check, and the normalization
of the final canonical map.
