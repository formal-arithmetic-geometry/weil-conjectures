## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceProperFlatH0Criterion` states
`AlgebraicGeometry.AlgebraicSpace.isIso_moduleStructureMap_of_proper_flat_field_fibres`
with one postponed proof and no new definitions. The node is unchanged except for
`lean`. No new nodes, dependency repairs, or statement correction are needed.

Source read: `literature/stacks-project/spaces-perfect.tex`, Tag 0E6B,
`lemma-proper-flat-h0`, lines 6610–6666, hypotheses (1)–(2) and conclusion (a).
The theorem intentionally states only conclusion (a), as does the assigned node.
Its docstring contains all seven proof steps of the node, preserving the canonical
unit normalization at degree zero and all dependency references.

The hypothesis and conclusion correspondence is as follows.

| Node clause | Lean rendering |
| --- | --- |
| An arbitrary scheme S | `{S : Scheme.{u}}` |
| Algebraic spaces X and Y over S, with morphism f | `{X Y : AlgebraicSpace S} (f : X ⟶ Y)` |
| Proper: separated, finite type, universally closed | `(hproper : MapIsProper f)`, whose definition is exactly these three predicates |
| Flat on compatible étale scheme charts | `(hflat : MapIsFlat f)` |
| Local finite presentation on étale charts | `hfp.1 : MapIsLocallyOfFinitePresentation f` |
| Finite presentation also requires quasi-compactness | `hfp.2.1 : MapIsQuasiCompact f.hom.hom` |
| Finite presentation also requires quasi-separatedness | `hfp.2.2 : MapIsQuasiCompact (pullback.diagonal f.hom.hom)` |
| Every field, without a restriction on characteristic or algebraic closure | `∀ (k : Type u) [Field k]` in `hfibre` |
| Every field-valued morphism to Y over S | `(a : Spec (CommRingCat.of k) ⟶ S) (b : schemeSpace (Over.mk a) ⟶ Y)` |
| The sheaf fibre product and its map to Spec k | `enlargedFibreProductFst b f`, with source `Spec k ×_Y X`; the canonical symmetry identifies it with the node's `X ×_Y Spec k`, including the projection |
| Its canonical scalar map k → Γ(X_b,O) is an isomorphism | `Function.Bijective (SheafOfModules.sectionsMap (moduleStructureMap (enlargedFibreProductFst b f)))`; see the normalization explanation below |
| The actual canonical f-sharp is invertible | `IsIso (moduleStructureMap f)` |
| Every algebraic space T → Y | `∀ (T : AlgebraicSpace S) (g : T ⟶ Y)` |
| The actual canonical base-changed structure map is invertible | `IsIso (moduleStructureMap (enlargedFibreProductFst g f))` |
| Small étale ringed sites and canonical module direct images | All structure maps use the existing `moduleStructureMap`, whose source is `SheafOfModules.unit Y.structureSheaf` and target is `(moduleDirectImage f).obj (SheafOfModules.unit X.structureSheaf)` |

The field hypothesis is a global-sections statement, not an assumed sheaf
isomorphism over Spec k. `SheafOfModules.sections` is the type of compatible sections
on the whole small site. For the represented spectrum its structure-sheaf sections
are canonically Γ(Spec k,O), hence k by the spectrum adjunction. By the defining
chart-limit universal property of `moduleDirectImage`, global sections of the
pushforward are exactly compatible regular functions on the source fibre. This
identification follows by taking the limit over the target charts of the chart-limit
formula: the category of all pairs (target chart, source chart mapping to it) projects
to the source charts, and compatible functions descend on the étale covering of each
source chart obtained by pulling back a target atlas. Thus the resulting section map
is the original scalar map, not a freely chosen isomorphism. In particular the chart
normalization of `moduleStructureMap` sends a regular function s to every a-sharp(s).
It preserves the ring operations and the unit under these identifications.
Consequently its bijectivity is equivalent to the stated ring-map isomorphism.
This is the same existing encoding used by
`structureMap_globalSections_bijective_of_geometricallyReduced_connected` in
`Sheaf.AlgebraicGeometry.SpaceProperFieldGlobalFunctions`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphism
  structure, `AlgebraicGeometry.Spec`, and `AlgebraicGeometry.Spec.map`.
- `Mathlib.Algebra.Field.Defs`: `Field` (the dependency is a Mathlib leaf).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsAlgebraicSpace`, `EtaleSite`, `structureSheaf`, and `Modules`; their signature
  and docstrings were read with the representability and chart definitions.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsProper`,
  `MapIsFlat`, `MapIsLocallyOfFinitePresentation`, and their constituent predicates.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `ModuleDirectImageModel`,
  `moduleChartDiagram`, `moduleChartScalar`, `moduleDirectImageModel`, and
  `moduleDirectImage` (the complete normalized chart-limit interface was read).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap`: `moduleStructureMap`
  and `existsUnique_moduleStructureMap`, including the normalization on every chart.
- The existing `ProperCurveModuli.MapIsQuasiCompact` declaration (in namespace
  `AlgebraicGeometry.AlgebraicSpace`) supplies the quasi-compactness predicate
  already publicly imported by the recorded morphism-properties module.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`,
  `enlargedFibreProduct` and `enlargedFibreProductFst` use actual representable sheaves
  and actual sheaf pullbacks. These are existing helpers, not fresh constructions.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf`: `SheafOfModules.sections` and
  `SheafOfModules.sectionsMap` take compatible sections and apply the sheaf map.

All already stated proof-dependency modules are imported. The Mathlib leaf
`lem-weil-pbc-left-exact-injective-resolution-degree-zero` is represented by
`Mathlib.CategoryTheory.Abelian.RightDerived`. The proof dependency
`lem-sfb-proper-flat-space-derived-base-change` has no recorded Lean declaration
in the read DAG, so there is no module to import for it; it is not needed for the
statement. Its use in the future proof remains explicit in the theorem docstring.

Edge cases checked before drafting:

- If Y is empty, it has no field-valued points; the hypothesis is vacuous and the
  conclusion is the unique isomorphism on its zero structure module. Any T → Y
  is empty as well. No nonemptiness assumption was inserted.
- An empty fibre over an actual field point has zero global-functions ring, so
  the scalar map from the nonzero field cannot be bijective. Such a fibre is
  correctly excluded by the hypothesis, rather than silently excluded by a binder.
- For an identity morphism the chartwise and finiteness hypotheses hold, its
  fibre is Spec k, and both structure maps are the canonical isomorphisms.
- Schemes and genuinely nonschematic algebraic spaces both use the same sheaf
  pullbacks and small-site module functors. The statement does not require f to
  be representable by schemes, nor T to be a scheme.
- Fields need not be algebraically closed, and all characteristics are allowed.
  The field universe is exactly the scheme universe u, so field-valued points
  including residue fields are available under the existing size convention;
  there is no independent smaller universe that could make the hypothesis vacuous.
- No Noetherian, separated-base, or quasi-compact-base hypothesis was added.
  Quasi-compactness and quasi-separatedness of f are the specified constituents
  of finite presentation, exactly as in the existing flat/proper/fp-locality lemma.

Searches actually performed:

1. `msearch.py ... leanfinder` with query
   `Proper flat finitely presented algebraic space morphism with scalar global functions on every field fibre has universally isomorphic structure sheaf direct image`:
   eight hits, headed by `AlgebraicGeometry.UniversallyOpen.of_flat`, `Flat`,
   flat-descent and formally unramified scheme results. No match for this theorem.
2. `msearch.py ... loogle` with query `"IsProper", "Flat", "IsIso"`: zero hits.
3. `msearch.py ... grep` with query
   `proper.*flat.*(global|sections)|[Hh]0.*(criterion|flat)` in `AlgebraicGeometry`:
   zero hits returned by that wrapper.
4. `rg` in `lean/WeilConjectures` and `lean/Sheaf` for proper/flat/global functions,
   H0 criteria, the node id and the proposed declaration name: no existing
   algebraic-space criterion. The nearby scheme-only theorem in
   `ProperFlatGlobalSectionsCriterion.lean` was opened and is not an exact match
   (its objects and module sites are schemes). The proper-field global-functions
   theorem was opened and supplies only the fibre conclusion under geometric
   hypotheses, not this universal pushforward statement.
5. `grep -rn` for the node id in `lean/WeilConjectures`: no matches.
6. Targeted `rg` for existing sections/scalar/fibre/finite-presentation interfaces
   found `SpaceProperFieldGlobalFunctions`, `AlgebraicSpaceFlatProperFpLocality`,
   `EnlargedEtaleRingedSite`, and the Mathlib compatible-section declarations.
   These were read and reused rather than redefined.

No statement dispute or source fault was found. `set_option autoImplicit false`
ensures every variable and universe is explicitly bound. The initial module
passed `scompile.py` in both sandbox and library contexts (1.9 seconds each),
with no error or unexpected warning. The delivery dry run recompiles the final
file after the final import/docstring cleanup.

## Second reading by Q157

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
