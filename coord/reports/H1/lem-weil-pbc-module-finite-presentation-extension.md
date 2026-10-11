## Worker report

The module `lean/Sheaf/AlgebraicGeometry/ModuleFinitePresentationExtension.lean`
states `AlgebraicGeometry.Scheme.Modules.exists_finitePresentation_extension`.
Its sole theorem has proof `sorry`; it introduces no definitions. Its docstring
records all nine proof steps and the DAG nodes used in them.

Source checked: https://stacks.math.columbia.edu/tag/01PI (Lemma 28.23.4).
The local literature checkout has no `stacks-project/properties.tex`, so the
source was read on the official Stacks page. The node matches that source.
No statement correction, new node, dependency module, or disputed statement.

Hypothesis and conclusion correspondence:

- Scheme X: `(X : Scheme.{u})`.
- X quasi-compact: `[CompactSpace X]`, without any Hausdorff assumption.
- X quasi-separated: `[QuasiSeparatedSpace X]`, equivalent to quasi-compactness
  of the scheme diagonal, as `quasiSeparatedSpace_iff_quasiSeparated` records.
- U an open subscheme: `(U : X.Opens)`; quasi-compactness is
  `(hU : IsCompact (U : Set X))`. There is no affineness assumption on U.
- F an O_X-module: `F : SheafOfModules.{u} (moduleRings X.toRingedSpace)`.
- F quasi-coherent: `[F.IsQuasicoherent]`.
- G an O_U-module: `G : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)`.
  This is the localized open site: an object is an open W contained in U, and
  the structure ring on it is O_X(W). It therefore expresses the node's
  sectionwise restriction convention exactly. Mathlib's
  `Scheme.Modules.overEquiv U` identifies this category with `(U : Scheme).Modules`;
  `overFunctorEquiv U` identifies this restriction with scheme open restriction.
- G of finite presentation: `[G.IsFinitePresentation]`. This is local cokernel
  presentation by two finite free modules, with no global finite-presentation
  or coherence requirement added.
- The given O_U-linear morphism: `(φ : G ⟶ F.over U)`.
- Existence of an O_X-module G': the first existential, in the same module category.
- Finite presentation of G': `G'.IsFinitePresentation`.
- Existence of an O_X-linear map φ': `(φ' : G' ⟶ F)` in the second existential.
- Identification on U: `(e : G'.over U ≅ G)` in the same existential.
- Equality of restricted maps under that identification:
  `(SheafOfModules.overFunctor (moduleRings X.toRingedSpace) U).map φ' = e.hom ≫ φ`.
  Composition in Lean runs left to right, so this says φ'|_U = φ ∘ e.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-pbc-scheme-conventions`: a convention-only node, deliberately no
  declaration. Its quasi-separated convention is rendered with Mathlib's
  `QuasiSeparatedSpace`, using `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.
- `def-weil-pbc-quasi-compact-scheme`: recorded Mathlib match `CompactSpace`
  (`Mathlib.Topology.Defs.Filter`); U uses its subset analogue `IsCompact`.
- `pqf-def-coherent`: imported `Sheaf.AlgebraicGeometry.Coherent`, whose module
  explicitly delegates the quasi-coherent clause to `SheafOfModules.IsQuasicoherent`.
  Its recorded `RingedSpace.IsCoherent` is the third clause, not the quasi-coherent
  clause, and is consequently not imposed here. The same module supplies the
  shared `AlgebraicGeometry.moduleRings` encoding.
- `def-weil-sheaf-of-modules-category`: `SheafOfModules` and its category structure
  (`Mathlib.Algebra.Category.ModuleCat.Sheaf`), used both globally and over U.
- `def-weil-pbc-module-finite-type-presentation`: `SheafOfModules.IsFinitePresentation`
  (`Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`), used for G and G'.
  The recorded equivalence between finite presentations and finite free cokernels
  was checked in its signatures/docstrings. `SheafOfModules.overFunctor`, `over`,
  and its action on morphisms are read from `PushforwardContinuous`.

Edge cases checked before writing:

- Empty X and U are allowed; there is no nonempty binder and local presentation
  on an empty site is vacuous.
- U = empty: a zero global module and zero map give an extension; the module on
  the empty open is identified by its unique sheaf isomorphism.
- U = X: choose G itself after the canonical open-site identification and φ.
- G = 0 or φ = 0 is allowed; no nonzero or injectivity/surjectivity assumptions.
- Finite presentations include zero generators and zero relations; no positive
  rank restriction has been introduced.
- X need not be Noetherian or separated. Its quasi-separatedness is retained.
- `universe u` is explicitly declared, and all carriers use the established
  `SheafOfModules.{u}` ringed-space encoding; no extra universe-lowering condition.

Searches for an existing declaration:

- `msearch.py ... leansearch "extend morphism from finitely presented sheaf on quasi
  compact open of qcqs scheme"`: service unavailable, Internal Server Error;
  the other search services and local source searches supplied the search evidence.

- `msearch.py ... leanfinder "extend morphism from finitely presented sheaf of modules
  on quasi-compact open of qcqs scheme"`: eight hits, all finite-presentation
  predicates, quasicoherent-data construction, and finite-presentation implications;
  none extends a module and a map.
- `msearch.py ... loogle "SheafOfModules.IsFinitePresentation,
  SheafOfModules.overFunctor"`: zero hits.
- `msearch.py ... grep "extend.*[Ff]inite|[Ff]inite.*[Pp]resentation.*extend"`:
  unrelated finiteness/extension hits; none for sheaf-module extension.
- `rg` of the item id and finite-presentation extension naming patterns in
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and repository `lean/Sheaf`:
  no theorem match (only an unrelated `extends` structure in FiberDegree).
- `rg` for `exists_finitePresentation_extension` in `dag/lean_names_upstream.json`,
  Mathlib, the source project, and `lean/Sheaf`: no collision.

Validation: server compilation with `scompile.py` succeeded, exit code 0,
with no errors or warnings (3.3 seconds). All variables and universes are explicit.

## Second reading by H1

Independent second reading: opened the delivered node and Lean file together,
then all six statement-dependency nodes and the declarations supplying their
notions. Read the official Stacks `properties.tex`, section
`section-extending-quasi-coherent-sheaves`, lemma
`lemma-extend-finite-presentation` (Tag 01PI), including its proof, from
https://raw.githubusercontent.com/stacks/stacks-project/master/properties.tex .
Also checked https://stacks.math.columbia.edu/tag/01PI . The local literature
checkout lacks this TeX file. The section adds no standing hypothesis;
all assumptions used here occur in the lemma itself.

Object, hypothesis, and conclusion checklist (every entry accepted):

1. An arbitrary scheme X: `(X : Scheme.{u})`. Read Mathlib's `Scheme`
   structure in `AlgebraicGeometry/Scheme.lean`: a locally ringed space locally
   isomorphic to spectra of commutative rings, exactly `def-pc-scheme`.
2. X quasi-compact: `[CompactSpace X]`. Read `Topology/Defs/Filter.lean`:
   `isCompact_univ`, explicitly without a separation condition, as recorded
   by `def-weil-pbc-quasi-compact-scheme`.
3. X quasi-separated: `[QuasiSeparatedSpace X]`. Read
   `quasiSeparatedSpace_iff_quasiSeparated (X : Scheme)` in
   `AlgebraicGeometry/Morphisms/QuasiSeparated.lean`: equivalence with
   quasi-separatedness of the terminal morphism. This renders the absolute
   scheme convention of `def-weil-pbc-scheme-conventions`; that node expressly
   collects conventions and defines no additional predicate.
4. An open subscheme U of X: `(U : X.Opens)`. The over category of opens in X
   over U is the category of opens contained in U, hence presents the same
   open subscheme; it does not require U to be affine.
5. U quasi-compact: `(hU : IsCompact (U : Set X))`. For an open subspace this
   is its compactness in its own topology. No compactness of its closure or
   quasi-compactness of an unrelated identity morphism is substituted.
6. An O_X-module F: `F : SheafOfModules.{u} (moduleRings X.toRingedSpace)`.
   Read `SheafOfModules` and `SheafOfModules.Hom` in
   `Algebra/Category/ModuleCat/Sheaf.lean`, the match of
   `def-weil-sheaf-of-modules-category`: sectionwise modules, linear maps,
   with the sheaf condition on the underlying additive presheaf.
   Read `moduleRings` in `Sheaf/Paper/DerivedHomMayerVietoris.lean`: it merely
   forgets commutativity of the actual structure sheaf, with no data hole.
7. F quasi-coherent: `[F.IsQuasicoherent]`. Read `pqf-def-coherent` and its
   `Sheaf.AlgebraicGeometry.Coherent` module: its first clause deliberately
   uses Mathlib's `SheafOfModules.IsQuasicoherent`, not `IsCoherent` (its third
   clause). Read `QuasicoherentData` and `IsQuasicoherent` in Mathlib's
   `Sheaf/Quasicoherent.lean`: a cover and local free cokernel presentations.
   This is the shared quasi-coherence notion, equivalent on schemes to the
   node's affine-local form, with no coherence assumption imposed.
8. An O_U-module G: `G : SheafOfModules.{u}
   ((moduleRings X.toRingedSpace).over U)`. Read `overFunctor` and `over` in
   `Sheaf/PushforwardContinuous.lean`: restriction via the forgetful functor
   from the over site. Also read `Scheme.Modules.overEquiv U` and
   `overFunctorEquiv U` in `AlgebraicGeometry/Modules/Sheaf.lean`: equivalence
   with modules on U and compatibility with scheme open restriction.
   Thus the object is precisely the one in the node, using the explicit
   sectionwise restriction convention in its finite-presentation dependency.
9. G locally of finite presentation: `[G.IsFinitePresentation]`. Read
   `def-weil-pbc-module-finite-type-presentation` and Mathlib's
   `Presentation`, `Presentation.IsFinite`, `QuasicoherentData.IsFinitePresentation`,
   and `SheafOfModules.IsFinitePresentation`. These assert finitely many
   generators and relations locally, not a globally chosen finite presentation.
   Read `presentationOfIsCokernelFree` and `Presentation.isColimit` in the same
   file: their signatures identify this condition with the node's finite
   free cokernel presentations. No Noetherian assumption appears.
10. Given O_U-linear map to F restricted to U: `(φ : G ⟶ F.over U)`.
    The same category's morphisms are linear, and the same over functor
    supplies restriction of F.
11. Existence of a global O_X-module G': the outer existential
    `∃ (G' : SheafOfModules.{u} (moduleRings X.toRingedSpace)), ...`.
12. G' of finite presentation: `G'.IsFinitePresentation`, the very same local
    predicate used for G, with no additional coherence or finite global rank.
13. Existence of a global O_X-linear map: `∃ (φ' : G' ⟶ F) ...`.
14. Existence of the identification on U: `(e : G'.over U ≅ G)` in that
    existential. It is an isomorphism of O_U-modules, not just additive groups.
15. Agreement with the given map under this identification:
    `(SheafOfModules.overFunctor (moduleRings X.toRingedSpace) U).map φ'
      = e.hom ≫ φ`.
    Both sides have source G' restricted to U and target F restricted to U;
    categorical composition runs left to right. This is exactly the node's
    compatibility requirement. The existential ordering allows the module,
    map, and identification to depend on all the given data, as required.

Edge cases: empty X and empty U are allowed (no nonemptiness binder); for
empty U, the zero global module with zero map is a possible extension and
sheaves on the empty open have the required unique identification. At U = X
one transports G and its map across the open-site equivalence. Zero F, zero G,
and zero maps are permitted, with no mono or epi condition on the given map.
Empty generators and relations, hence ranks m = 0 and n = 0, are permitted by
`Finite` in the presentation predicate. An empty affine cover in the proof
is covered by its k = 0 base case. There is no characteristic, field,
Noetherian, Hausdorff, or separatedness restriction. The universe u is bound;
the theorem uses the project's established ringed-space module universe.
It has no test-object quantifier in a smaller universe and no independent
index-universe restriction. These checks reveal no excluded source case.

Independent searches, using wording different from the first worker:

- LeanFinder: `spreading out a finitely presented module sheaf and its map
  from an open subscheme`: eight hits, local finite-presentation definitions,
  presentation transport, and a scheme-morphism finite-presentation theorem;
  no extension of both a module and its map.
- Loogle: `SheafOfModules.IsFinitePresentation, SheafOfModules.IsQuasicoherent`:
  only `SheafOfModules.instIsQuasicoherentOfIsFinitePresentation`; read its
  signature and implementation, which gives an implication, not this extension.
- LeanSearch: `A map from a locally finitely presented sheaf on a compact open
  spreads to the ambient scheme`: service returned Internal Server Error;
  recorded as unavailable, not as evidence of absence.
- msearch grep: `01PI|lift_finitePresentation|extend_finitePresentation|
  finitePresentation_extension|extend.*SheafOfModules`: no hits.
- Direct rg in Mathlib's module-sheaf and algebraic-geometry sources,
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, repository `lean/Sheaf`,
  and `dag/lean_names_upstream.json`, using `extend.*(presentation|presented)`,
  `(presentation|presented).*exten`, `01PI`, and the declaration name: only
  unrelated field extensions, presentations of groups/rings, and scheme
  finite-presentation results; no duplicate theorem or name collision.

No mismatch found; no Lean or node change was needed. There are no new nodes,
no dependency modules, and no statement correction to review. The two imports
supply the shared module notions and quasi-separated scheme convention.
The module and declaration docstrings identify Tag 01PI and the blueprint id;
the theorem docstring carries all nine node proof steps, including the base
case, compatible gluing, finite-type replacements, and finite-presentation
cokernel construction. There are no new definitions, instances, or proofs;
the sole theorem has exactly `sorry` as its proof. No variable or universe is
unbound; every line is at most 100 characters. Checked mechanically that
`lean.statement` is verbatim the signature in the file.

Validation: independently ran `scompile.py H1
lem-weil-pbc-module-finite-presentation-extension
lean/Sheaf/AlgebraicGeometry/ModuleFinitePresentationExtension.lean`.
Server compilation finished in 3.3 seconds, exit code 0, with no warnings or
errors. Second reading changed only this report by adding the independent audit.
