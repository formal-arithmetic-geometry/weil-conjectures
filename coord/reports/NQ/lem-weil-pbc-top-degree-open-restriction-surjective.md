## Worker report

The module `Sheaf.AlgebraicGeometry.TopDegreeOpenRestrictionSurjective` states
`AlgebraicGeometry.Scheme.Modules.top_degree_open_restriction_surjective`, with
`sorry` as its only proof. It supplies a surjective k-linear lift of the existing
canonical module cohomology restriction. Equality of its underlying additive map
with `moduleCohomologyFMap j ((restrictAdjunction j).unit.app F) d` pins the lift
completely: this is not an arbitrary map or a new cohomology construction.

Hypothesis and conclusion correspondence:

- A field k: `(k : Type u) [Field k]`.
- A k-scheme X: `(X : Scheme.{u}) [X.Over (Spec (.of k))]`. Its structure
  morphism is `X ↘ Spec (.of k)`.
- X Noetherian: `[IsLocallyNoetherian X] [CompactSpace X]`. This is the
  locally Noetherian plus quasi-compact characterization, with no separation
  hypothesis. Both hypotheses are necessary for this characterization.
- Dimension exactly d >= 0: `(d : ℕ)` and
  `(hdim : topologicalKrullDim X = (d : WithBot ℕ∞))`. Equality is retained,
  rather than replacing exact dimension by a bound. Negative and infinite
  dimensions are not asserted in the node.
- A quasi-compact open immersion u: `(V : Scheme.{u}) (j : V ⟶ X)` with
  `[IsOpenImmersion j] [CompactSpace V]`. This permits any presentation of the
  open subscheme, rather than requiring a literal element of X.Opens.
- An arbitrary O_X-module: `(F : SheafOfModules.{u} (moduleRings X.toRingedSpace))`.
  This is the exact Mathlib match for the recorded general ringed-site module
  category; its owning module `Sheaf.CategoryTheory.RingedSiteModules` is imported.
- H^d(X,F): `(RingedSpace.moduleCohomology X.toRingedSpace d).obj F`, the
  cohomology functor recorded by `pqf-def-cohomology`.
- F restricted to V: `(restrictFunctor j).obj F`, Mathlib's canonical restriction
  along an open immersion, with its adjunction `restrictAdjunction j`.
- H^d(V,F|_V): `(RingedSpace.moduleCohomology V.toRingedSpace d).obj
  ((restrictFunctor j).obj F)`.
- Canonical k-actions: apply `ModuleCat.restrictScalars` along
  `((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (X ↘ Spec (.of k)).appTop).hom`
  on the source, and the same expression for `j ≫ (X ↘ Spec (.of k))` on V.
  These are precisely k -> Γ(X,O_X) and k -> Γ(V,O_V). No independently
  chosen k-structure on V is assumed; the composite supplies the induced one.
- k-linearity: L is a morphism between these `ModuleCat k` objects.
- Canonicity: `(forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}).map L =
  moduleCohomologyFMap j ((restrictAdjunction j).unit.app F) d`.
  The adjunction unit is the sectionwise restriction F -> j_*(F|_V).
  Forgetting scalar restriction does not change the underlying additive groups.
- Surjectivity: `Function.Surjective L`.
- The negative qualifications (no coherence and no properness) are realized by
  the absence of such assumptions; no separatedness is assumed either.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- `Mathlib.AlgebraicGeometry.Over`: `AlgebraicGeometry.Scheme.Over`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`
  transparently abbreviates the existing `SheafOfModules` used here.
- `Sheaf.Paper.PQFCohomology`: `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages`,
  which records `AlgebraicGeometry.RingedSpace.moduleCohomology`; the latter's
  full defining signature and docstring were also read in
  `Sheaf.Topology.RingedSpaceModuleCohomology`.
- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMap`:
  `AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap`. The module's
  `ModuleCohomologyFMapData`, construction and restriction specialization were
  read. The already landed node `def-weil-pbc-module-cohomology-fmap` is added
  to stmt_deps to name the canonical map explicitly; it is not duplicated.
- `Mathlib.AlgebraicGeometry.Modules.Sheaf`: `Scheme.Modules.restrictFunctor`
  and `Scheme.Modules.restrictAdjunction`, whose full signatures and definitions
  were read. Restriction is sectionwise on the open image, not the unrelated
  general Mathlib pullback implementation.

The proof-dependency modules with recorded declarations are imported without
`public`, unless already needed publicly for the signature. The unstated
`lem-weil-pbc-punctured-neighborhood-cohomology-colimit` has no module to import;
it remains a proof dependency and is explicitly named in the theorem docstring.
It is not required to formulate this statement. No import cycle was introduced.
The theorem docstring reproduces all ten proof steps with their dependency ids.

Source verification: read `literature/stacks-project/cohomology.tex`,
`proposition-cohomological-dimension-spectral` (Tag 0A3G), statement and proof,
and `lemma-modules-abelian` (Tag 01F1), statement and proof. The former gives
surjectivity for arbitrary abelian sheaves on spectral spaces. The latter
identifies module and abelian cohomology by the common resolution, compatibly
with restriction. The last proof step in the DAG gives k-linearity on that same
resolution, matching the scalar-restriction encoding here.

Edge cases checked mathematically before writing:

- d=0: a zero-dimensional Noetherian scheme is finite discrete; glue any section
  over V with zero on the complementary open. H^0 is global sections.
- V empty: the target cohomology is zero, so restriction is surjective. There is
  no Nonempty assumption on V and the zero-ring global sections cause no issue
  for restriction of scalars.
- V=X and j the identity, or an arbitrary isomorphic presentation: the canonical
  restriction is an isomorphism. General open immersions are bound explicitly.
- F=0: both cohomology objects vanish.
- X empty: its topological dimension is bottom, so the exact nonnegative finite
  dimension hypothesis is impossible, exactly as the node requires.
- Neither positive characteristic nor characteristic zero is excluded.
- Nonproper, nonseparated and noncoherent cases remain in scope. All dimensions,
  fields and schemes use an arbitrary explicit universe u; no independent small
  test universe or extra derived-category hypothesis is introduced.

Searches for an existing statement (all via the required tools/read-only sources):

- `msearch.py ... leanfinder "Top degree cohomology restriction to a quasi compact
  open of a Noetherian scheme is surjective"`: 8 hits, concerning sections,
  affine Zariski sites, ideal subschemes, qcqs basic-open localization and affine
  presentations; none states top-degree cohomology restriction surjectivity.
- `msearch.py ... loogle "topologicalKrullDim, Function.Surjective"`: 0 hits.
- `msearch.py ... grep "cohomology.*restriction|restriction.*cohomology" Topology`:
  0 hits in Mathlib.
- `msearch.py ... leansearch "Cohomology in top dimension restricts surjectively
  to an open subscheme of a Noetherian scheme"`: service unavailable, Internal
  Server Error; recorded as unavailable, no mathematical verdict drawn.
- `rg` of moduleCohomology/openModuleCohomology/cohomology restriction in
  `lean/Sheaf` and the slopmaster2 source found the canonical h-map, the
  open-module alternative, Mayer--Vietoris, and scalar cohomology operations.
  These were inspected; none states this surjectivity theorem.
- `rg` for the item id, top-degree restriction wording and proposed declaration
  name in the slopmaster2 source, Mathlib, `lean/Sheaf` and upstream name index:
  no existing theorem/name collision. DAG searches found the existing canonical
  map node and the open-module and scalar-operation nodes, so no new notion
  node or duplicate construction was introduced.

No statement correction, new definition node, dependency-interface repair or
STATEMENT-DISPUTED issue is needed. The node copy changes only lean and adds the
already landed canonical-map node to stmt_deps.

Validation: `scompile.py NQ lem-weil-pbc-top-degree-open-restriction-surjective`
compiled the delivered module on the server cleanly (1.5 seconds, nice 19,
two threads, 60-second limit). No local compilation was used. `deliver2.py NQ lem-weil-pbc-top-degree-open-restriction-surjective --no-push`
printed OK: compilation and preflight passed except for the independent second
reading, which the second reader supplies. Nothing was pushed.

## Second reading by NQ

I independently read the repository node, the sandbox node and complete Lean module,
Stacks `cohomology.tex` at `proposition-cohomological-dimension-spectral` (Tag 0A3G)
and `lemma-modules-abelian` (Tag 01F1), and the statement-dependency records and
implementations. Tag 0A3G assumes a spectral space of dimension d and an arbitrary
abelian sheaf; its second clause assumes a quasi-compact open. There is no hidden
coherence, properness, separation or characteristic hypothesis. Tag 01F1 applies
to every module on a ringed space and computes both cohomologies with the same
module-injective resolution, giving compatibility with restriction. The node's
Noetherian schemes form the stated specialization, without extra hypotheses.

The node's objects, hypotheses and conclusion, item by item:

1. Field k: `(k : Type u) [Field k]`. Exact; no algebraic closure or characteristic
   condition. This is Mathlib's recorded field notion.
2. Scheme X over k: `(X : Scheme.{u}) [X.Over (Spec (.of k))]`. Exact;
   `Scheme.Over` is the structure-morphism datum, read in Mathlib `Over.lean`.
3. X Noetherian: `[IsLocallyNoetherian X] [CompactSpace X]`. Exact, by the
   locally Noetherian plus quasi-compact definition. Read the actual
   `IsLocallyNoetherian.component_noetherian` signature. CompactSpace imposes
   no Hausdorff condition. No separatedness assumption is present.
4. Dimension d >= 0, with equality: `(d : ℕ)` and
   `hdim : topologicalKrullDim X = (d : WithBot ℕ∞)`. Exact; Mathlib defines
   this dimension as `Order.krullDim (IrreducibleCloseds X)`, including bottom
   for the empty space. The signature retains equality, not an upper bound.
5. Open immersion u:V -> X: `(V : Scheme.{u}) (j : V ⟶ X)
   [IsOpenImmersion j]`. Exact; the recorded Mathlib property is an open
   immersion of locally ringed spaces. Arbitrary presentations of the open,
   including isomorphic presentations, are allowed.
6. V quasi-compact: `[CompactSpace V]`. Exact. Though derivable here from
   Noetherianity, this is an explicit hypothesis in the node itself.
7. Every O_X-module F: `(F : SheafOfModules.{u} (moduleRings X.toRingedSpace))`.
   Exact. Read `ringedSiteModules`: it transparently abbreviates precisely
   Mathlib's `SheafOfModules`, so the statement does not substitute another
   module category or a quasi-coherent subcategory.
8. Source H^d(X,F): `(RingedSpace.moduleCohomology X.toRingedSpace d).obj F`.
   Exact. Read `PQFCohomology` and `RingedSpaceModuleCohomology`: the latter
   is the right derived global-sections functor in O_X-modules, with values
   in modules over global functions, exactly as `pqf-def-cohomology` requires.
9. Restriction F|_V: `(restrictFunctor j).obj F`. Exact. Read Mathlib
   `Modules/Sheaf.lean`: `restrictAppIso` identifies its sections on B with
   F(j(B)); `restrictAdjunction_unit_app_app` is the section restriction
   F(B) -> F(B intersect j(V)). This is genuine open restriction.
10. Target H^d(V,F|_V): `(RingedSpace.moduleCohomology V.toRingedSpace d).obj
    ((restrictFunctor j).obj F)`. Exact; the same cohomology notion is used
    on both schemes.
11. Canonical k-actions: the two `ModuleCat.restrictScalars` use the inverse
    `ΓSpecIso` followed by the top component of the structure map of X,
    respectively `j ≫ (X ↘ Spec (.of k))`. Exact maps k -> Gamma(X,O_X)
    and k -> Gamma(V,O_V); no independently chosen action on V is assumed.
    Read `ΓSpecIso` and `restrictScalars`, whose action is r*x = f(r)*x.
12. Canonical restriction is k-linear: the witness `L` is a morphism in
    `ModuleCat k`, and its image under `forget₂` equals
    `moduleCohomologyFMap j ((restrictAdjunction j).unit.app F) d`.
    Exact: the equality pins the underlying additive map completely. Read
    the recorded FMap construction, its resolution data and canonical sections
    comparison, and its open restriction specialization. The existential
    formulation asserts linearity of that fixed map, rather than assuming
    an arbitrary surjective map between the same objects.
13. Surjectivity: `Function.Surjective L`. Exact. Scalar restriction preserves
    the underlying groups, so this is surjectivity of the canonical restriction.
14. No coherence or properness required: no such binders occur. Exact.
    All universal objects precede `∃ L`, as required for every F and j.

Edge cases: d=0 remains included; a zero-dimensional Noetherian scheme is finite
and discrete, so extension by zero supplies a section preimage. V empty is
allowed and its target is zero; the zero ring of its global functions causes no
problem for restriction of scalars. F=0 gives zero cohomology. Identity j, V=X,
and arbitrary isomorphic presentations are included. X empty has dimension bottom
and thus does not satisfy the node's nonnegative exact dimension hypothesis;
Lean agrees. There is no index family to restrict. Every field characteristic is
included. The explicit arbitrary universe u follows the recorded scheme/module
cohomology size convention, with no additional universe equality, derived-category
instance or smallness hypothesis. All variables are bound and autoImplicit is false.

Independent searches, using wording different from the first reader:

- LeanFinder: `highest nonvanishing sheaf cohomology restriction epimorphism open
  subspace`, eight hits. Mayer--Vietoris short-complex epimorphisms, group-cochain
  epimorphisms, truncations and condensed limits do not state this result.
- Loogle: `"cohomology"`, twelve hits, all HomComplex cohomology-class operations;
  no top-degree open-restriction theorem. An earlier two-string query was rejected
  by Loogle's parser and is not counted as negative evidence.
- LeanSearch: `Restriction on the highest cohomology of any module sheaf on a
  Noetherian scheme is surjective for open immersions` was unavailable (Internal
  Server Error); no negative mathematical inference was made from that failure.
- Independent `rg` in Mathlib Topology and Sites, upstream WeilConjectures and
  project Sheaf for `top.?degree.*restrict|restrict.*top.?degree|cohomology.*surject|
  surject.*cohomology` found no exact theorem. I opened upstream Curve/Assertions:
  its similarly named assertion is degree-two etale cohomology of coefficient
  sheaves on curves, not arbitrary Zariski O_X-modules in dimension d. The other
  hits concern Cech criteria, group cochains and unrelated derived statements.

No H3/H4 mismatch was found. No new definition or dependency module was delivered,
and no statement correction or citer audit is needed. The existing canonical-map
node added to stmt_deps is the genuine already recorded construction. The ten-step
proof docstring reproduces the node's proof, including the punctured-neighborhood
proof dependency that is not needed to type this statement. There is exactly one
postponed theorem, no data definitions and no proved assertions in this module.
Module/declaration source and blueprint docstrings and 100-character lines pass.
The node's `lean.statement` equals the file's signature verbatim. I preserved the
Lean and node because they are correct; the second reading adds this review only.
