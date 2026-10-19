## Worker report

The module `Sheaf.AlgebraicTopology.UnstraighteningSimplexDkEquivalence` states
`SSet.ConePresheaf.unstraightening_simplex_dk_equivalence`. It constructs the
specific enrichment required in the node, then states its Dwyer–Kan conclusion.
The node's natural-language statement and dependencies are unchanged; only its
`lean` field is set. All universes and variables are bound explicitly. There are
no new independent notions or dependency repairs in this delivery.

Clause-by-clause correspondence:

- The nonnegative integer is `(n : ℕ)`, including zero. The base everywhere in the
  main theorem is the actual `(Δ[n] : SSet.{u})`, with arbitrary explicit `u`.
- The presheaf objects are the recorded `ConePresheaf.Presheaf Δ[n]`, whose functor
  is an enriched functor on `(PinchedCube.rigidification.obj Δ[n])ᵒᵖ` to `SSet.{u}`.
  There is no replacement of coherent realization by the ordinary ordinal category.
- The full subcategory of projectively cofibrant and fibrant objects is expressed
  by quantifying over those same presheaf objects with `IsProjectivelyBifibrant`.
  This abbreviation's real definition is `IsProjectivelyCofibrant F ∧
  ∀ c, KanComplex (obj F c)`. Its two clauses are exactly projective cofibrancy and
  objectwise Kan fibrancy, not merely objectwise fibrancy alone. Because mapping
  objects remain `ConePresheaf.mapping F G`, this is the full simplicial subcategory.
- The source mapping simplicial sets are the dependency's existing `mapping F G`:
  their m-simplices are the existing full graded enriched transformations with
  parameter Δ[m], equivalently enriched transformations F × Δ[m] → G. All action
  compatibility in positive simplicial degrees is retained.
- The target objects are all `E : Over Δ[n]` satisfying
  `Enhanced.rightFibration E.hom`; no additional fibrant-slice or cofibrancy
  condition is imposed. The first conjunct states that `rightProjection F` is a
  right fibration for every source object, so U has precisely this target.
- The target mapping complex is the existing
  `Enhanced.transportOverHom (rightProjection F) (rightProjection G)`.
  Its definition is the subcomplex of the internal Hom imposing the over-base
  equation at every test simplex. Thus its m-simplices are exactly the maps
  U(F) × Δ[m] → U(G) over the fixed base.
- The mapping comparison is the actual `unstraighteningMapping F G`, with real
  component data. `pinchCone` is a pushout descendent: on the base it collapses S
  to the initial point x, and on the cone it uses the ordered-simplex identification
  followed by the actual pinch. `coneParameterAt` applies this functor on the
  old-object-to-cone-vertex mapping object, transports its two endpoints, then
  applies `pinchedHomIso.inv` and `pinchedMaximum`. These are the recorded Q → Δ
  maximum maps, not arbitrary weak equivalences or unspecified chosen maps.
  `parameterComponent` evaluates a graded transformation on the pair consisting
  of the original F-label and that parameter. `parameterLabel` packages these
  components as a full enriched transformation; `parameterMap` gives the actual
  map U(F) × Δ[m] → U(G). This is the precomposition in Remark the project server under
  U(F × K) = U(F) × Sing_Q K and K → Sing_Q K induced by Q → Δ.
- `parameterMap_functorial` records both normalization on ordinary arrows of U
  and composition with one shared parameter. `parameterLabel_restrict` and
  `parameterMap_restrict` supply both simplicial naturality requirements. These
  are the well-definedness and functoriality statements of this node's enrichment.
- Local weak equivalence is exactly
  `Enhanced.IsWeakHomotopyEquivalence (unstraighteningMapping F G)` for every
  pair of source objects. This uses the dependency's geometric-realization
  convention, with all positive based homotopy groups and path components.
- Equivalence of path-component categories is expanded without defining a second
  Dwyer–Kan predicate. Full faithfulness is `Function.Bijective
  (SSet.mapπ₀ (unstraighteningMapping F G))` for every pair. Essential surjectivity
  is the last conjunct: every right fibration E receives some bifibrant F and
  slice arrows `f : rightObj F ⟶ E`, `g : E ⟶ rightObj F` whose composites have
  the identity components in the two existing mapping complexes over Δ[n].
  These are equalities of π₀ classes, not strict inverse-arrow equations.
  The representatives use the existing `transportHomVertex` and the genuine
  `Over.w` equations. The expansion is the same local/π₀ criterion as the
  recorded `CategoryTheory.DwyerKanEquivalence` and `PiZeroEquivalence`.
- The theorem has no general-base slice-model conclusion or hypothesis. Some
  auxiliary maps are defined for arbitrary S because their construction requires
  no slice model structure; the Dwyer–Kan assertion is restricted to Δ[n].

Dependency declarations read and reused:
- `Sheaf.CategoryTheory.SpaceTransportClassification`:
  only the existing constructions `Enhanced.transportOverHom` and `Enhanced.transportHomVertex`. The classification assertion and its proof are not used. This reuse prevents a duplicate definition of mapping complexes. The downstream theorem has a DAG path through this item; it is deliberately
  not introduced as a theorem prerequisite. The module import exposes these
  already-existing constructions, and does not depend on that theorem.
- `Sheaf.CategoryTheory.UnstraighteningHomotopyDescent` is imported for its existing `SSet.ConePresheaf.coneParameter`, whose path-nerve signature is distinct from this item's `coneParameterAt`; the existing canonical path parameter is thereby reused and the namespace collision is avoided.

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.IsWeakHomotopyEquivalence`, with its realization/component/group
  definition; the existing ordered join imported through the cone dependency.
- `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases` reexports
  `Sheaf.CategoryTheory.InfinityFibrations`, whose
  `SSet.Enhanced.rightFibration` is the full right-horn lifting condition.
- `Sheaf.AlgebraicTopology.ConePresheafAdjunction`:
  `Presheaf`, `obj`, `action`, `Hom`, `component`, `homMk`, `mapping`,
  `IsProjectivelyCofibrant`, `ParameterMap`, `restrictParameter`, `left`,
  `RightSimplex`, `rightRestrict`, `rightSet`, `rightObj`, `rightProjection`,
  `rightSetMap`, and the ordinary `right` functor. These are reused unchanged.
  Its published module also exposes the canonical constructions
  `Straightening.conePushout`, `baseInclusion`, and `coneVertex`.
- `Sheaf.AlgebraicTopology.PinchedCubeLatching`:
  `rigidification`, `initialFace`, `J`, `pinch`, `x`, `y`, `Q`, `qFunctor`,
  and the normalized isomorphism and maximum-map clauses of
  `pinched_cube_latching`. The latter theorem has four universe parameters in
  the current compiled source; all four are explicitly instantiated to u.
- `Sheaf.CategoryTheory.SpaceTransportClassification`:
  only the existing constructions `Enhanced.transportOverHom` and
  `Enhanced.transportHomVertex`. The classification assertion and its proof
  are not used. This reuse prevents a duplicate definition of mapping complexes.
  The downstream theorem has a DAG path through this item; it is deliberately
  not introduced as a theorem prerequisite. The module import exposes these
  already-existing constructions, and does not depend on that theorem.
- Mathlib: cartesian tensor/lift/projections, closed curry/uncurry, simplicial
  Yoneda, `Over`, enriched composition, and `SSet.π₀`, `π₀.mk`, `mapπ₀`.

No data are selected from unproved mere existence. The simplex-cone isomorphism
is selected from the explicit unique-existence statement fixing its full initial
face and final vertex. The pinched-cube isomorphism and maximum map are selected
from the existing theorem with equations on the surjective quotient generator;
those equations determine each map uniquely. All other map data are explicit
composites, pushout descents, or enriched transformation components. The postponed
technical statements are named, documented in this node's module, and listed in
`lean.declarations`; each has its source and a natural-language proof. Their
proofs, including the main theorem, are exactly `by sorry`. No result is proved
in this stage; the small proof terms inside definitions check structural laws.

Edge cases checked before drafting:

- n = 0: Δ[0] is allowed, the ordered cone is Δ[1], and Q⁰ is the point;
  no positive-dimensional-base assumption appears.
- Empty total space/right fibration and empty-valued presheaves are allowed.
  No nonemptiness binder is present, and the mapping definition handles empty
  simplicial sets. Essential surjectivity does not assert a vertex of E.
- Arbitrary simplex operators, including degeneracies, occur in the mapping
  constructions. The Q-map used is cosimplicial; the face-only topological
  homeomorphisms from the pinched-cube theorem are never used for enrichment.
- Both source cofibrancy and fibrancy are retained for every pair of source
  objects. The target includes arbitrary right fibrations, not only ones already
  presented by unstraightening or a chosen model structure.
- The inverse equations are in mapping-space components over the same base.
  Neither equality of underlying objects nor strict inverse maps is demanded.
- The universe is arbitrary; no equality between independent mathematical size
  parameters is imposed. The auxiliary instantiation of the pinched-cube theorem
  merely reads its Q, endpoints and topological realization in the same u.

Searches performed (the wrapper records exact outputs in `searches.jsonl`):

1. LeanFinder: `Unstraightening is a Dwyer Kan equivalence on projectively
   cofibrant fibrant simplicial presheaves over the standard simplex`.
   Eight results, all ordinary nerve/homotopy-category adjunctions or their
   product comparisons; none states coherent unstraightening over a simplex.
2. Loogle: `DwyerKanEquivalence, EnrichedFunctor`. Zero hits; identifier
   `DwyerKanEquivalence` is unknown to Mathlib's search service.
3. Mathlib grep via msearch: `unstraighten|Dwyer.?Kan`. Zero hits.
4. LeanSearch: `Dwyer Kan equivalence of simplicial categories`. Eight results,
   concerning opposite simplicial objects, simplex skeletal equivalence and
   `SimplicialCategory.homEquiv'`; none is this theorem.
5. Direct rg of the upstream `WeilConjectures` tree for the item id,
   `DwyerKan|unstraighten|Unstraighten`: no hits. Upstream name-index search
   likewise found no matching unstraightening theorem.
6. Direct rg of `lean/Sheaf`: found the raw cone-presheaf adjunction, the
   pinched-cube construction, the general unmarked-straightening theorem, and
   the existing mapping-over-base construction. Their complete relevant
   signatures and documentation were read. None states the present simplex
   Dwyer–Kan theorem with this canonical mapping comparison. The existing
   Dwyer–Kan predicate was read and its clauses reused in expanded form.

Source check: read HTT online at the node's exact source URL, Lemma the project server
and Remark the project server (printed pp. 83 and 78), including the surrounding Lemmas
the project server, the project server and the project server. The ordinary arrow normalization and simultaneous
parameter composition are exactly the simplicial functor construction in the
remark. The source supports the stated result; no STATEMENT-DISPUTED issue or
statement correction was needed.

Validation: prescribed `scompile.py NP lem-coef-unstraightening-simplex-dk-equivalence`
on the delivered module succeeds in sandbox and library mode, within the 60-second
per-file limit, with no warnings or errors. Temporary diagnostic `#check` commands
were removed. The required delivery dry run is the final check; the independent
second reading remains the next worker's task.

## Earlier second reading (a previous round; superseded)

I reread the node statement, its four statement dependencies, the module, and HTT Lemma
the project server with Remark the project server. The source says that, for every integer n ≥ 0,
unstraightening over the standard simplex is an equivalence of simplicial categories on
cofibrant-fibrant diagrams and right fibrations. The node expands this into the following
objects and clauses, which I matched to the Lean signature:

- The object introduced is `(n : ℕ)`, with no positivity hypothesis; the base is exactly
  `(Δ[n] : SSet.{u})`.
- A source object is `F : Presheaf (Δ[n] : SSet.{u})`; the full subcategory condition is
  `IsProjectivelyBifibrant F`, defined in this module as projective cofibrancy together
  with `∀ c, KanComplex (obj F c)`.
- The source mapping simplicial set is the recorded `mapping F G`, whose degree-m
  simplices are the recorded `ParameterMap F G (Δ[m])`, i.e. enriched transformations
  with parameter `F × Δ[m] → G`.
- The target objects are every `E : Over (Δ[n] : SSet.{u})` with
  `Enhanced.rightFibration E.hom`; no target fibrancy, cofibrancy, or nonemptiness is
  added. The first conjunct states this right-fibration property for every bifibrant F.
- The target mapping simplicial set is the existing
  `Enhanced.transportOverHom (rightProjection F) (rightProjection G)`, the subcomplex
  of maps over the fixed simplex. The actual comparison is
  `unstraighteningMapping F G`, built from `parameterMap` and the canonical
  `Q → Δ` data.
- For each bifibrant F and G, the second conjunct gives exactly the local condition
  `Enhanced.IsWeakHomotopyEquivalence (unstraighteningMapping F G)` and the bijection
  on components `Function.Bijective (SSet.mapπ₀ (...))`. The separate
  `parameterMap_functorial`, `parameterLabel_restrict`, and `parameterMap_restrict`
  declarations establish the identity, composition, and simplicial naturality required
  for this comparison to be the enriched unstraightening functor.
- The final conjunct quantifies over every right fibration E and supplies a bifibrant F,
  arrows `f : rightObj F ⟶ E` and `g : E ⟶ rightObj F`, and the two π₀ equalities in
  the existing over-base mapping complexes. These are precisely the component equalities
  for `f ≫ g` and `g ≫ f`, hence essential surjectivity in the node's path-component
  category. The `Over.w` terms retain the required over-`Δ[n]` equations.
- No general-base slice-model assertion occurs in the Lean theorem, matching the final
  sentence of the node.

The helper declarations were checked against the dependency interfaces. `Presheaf`,
`IsProjectivelyCofibrant`, `mapping`, `rightProjection`, `rightObj`, and `rightSetMap`
come from `ConePresheafAdjunction`; `rightFibration` comes from
`InfinityFibrationsOverSimplicialBases`; `transportOverHom` and `transportHomVertex` are
the existing over-base mapping constructions; and the pinched-cube isomorphism and
maximum map are selected from `PinchedCube.pinched_cube_latching`. The module does not
redefine any of these notions.

Edge cases checked: `n = 0` is admitted; empty bases, empty presheaf values, empty total
right fibrations, and zero-dimensional mapping simplices are not excluded; degeneracy
operators are included by `rightRestrict` and `parameterMap_restrict`; the π₀ inverse
conditions are homotopy-component equalities rather than strict inverse equations; and
there is only one explicit universe `u`, so no independent size restriction is imposed.

I repeated the three required searches. LeanFinder returned only standard-simplex and
nerve utilities; Loogle returned no `DwyerKanEquivalence` hit; and the Mathlib/project
`rg` searches found no unstraightening Dwyer–Kan theorem. Direct searches of the upstream
`WeilConjectures` tree and this project's `lean/Sheaf` found only the dependency
constructions, not this theorem. The HTT source check confirms the standard-simplex
restriction and the enriched comparison in Remark the project server.

The returned delivery exposed a namespace collision: the live `Sheaf.CategoryTheory.UnstraighteningHomotopyDescent` module already declares `SSet.ConePresheaf.coneParameter` for path nerve parameters. This item's helper has a different domain and codomain (a coherent mapping object over an arbitrary base simplex), so it is retained under the disambiguating name `coneParameterAt`; the existing declaration remains imported and available for the path-level construction.

The worker left the node's `lean` field unset even though the module compiled. I repaired
that bookkeeping mismatch by recording the exact theorem signature, module, file,
primary declaration, and all helper declarations in the sandbox node copy. I found no
mathematical statement mismatch, no extra hypothesis, no weakened clause, no hollow
definition, and no dependency repair. `scompile.py` compiles the module cleanly with no
warnings or errors.

## Second reading by NP

I reread the node statement, its source place (HTT Lemma the project server, with Lemmas the project server,
the project server, the project server and Remark the project server), every recorded statement dependency, and the
delivered module. The item-by-item match is:

- The object introduced is `(n : ℕ)`, hence every integer `n ≥ 0`; the Lean base is exactly
  `(Δ[n] : SSet.{u})`.
- A source object is `F : Presheaf (Δ[n])`, with the full-subcategory condition rendered
  by `IsProjectivelyBifibrant F := IsProjectivelyCofibrant F ∧ ∀ c, KanComplex (obj F c)`.
  This is projective cofibrancy plus objectwise fibrancy, with no extra condition.
- Source mapping objects are the dependency's `mapping F G`; its degree-`m` simplices are
  `ParameterMap F G (Δ[m])`, the enriched transformations with parameter `Δ[m]`.
- Target objects are all `E : Over (Δ[n])` with `Enhanced.rightFibration E.hom`; the first
  conjunct says `rightProjection F` has exactly this property for each bifibrant `F`.
- Target mapping objects are the existing
  `Enhanced.transportOverHom (rightProjection F) (rightProjection G)`, whose subcomplex
  condition is precisely the over-`Δ[n]` equation in every parameter degree.
- The comparison is the actual `unstraighteningMapping F G`, built from `parameterMap`
  and the canonical `Q → Δ` data. `parameterMap_functorial`,
  `parameterLabel_restrict`, and `parameterMap_restrict` supply identity, shared-parameter
  composition, and simplicial naturality.
- Local equivalence is `Enhanced.IsWeakHomotopyEquivalence (unstraighteningMapping F G)`;
  the additional `Function.Bijective (SSet.mapπ₀ ...)` is the required full-faithfulness
  clause on path components.
- Essential surjectivity quantifies over every right fibration `E` and supplies a
  bifibrant `F`, over-base maps `f` and `g`, and the two π₀ equalities for their composites.
  These are component equalities, not strict inverse equations.
- There is no general-base slice-model assertion or hidden fibrancy/cofibrancy hypothesis.

The dependency interfaces were checked directly: `Presheaf`, `mapping`, the projective
cofibrancy predicate, and `rightProjection/rightObj` come from
`ConePresheafAdjunction`; `rightFibration` is the full outer-right-horn predicate; and
`transportOverHom`/`transportHomVertex` are the existing over-base mapping constructions.
The pinched-cube theorem supplies the normalized isomorphism and maximum map used by the
actual parameter construction. No notion is duplicated and no dependency interface needs
repair.

Edge cases are covered: `n = 0`; empty bases and empty-valued presheaves or right
fibrations; all faces and degeneracies in the simplicial mapping complexes; zero-dimensional
mapping simplices; and arbitrary universe `u` without an imposed equality to another size.
The essential-surjectivity witness does not assert a vertex of the target, and its inverse
conditions remain equalities in π₀ over the fixed base.

Searches were repeated with LeanFinder, Loogle, `msearch.py`, and direct `rg` over Mathlib,
the upstream `WeilConjectures` tree, and this project's `lean/Sheaf`. They found only
ordinary nerve/model-category utilities and the already-recorded cone, pinched-cube,
unstraightening, and over-base mapping constructions; no existing declaration states this
standard-simplex Dwyer–Kan equivalence. The online HTT PDF was checked at the exact lemma
and remark; its conclusion and enrichment agree with the node.

No mathematical mismatch was found and no Lean source change was necessary in this reading.
The only bookkeeping issue remains the worker's missing `lean` record in the shared node;
the sandbox copy records the exact signature, module, declaration, and helper declarations.
The prescribed `scompile.py` check was rerun and passed for both sandbox and library modes.

## Maintainer review fix (cc review service, 2026-10-17, head 2e0948190b54)

This delivery imported two modules whose nodes depend on this item, so it would close a stage-3
import cycle.
- `Sheaf.CategoryTheory.UnstraighteningHomotopyDescent` belongs to
  lem-coef-unstraightening-homotopy-descent. That node cites this item directly in its proof. The
  delivery uses nothing from it: the import was added only after the rename to `coneParameterAt`.
  But a name collision matters only when both modules are imported together, and the rename
  already removes it.
- `Sheaf.CategoryTheory.SpaceTransportClassification` belongs to
  lem-coef-space-transport-classification, which reaches this item through
  simplicial-right-fibration-presentation and unstraightening-homotopy-descent.

The fix makes these changes:
- Both imports are removed. The worker report's bullets that justify them are superseded.
- `transportOverHom`/`transportHomVertex` are replaced by the landed
  `SSet.Enhanced.relativeOperadicDiagrams` (def-coef-relative-symmetric-operadic-algebras, not
  downstream of this item). It is the identical subcomplex
  `{h | ∀ k a z, q (h a z) = p z}` of `ihom E E'`, so its m-simplices are the maps
  E × Δ[m] → E' over the base, exactly Fun_{/Δ[n]}(E,E') as the node states.
- A new vertex helper `SSet.ConePresheaf.overHomVertex` is added, with real data
  (`diagramVertex f` and the over-base equation) and listed in lean.declarations.

The fix keeps the group's rename `coneParameterAt`, which avoids a clash with the live
`SSet.ConePresheaf.coneParameter` of UnstraighteningHomotopyDescent. It also adds `import` lines
for the stated proof dependencies that have modules (stages/2-statements.md rule 7). The main
docstring now carries the node's 13 proof steps with the nodes they use.

The theorem's clauses are otherwise unchanged. The fixed file compiles clean through
nt_compile.py.
