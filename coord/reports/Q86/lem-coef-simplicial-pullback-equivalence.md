## Worker report

The module `Sheaf.AlgebraicTopology.SimplicialPullbackEquivalence` states
`SSet.simplicial_pullback_equivalence`, with exactly one postponed theorem and no
new definitions. Its proof is `sorry`. The declaration's docstring contains all
six steps of the node's natural-language proof. The previous attempt left only
dispatcher markers; this delivery supplies the missing module, node and report.

Hypothesis and clause correspondence:

- Small simplicial categories with associative, unital simplicial composition:
  `{A B C : SCat.{u}}`. This is the existing
  `CategoryTheory.CoherentNerve.SCat`, bundling Mathlib's
  `EnrichedCategory SSet`; its identity, associativity and composition laws are
  actual proof fields. Objects and all mapping simplices lie in `u`, which is
  explicitly bound and arbitrary.
- Simplicial functors `p : A → B` and `q : C → B`:
  `(p : A ⟶ B) (q : C ⟶ B)` in `sCatCategory`. These arrows are
  `EnrichedFunctor SSet A B` and `EnrichedFunctor SSet C B`, with their genuine
  unit and composition preservation laws, and arbitrary object functions.
- Every mapping map of `p` is a Kan fibration:
  `_hp : ∀ a a' : A, SSet.modelCategoryQuillen.J.rlp (p.map a a')`.
  This is exactly the horn lifting property, using the dependency's recorded
  Mathlib fibration class, not a choice of another model structure.
- Form the strict pullback `E = A ×_B C`:
  `(E : PullbackCone p q) (_hE : IsLimit E)`. This is a limit in the
  **ordinary category of enriched functors**, so its square commutes by equality
  of enriched functors. It is not a categorical pseudopullback or an enhanced
  homotopy pullback. In particular `E.condition` imposes equality of object
  images and of the simplicial mapping maps. Its universal property is exactly
  the strict enriched pullback universal property. The coordinate model has
  objects `{ac : A × C // p.obj ac.1 = q.obj ac.2}` and degreewise compatible
  pairs of mapping simplices, with componentwise units and composition. Any
  `IsLimit E` is uniquely isomorphic to that model as a cone. Thus using a
  limit cone is the standard choice-independent expression of “form the strict
  pullback,” not an extra mathematical restriction on `p` or `q`, and not an
  unspecified comparison map. No data is selected by `Nonempty` or `sorry`.
- A vertex with arbitrary endpoints in the pullback:
  `{x y : E.pt} (e : (EnrichedCategory.Hom x y) _⦋0⦌)`.
- Invertible in `π₀ E`: the left side of `↔` is an inverse vertex `d` in the
  reverse mapping set and both equations in Mathlib's `SSet.π₀` quotient.
  `eComp SSet x y x` on `(e,d)` equals the identity component at `x`, and
  `eComp SSet y x y` on `(d,e)` equals the identity component at `y`.
  Every component has a vertex representative, so this says precisely that
  the vertex's class is invertible in the component category.
- Projection to `A`: the first conjunct on the right states the same two inverse
  equations for `(E.fst.map x y).app _ e`, at endpoints `E.fst.obj x/y`.
- Projection to `C`: the second conjunct states the same equations for
  `(E.snd.map x y).app _ e`, at endpoints `E.snd.obj x/y`.
- “If and only if” is `↔`, and the two projected conditions are joined by `∧`.
- “No mapping set is assumed Kan” and “neither functor lifts equivalences on
  objects”: there is no such binder, instance or condition. Only the specified
  local horn lifting property for `p` is imposed. In particular nothing is
  assumed about the local fibration behavior of `q`.

Dependency declarations read and used:

- `def-weil-pbc-simplicial-set` is a Mathlib leaf: `SSet` in
  `Mathlib.AlgebraicTopology.SimplicialSet.Basic`. I also read its matched
  `SSet.degenerate`, `SSet.nonDegenerate`, `SSet.Subcomplex` and `SSet.Finite`;
  those ancillary notions do not occur in this statement.
- `lem-coef-kan-quillen-right-proper` records
  `Sheaf.AlgebraicTopology.KanQuillenRightProper`,
  `SSet.KanQuillen.right_proper_kan_quillen`. Its full signature and docstring
  identify fibrations with `SSet.modelCategoryQuillen.J.rlp` and supply exactly
  the arbitrary-base right properness used in the proof. The module is a public
  import, and no replacement weak-equivalence or fibration class is defined.
- Added the already landed `def-coef-coherent-nerve-infrastructure` to
  `stmt_deps`, to use its recorded module
  `Sheaf.CategoryTheory.CoherentNerveInfrastructure`, declarations
  `CategoryTheory.CoherentNerve.SCat` and `sCatCategory`. I read the definition
  node and its recorded source. This reuses the actual ordinary category of
  small simplicial categories; it is not a new definition. Following its
  statement/proof dependency closure does not reach this item.
- `Mathlib.AlgebraicTopology.SimplicialSet.PiZero`: `SSet.π₀` and `SSet.π₀.mk`.
  Its quotient identifies precisely finite zigzags of edges, with no Kan
  assumption. `π₀.mk_surjective` justifies the representative description.
- Mathlib's `PullbackCone`, `IsLimit`, `PullbackCone.fst/snd` express the strict
  pullback and its canonical projections. The enriched functor laws, `eComp`
  and `eId` are the existing Mathlib declarations.
- The stated proof dependency `lem-coef-realization-finite-limits` is imported
  without `public`: `Sheaf.AlgebraicTopology.RealizationFiniteLimits`, theorem
  `SSet.realization_finite_limits`.
- `lem-coef-homotopy-groups-basepoint-change` has no recorded Lean declaration
  or Mathlib match, so its module cannot yet be imported. Its statement remains
  explicitly cited in the proof docstring. It is only a proof dependency.

Edge cases checked before drafting: empty object sets give no endpoints and the
statement remains universal; empty mapping sets give no vertex to test; `x = y`
and coincident images are allowed; identity vertices and either functor equal
to an identity are included. For discrete mapping sets the statement reduces
to the usual strict categorical pullback inversion test. In general inverse
vertices need only satisfy equations on components, rather than strict inverse
equations. All degrees and both edge orientations are retained by `SSet.π₀`.
Arbitrary non-Kan mapping sets and an arbitrary (not locally fibrant) base are
allowed. The common arbitrary universe includes all small input diagrams after
choosing a common universe; no object/morphism size equality is imposed on a
site or other unrelated category.

Searches made, using `msearch.py` (records in sandbox `searches.jsonl`):

- LeanSearch: “A strict pullback of simplicial categories along a local Kan
  fibration detects invertible morphisms on components”. Eight results concern
  horn lifting, fibrations stable under base change, finite simplicial
  pullbacks and ordinary categorical pullbacks; none states this theorem.
- LeanFinder: “A strict pullback of simplicial enriched categories along a
  mappingwise Kan fibration detects invertible morphisms in the component
  category”. Results concern quasi-category enrichment, conical pullbacks
  inside an enriched category, strict Segal objects and simplicial fibrations;
  no equivalence-detection theorem for the category of simplicial categories.
- Loogle: `"EnrichedCategory", "pullback"`: zero results.
- Mathlib grep: `Enriched.*[Pp]ullback|[Pp]ullback.*Enriched|IsEquivalenceVertex`:
  zero results. Direct source inspection of `CategoryTheory/Enriched/` found
  `HasConicalPullback`, which concerns pullbacks inside a fixed enriched
  category, not the strict pullback category used here.
- Project source grep: `SimplicialCategory|simplicial.*pullback|IsEquivalenceVertex`
  in upstream `WeilConjectures/`: no match. Search by this node id also gave
  no match. Exact declaration-name searches in Mathlib, upstream, side Lean
  and `dag/lean_names_upstream.json` found no existing statement.
- Side Lean searches found the reusable coherent-nerve infrastructure and the
  downstream `SimplicialIntervalLifting.lean`. The latter has an
  `IsEquivalenceVertex` abbreviation, but its theorem depends on this item.
  We therefore expand the inverse equations in this statement instead of
  importing that downstream module or creating a duplicate definition.

Source checked: [Bergner, arXiv math/0406507](https://arxiv.org/pdf/math/0406507),
Section 1's definition of components and the strict pullback in Proposition 2.5,
printed p. 8 (PDF page 8). This node supplies the implicit compatibility step;
it does not import or assert the global Bergner model structure.

No statement correction, new nodes, dependency-module repairs or disputed
statement. The sole node delta is `lean` and the added landed infrastructure
statement dependency. The node JSON uses indent 1, Unicode and a final newline;
its Lean signature is copied verbatim from the module. All universes and
variables are explicitly bound. No file-local notation or instance is used.

Validation: the prescribed `scompile.py Q86
lem-coef-simplicial-pullback-equivalence <module>` compiled both its sandbox and
library forms cleanly, in 1.6 s and 1.8 s respectively, under the default
60-second per-file limit. No compiler warnings or errors. The independent
second reading and delivery remain with the second reader.

## Second reading by Q86

The node introduces the following data, checked in order against the source
description and the Lean signature:

1. A small simplicial category is rendered by
   `CategoryTheory.CoherentNerve.SCat.{u}`, the existing bundled enriched
   category of simplicial sets. Its object type, mapping simplicial sets,
   units, and associative composition are supplied by `EnrichedCat`.
2. The functors `p : A ⟶ B` and `q : C ⟶ B` are ordinary arrows in the
   landed `sCatCategory`, hence enriched functors with their object and mapping
   maps and preservation laws. No object-level lifting condition is added.
3. The hypothesis that every `A(a,a') → B(pa,pa')` is a Kan fibration is
   exactly `_hp : ∀ a a' : A, SSet.modelCategoryQuillen.J.rlp (p.map a a')`.
   This is the recorded Kan–Quillen horn-lifting class from
   `lem-coef-kan-quillen-right-proper`; no finiteness, fibrancy, or condition
   on `q` is present.
4. The strict pullback is rendered by `(E : PullbackCone p q) (_hE : IsLimit E)`
   in the ordinary category `SCat`. Thus `E.pt`, `E.fst`, and `E.snd` are the
   compatible object/mapping pullback and its canonical projections. The limit
   cone is only the choice-independent expression of the strict pullback.
5. An arbitrary pullback object pair and degree-zero vertex are rendered by
   `{x y : E.pt}` and `e : (EnrichedCategory.Hom x y) _⦋0⦌`.
6. The left side expands invertibility in `π₀ E` as an existential reverse
   vertex `d` and the two component equalities for `eComp` against `eId`.
   The first right-hand existential is the identical condition for
   `(E.fst.map x y).app _ e` in `A`; the second is the identical condition for
   `(E.snd.map x y).app _ e` in `C`. They are joined by `∧` and have the same
   quantifier order as the node. There is no Kan assumption on mapping sets
   and no equivalence-lifting assumption on either functor.

Edge cases were rechecked: empty object types and empty mapping simplicial sets
make the universal statement vacuous where appropriate; `x = y`, coincident
images, identity functors, identity vertices, and zero-dimensional simplices
are all admitted; discrete mapping sets reduce to the ordinary pullback
criterion; arbitrary universes are represented by the single explicitly bound
`u`, with no forced site or morphism universe equality.

I reread the recorded dependency declarations for the Kan–Quillen right proper
interface and the coherent-nerve infrastructure, and searched Mathlib,
upstream `WeilConjectures`, side Lean, and DAG names for an existing enriched
pullback equivalence statement or duplicate notion. The searches found only
ordinary categorical pullbacks, simplicial-set fibration infrastructure, and
the downstream interval-lifting abbreviation, so no existing declaration can
replace this theorem. The source checked is Bergner, Proposition 2.5, printed
p. 8; its pullback is the strict enriched pullback used here. Section 1 defines
homotopy equivalences as vertices becoming isomorphisms in the component
category. Proposition 2.5 also assumes object-level equivalence lifting for
its own conclusion, but the node is explicitly an agent expansion of the
pullback compatibility step, whose six-step mapping-space proof requires only
the local fibration assumption; that stronger hypothesis is not imported.

Independent search log, also recorded in `searches.jsonl`:

- LeanFinder: “An enriched pullback of simplicial categories reflects
  equivalences if one projection to the base is locally a Kan fibration”.
  Eight hits: enriched conical pullbacks, nerve reflectivity, and stability
  of fibrations/trivial fibrations; none states this result. A conical
  pullback is inside one enriched category, not a pullback of categories.
- Loogle: `"EnrichedFunctor", "π₀"`, zero hits.
- LeanSearch: “In a cartesian square of simplicial categories a vertex is a
  homotopy equivalence when both its images are, provided one mapping-space
  functor is a fibration”. Eight hits: ordinary pullback squares, fibrations,
  and product comparison for the simplicial-set homotopy-category functor;
  none is the enriched strict-pullback assertion.
- `rg`: `pullback.*(equivalence|invertib)|(?:equivalence|invertib).*pullback`
  and `IsEquivalenceVertex`, plus the exact declaration name, across upstream,
  Mathlib enrichment and simplicial sets, side Lean, and upstream DAG names.
  No existing theorem matches. The downstream interval-lifting abbreviation
  is deliberately not imported, avoiding a dependency cycle; no new
  equivalence-vertex definition is introduced here.

No mismatch was found. The worker's added `def-coef-coherent-nerve-infrastructure`
statement dependency is required by the actual `SCat` declaration and is
already landed. I made no change to the theorem statement or module. The node's
`lean.statement` remains verbatim equal to the signature in the file, and the
prescribed `scompile.py` check passes for both sandbox and library forms with
no diagnostics other than the allowed postponed proof.
