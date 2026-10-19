## Worker report

This delivery states `CategoryTheory.exists_enriched_functorial_factorization` in
`Sheaf.CategoryTheory.EnrichedFunctorialFactorizations`. Its only postponed theorem
is the item itself; the proof is exactly `by sorry`. Its docstring supplies the ten
DAG proof steps. The canonical arrow enrichment is constructed from Mathlib's
`Enriched.FunctorCategory.enrichedOrdinaryCategory`, with no postponed data.

The item statement is unchanged. Hypotheses and conclusions match as follows:

- The universe U is `v`; category objects have independent universe `u`.
  `(C : Type u) [Category.{v} C] [SimplicialCategory C]` supplies U-small mapping
  simplicial sets, associative simplicial composition and identity vertices, and
  identifies ordinary morphisms with vertices through Mathlib's `eHomEquiv` and
  `SimplicialCategory.homEquiv'`.
- Small colimits and limits are `[HasColimitsOfSize.{v, v} C]` and
  `[HasLimitsOfSize.{v, v} C]`. These are exactly the U-small shapes, including
  empty shapes; no size equality is imposed on category objects.
- Local presentability is `[IsLocallyPresentable.{v} C]`. Its defining existential
  cardinal carries `Cardinal.IsRegular` (which includes infinitude), and
  `IsCardinalLocallyPresentable` supplies a small family of cardinal-presentable
  objects generating under cardinal-filtered colimits. `IsCardinalFiltered` uses
  the size of `Arrow A`, exactly the number of morphisms in the node's definition.
- `T : SimplicialTensorCotensor C` supplies both enriched adjunctions, as canonical
  isomorphisms induced by universal elements (see the new-node paragraph below).
  It asserts tensors and cotensors for every `K : SSet.{v}`.
- `J : MorphismProperty C` with `[J.IsSmall.{v}]` is a small set of actual arrows:
  Mathlib's `IsSmall` says that `J.toSet : Set (Arrow C)` is U-small. It does not
  require a small isomorphism-closed class or a model structure.
- `R` and `L` are written as Mathlib's `J.rlp` and `J.rlp.llp`. Their definitions
  quantify over ordinary `HasLiftingProperty` squares and diagonal fillers.
- `hT` quantifies over every small simplicial set and every actual generator,
  requiring `J.rlp.llp (T.tensorMap K j)`. `tensorMap` is the canonical arrow
  obtained by the inverse universal isomorphism; it is not extra arbitrary data.
- `Arr_Delta(C)` is represented by `ComposableArrows C 1 = Fin 2 ⥤ C`. Any
  arrow `f` gives `ComposableArrows.mk₁ f`; conversely the diagram's `hom` is
  its single arrow. Mathlib's enriched end on these diagrams imposes only the
  endpoint square condition: the identities add no condition. This is the
  canonical simplicial arrow category from Riehl equation (13.1.1), presented as
  an isomorphic diagram category, with no restriction on arrows.
- `E : EnrichedFunctor SSet.{v} (ComposableArrows C 1) C` provides object values
  and simplicial maps of hom-objects preserving identities and composition.
- The dependent functions `i` and `p` give the two component vertices.
  The first three conjuncts state respectively `i f ≫ p f = f.hom`,
  `J.rlp.llp (i f)` and `J.rlp (p f)` for every arrow.
- The final two conjuncts are equalities of simplicial maps on the full enriched
  hom-object. The endpoint projections are `enrichedHomπ ... 0` and
  `enrichedHomπ ... 1`. The equations are exactly `E(b,c) i_f = i_g b` and
  `p_g E(b,c) = c p_f`. Thus all simplicial parameters, faces and degeneracies
  are retained, rather than only naturality on vertices.

Dependency declarations read and used:

- `def-weil-pbc-simplicial-set`: Mathlib.AlgebraicTopology.SimplicialSet.Basic,
  `SSet` (functors from `SimplexCategoryᵒᵖ` to `Type v`). Its recorded additional
  clauses in Degenerate, Subcomplex and Finite were also read; this theorem uses
  only simplicial sets and their natural transformations.
- `def-weil-pbc-category-colimit`: Mathlib.CategoryTheory.Limits.HasLimits,
  `Limits.colimit`, `Cocone`, `IsColimit`, `colimit.desc`; the signature and
  to-dual-generated chosen-colimit definition were read. The hypothesis uses
  `HasColimitsOfSize`; actual colimits and their canonical maps occur in the
  documented construction. Small limits are supplied by `HasLimitsOfSize`.
- The added `def-coef-simplicial-tensor-cotensor` uses the definitions and
  canonical tensor map in `Sheaf.CategoryTheory.SimplicialTensorCotensor`.
- Other Mathlib notions used: `SimplicialCategory` / `EnrichedOrdinaryCategory`,
  `eComp`, `eHomWhiskerLeft`, `eHomWhiskerRight`, `EnrichedFunctor`,
  `Enriched.FunctorCategory.enrichedOrdinaryCategory` and `enrichedHomπ`,
  `MonoidalClosed.curry`, `MorphismProperty.rlp`, `.llp`, `.IsSmall`,
  `IsLocallyPresentable`. Their full defining signatures were read.

Every stated proof dependency is imported: LocallyPresentable for object ranks,
HasCardinalLT for the regular bound, RelClasses for transfinite recursion,
LiftingProperty for lifting-class closure, TransfiniteCompositionLifting for
continuous composition, Types.Filtered for elementwise colimits, and HasLimits
for colimits. No proof-only dependency is omitted and no import cycle is introduced.

Edge cases checked before writing: `J` empty gives `R = all arrows`, `L` the
isomorphisms, and identity/domain factorization. The zero/empty simplicial set
is allowed by the tensor hypothesis. The terminal one-object category is allowed.
Empty category objects are not separately prohibited; the assumed empty colimit
already implies an initial object. Arbitrary non-cofibrant endpoints are allowed.
No model category or endpoint cofibrancy hypothesis appears. Object universe `u`
is unrestricted relative to the hom/simplicial-set universe `v`.

Searches for the item and the missing notion (actual msearch searches):

- LeanSearch: "A simplicially enriched category has functorial factorizations by
  the enriched small object argument". Hits include ordinary SmallObject
  factorizations and SimplicialCategory; none gives the enriched conclusion.
- LeanFinder: "Enriched simplicial functorial factorization small object argument
  tensor copowers". Eight hits about tensors in the augmented simplex category,
  simplicial enrichment and closed simplicial sets; no factorization match.
- Loogle: `"EnrichedFunctor", "FunctorialFactorizationData"`: zero hits.
- Mathlib grep: `enriched.*small.object|small.object.*enriched`: zero hits in
  CategoryTheory. An earlier broader grep also matched unrelated TensorLE and
  Day convolution code, with no relevant result.
- For tensors/cotensors, LeanSearch query "A tensor or cotensor in a simplicial
  category represents the enriched hom functor" and LeanFinder query "Tensor
  and cotensor of an object in a simplicial category enriched adjunction" find
  hom-functors and SSet's monoidal closed structure, not tensors in a general
  enriched category. Loogle `"SimplicialCategory", "cotensor"` gives zero hits.
  Mathlib grep `cotensor|simplicial tensor` in CategoryTheory finds only the
  unrelated cotensorator of an oplax monoidal functor.
- Direct rg of WeilConjectures and lean/Sheaf for simplicial tensor/cotensor
  names and enriched small-object arguments gives zero hits; exact new names
  were also absent. Search for this item's id in WeilConjectures gives no match.
  `tools/blueprint_refs.py search 'simplicial tensor'` gives zero nodes. The
  definition nodes of sec-six-functors contain no tensor/cotensor definition;
  the generic theorem and the simplicial model/diagram nodes mention the notion
  but do not define it. `dag/lean_names_upstream.json` contains no matching names.

Source checked directly: Riehl's PDF was downloaded into the sandbox scratchpad
and its sections 3.6--3.7, 13.1--13.2 and Theorem 12.5.1 were read, including
Definitions 3.7.2--3.7.3, Remark 3.7.4, equation (13.1.1), and Theorem 13.2.1.
The all-K tensor assumption is the node's sufficient condition for Riehl's
attaching-square condition. The relevant current blueprint proof was also read.
No statement correction, disputed statement or unusable dependency was found.

## New nodes

`def-coef-simplicial-tensor-cotensor` defines chosen tensors/cotensors in a
simplicial category by universal elements and canonical representing isomorphisms.
Its source is Riehl, Definitions 3.7.2--3.7.3 and Remark 3.7.4 (printed p.38).
The Mathlib simplicial-category module explicitly leaves simplicial tensors as a
TODO; the searches above and the new node's raw search records found no existing
notion. This is an independent definition, not a restatement of the item theorem.
Its only prerequisite is the existing simplicial-set node.

The structure fields `tensor`, `tensorUnit` and `tensor_isIso` specify
`Map(K tensor X,Y) ≅ [K,Map(X,Y)]`, where the comparison curries composition
with `tensorUnit`. The cotensor fields specify
`Map(X,Y^K) ≅ [K,Map(X,Y)]`; the symmetry swaps the parameter K past the
mapping object before composition with `cotensorCounit`. Since these are the
canonical maps induced by universal elements, enriched naturality follows from
the enriched category laws; arbitrary, non-natural objectwise isomorphisms
would not suffice. On vertices, the inverse tensor comparison sends
`tensorUnit K Y` precomposed by f to `tensorMap K f`. All data are real
structure fields or this explicit canonical construction; there is no sorry
in the definition module. The item cites the new node in stmt_deps.

## Validation

Both files are compiled separately in dependency order with the prescribed
scompile.py wrapper. Earlier diagnostics (named argument order of Mathlib's
functor-category enrichment and line wrapping) were repaired. `autoImplicit`
is explicitly false in both modules. The required deliver2.py --no-push dry run
is the final check; the second reader supplies its independent report and delivers.

## Second reading by Q63

I independently read the item node, both delivered modules, the new definition
node, the two original statement-dependency records and their Mathlib declarations.
There is no repair note for this item and no statement_change. Source checked:
the sandbox's Riehl Categorical Homotopy Theory text, Definitions 3.7.2--3.7.3,
Remark 3.7.4 (printed p.38), section 13.1 including (13.1.1) (p.176),
Theorem 13.2.1 and its proof (pp.177--178), and the smallness condition (*)
after Theorem 12.5.1 (p.159). This is not a Stacks-sourced node. Section 13.1
assumes completeness, cocompleteness, tensors and cotensors throughout; all four
are explicit here. The source's attaching-square condition follows from the
node's stated all-K tensor condition, without a model-category assumption.

My object/hypothesis/conclusion checklist, in the order of the node:

1. Universe U and an underlying category with U-small mapping simplicial sets:
   `universe v u`, `(C : Type u) [Category.{v} C] [SimplicialCategory C]`.
   I read `SimplicialCategory := EnrichedOrdinaryCategory SSet.{v} C`, its
   `homEquiv` identity/composition axioms and `homEquiv'` to zero-simplices.
   This gives exactly the stipulated enrichment and underlying vertices. PASS.
2. All U-small colimits and limits: `HasColimitsOfSize.{v, v} C` and
   `HasLimitsOfSize.{v, v} C`. I read both class signatures and the recorded
   `Limits.colimit` (generated from `limit`), `Cocone`, `IsColimit` and
   canonical descent interface. The shape universe is v, not u. PASS.
3. Locally presentable in the stated ordinary sense:
   `IsLocallyPresentable.{v} C`. I read its existential regular cardinal and
   `IsCardinalLocallyPresentable`, `HasCardinalFilteredGenerator`, and
   `IsCardinalFiltered.nonempty_cocone`: its cardinal bound is on `Arrow A`,
   hence counts morphisms as required. No larger-universe colimits or
   extra finiteness assumption have been introduced. PASS.
4. Tensors and cotensors with both enriched natural adjunctions:
   `(T : SimplicialTensorCotensor C)`. Its `tensorUnit` followed by composition
   and `curry` gives `Map(K tensor X,Y) -> [K,Map(X,Y)]`; `tensor_isIso`
   requires that canonical map to be invertible. The cotensor comparison
   swaps K past `Map(X,Y^K)` and composes with `cotensorCounit`, yielding
   `Map(X,Y^K) -> [K,Map(X,Y)]`. These universal-element maps are enriched
   natural by associativity. They encode the source's representing property,
   rather than arbitrary objectwise bijections. PASS.
5. A small set J of actual morphisms: `(J : MorphismProperty C) [J.IsSmall.{v}]`.
   I read `IsSmall.small_toSet` and `isSmall_iff_eq_ofHoms`: smallness is of
   the subset of `Arrow C`, exactly a small family of generators. PASS.
6. Ordinary right class R and ordinary left class L: `J.rlp` and `J.rlp.llp`.
   I read their definitions in MorphismProperty.LiftingProperty: each quantifies
   over ordinary `HasLiftingProperty`, with no chosen or enriched fillers. PASS.
7. Every small K and generator j has `K tensor j` in L: `hT` has precisely
   these quantifiers and uses `T.tensorMap K j`. I traced `tensorMap`: the
   right unitor makes the input K tensor unit, currying turns the generator's
   precomposed universal element into a vertex, the inverse canonical tensor
   comparison gives a vertex in the tensor Hom, and `eHomEquiv.symm` gives
   the ordinary arrow. This is the actual canonical tensor of j. PASS.
8. The specified simplicial arrow category: `ComposableArrows C 1` is
   definitionally `Fin 2 ⥤ C`. The instance `simplicialArrowCategory` uses
   Mathlib's `enrichedOrdinaryCategory`, not new mapping data. I read its end,
   `enrichedHomπ` and `enrichedHom_condition`. For Fin 2 the single nonidentity
   condition is exactly `g b = c f`; the identity conditions are automatic.
   Every arrow has the constructor `ComposableArrows.mk₁`, so no arrows or
   simplicial parameters are lost through this presentation. PASS.
9. A simplicial middle-object functor: the first existential is
   `E : EnrichedFunctor SSet.{v} (ComposableArrows C 1) C`. I read
   `EnrichedFunctor.obj`, `.map`, `.map_id` and `.map_comp`: these are exactly
   objects and simplicial maps preserving identities and composition. PASS.
10. For every arrow f, two component vertices and the factorization and classes:
    the dependent functions `i` and `p` have the stipulated endpoints. The first
    three conjuncts give `i f ≫ p f = f.hom`, `J.rlp.llp (i f)` and
    `J.rlp (p f)`. No endpoint cofibrancy or model structure is assumed. PASS.
11. Enriched naturality of i: the fourth conjunct says, on the full enriched
    hom-object, projection to b followed by postcomposition with i_g equals
    E's action followed by precomposition with i_f. This is `i_g b = E(b,c)i_f`
    in every degree. I checked the directions of both eHomWhisker operations.
    PASS.
12. Enriched naturality of p: the last conjunct is postcomposition of E's action
    with p_g equal to precomposition of c with p_f, or `p_g E(b,c) = c p_f`.
    Both sides are maps of simplicial sets, so faces, degeneracies and all
    higher parameters are included. Existentials precede the universal arrows,
    giving a global factorization choice as required. PASS.

Edge cases: empty J is allowed by IsSmall and hT and gives identities followed
by f (L is the isomorphisms, R all arrows). K may be the empty simplicial set
or Delta[0]; there is no nonemptiness or positive-degree binder. Empty colimit
and limit shapes are included. The empty category cannot satisfy cocompleteness,
exactly as in the node; the terminal one-object category and categories with
zero objects are not excluded. Schemes, rings and characteristics do not occur.
The two universes u and v are independent, with no imposed equality or ordering.

New node review (H12): `def-coef-simplicial-tensor-cotensor` is an independent
missing notion, not a new theorem. Its statement agrees with the source's tensor
and cotensor adjunctions and fixes their canonical maps by universal elements.
Both comparisons and `tensorMap` in its module were checked above. Its fields
have the required definition/split status, same chapter and unit, empty proof
and proof_deps, null mathlib_match/proof_origin, all three search kinds, worker
creation record, ancestor/via and none/none lean_audit; the item cites it.
No dependency module is delivered. The arrow instance reuses the existing
Mathlib enrichment construction, and has no postponed data.

Independent duplicate searches on 2026-10-17:

- LeanFinder via msearch: "Simplicial enriched small object argument factorization
  with simplicially natural legs" returned ordinary SmallObject factorization
  and its naturality lemmas, which lack actions on simplicial mapping objects.
- LeanFinder: "An enriched category admits tensors and cotensors representing
  its enriched hom objects" returned enriched categories, conical limits and
  self-enrichment, not a tensor/cotensor interface for arbitrary C.
- LeanSearch: "Tensors and cotensors representing enriched hom functors in a
  simplicial category; enriched small object argument" returned eHomFunctor,
  sHomFunctor, SimplicialCategory and functor-category enrichments; none is the
  statement or the missing definition. The existing functor enrichment is used.
- Loogle: `"EnrichedFunctor", "FunctorialFactorization"` returned zero hits.
- Direct rg in Mathlib CategoryTheory and AlgebraicTopology/SimplicialCategory,
  upstream WeilConjectures, and project lean/Sheaf with enriched/factorization,
  small-object, cotensor, tensored and copowered terminology found no duplicate.
  The general simplicial tensor remains an explicit TODO in Mathlib's Basic.
  I inspected the project hit MarkedPointCartesianModel: its tensor/cotensor
  fields concern only marked simplicial sets, not arbitrary simplicial C.
  SheafFlatModel is about cochain-complex enrichment, and cotensorators of
  pullback functors are another notion. DAG definition-node searches for
  tensored/cotensored notions found none; exact names and simplicial tensor/
  cotensor patterns in dag/lean_names_upstream.json found no collision.

H5/H6/H8/H9: both modules have explicit `autoImplicit false`, bound universes,
source/blueprint docstrings and no private or local API. The item's only theorem
has proof `by sorry`; its docstring follows all ten node proof steps, and its
proof dependencies' Mathlib modules are imported. Both definitions have real
structure data or canonical constructions. Both lean.statement strings were
checked verbatim against their module signatures. All Lean lines are at most
100 characters. Both sibling modules compiled cleanly through the prescribed
scompile.py invocation, separately and in dependency order, with no diagnostics.

Mismatches found: none. Changes: appended this independent second-reading report;
Lean modules, mathematical statements and node records are unchanged.
