## Worker report

The module `Sheaf.CategoryTheory.CocartesianInnerHornComparison` states
`SSet.Enhanced.cocartesian_inner_horn_comparison`, with its sole theorem proof `sorry`.
No definition or hypothesis has been replaced, no node statement was corrected, and
there are no new nodes or dependency repairs. Its declaration docstring contains all
seven DAG proof steps and the nodes each step uses.

Source checked: Higher Algebra, Lemma the project server, printed pp. 307–309, downloaded from
https://www.math.ias.edu/~lurie/papers/HA.pdf into this sandbox's scratchpad and read
with pdftotext. The source asks for a map of quasicategories to the standard simplex
and cocartesian lifts from every object in the preceding fiber. This is precisely
the node's statement. The standard simplex is a quasicategory; the node explicitly
states the inner-fibration condition, retained here. The node's monomorphism clause
is the literal inclusion in the source. The source's second filtration says
“nondecreasing” while putting the maximal simplex first; the node has already
corrected that to nonincreasing, and the docstring preserves the corrected plan.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Small simplicial sets | `C : SSet.{u}`; the standard simplex and horn have the same universe. |
| Dimension N and missing vertex i | `N : ℕ`, `i : Fin (N + 1)`. |
| `0 < i < N` | `hi : 0 < i`, `hiN : i < Fin.last N`. These entail `N ≥ 2`. |
| C is a quasicategory | `[Quasicategory C]`. |
| Inner fibration to the standard simplex | `q : C ⟶ (Δ[N] : SSet.{u})`, `[InnerFibration q]`. |
| Every x in the fiber at i−1 | `hlift` quantifies `x : C _⦋0⦌` with `stdSimplex.obj₀Equiv (q.app (op ⦋0⦌) x) = ⟨i.val - 1, by omega⟩`. |
| There is an edge x → y | `∃ (y : C _⦋0⦌) (e : C _⦋1⦌), C.δ 1 e = x ∧ C.δ 0 e = y`. The face `δ 1` is the source. |
| y lies in the fiber at i | `stdSimplex.obj₀Equiv (q.app (op ⦋0⦌) y) = i`. |
| The edge lies over i−1 → i | `SSet.yonedaEquiv.symm e ≫ q = SSet.stdSimplex.map (SimplexCategory.mkOfSucc ⟨i.val - 1, by omega⟩)`. `mkOfSucc` selects successive vertices in the standard simplex. |
| That edge is q-cocartesian | `IsCocartesianEdge q (SSet.yonedaEquiv.symm e)`, using the recorded dependency's exact outer-horn lifting definition. |
| The displayed canonical pullback inclusion | `pullback.fst q (horn N i).ι`. Its domain is `pullback q (horn N i).ι`, ordered as `C ×_{Δ[N]} Λ[N,i]`, and its codomain is C. No map is assumed or chosen as an additional parameter. |
| Categorical equivalence | For every `D : SSet.{max u v}` with `D.Quasicategory`, `((hoFunctor.map ((MonoidalClosed.pre (uliftFunctor.{v, u}.map (pullback.fst q (horn N i).ι))).app D)).toFunctor).IsEquivalence`. This is the testing signature in `exists_joyal_model_structure`, verbatim for this particular canonical map. |
| Monomorphism | `Mono (pullback.fst q (horn N i).ι)`, equivalent to degreewise injectivity in the simplicial presheaf category. |
| No lifts over other edges or colimits are assumed | There is only the single-edge `hlift` binder; no cocartesian-fibration instance, global family of lifts, or colimit structure is required. |

The explicit y and its fiber equation merely spell out the node's given target;
they do not strengthen the edge-lifting condition. The `by omega` terms only prove
that the natural-number predecessor fits in the relevant finite ordinal. No
mathematical theorem is proved by these index bounds. Every variable and universe
is bound explicitly, with `set_option autoImplicit false`.

Dependency interfaces read and used:

- `def-cbc-enhanced-diagrams-cones`: `Sheaf.CategoryTheory.EnhancedDiagramsCones`, `SSet.Enhanced.coneCategory`.
- `def-coef-infinity-fibrations`: `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases`, `SSet.Enhanced.cocartesianFibrationOver`.
- `lem-coef-joyal-model-structure`: `Sheaf.AlgebraicTopology.JoyalModelStructure`, `SSet.exists_joyal_model_structure`.

The enhanced-diagram node explicitly uses Mathlib's `SSet`, `stdSimplex`, `horn`,
and `Quasicategory`; these are reused directly. The recorded
`InfinityFibrationsOverSimplicialBases` module publicly reexports
`InfinityFibrations`, whose full `IsCocartesianEdge` definition and documentation
were read. We use that declaration, and Mathlib's `InnerFibration`, rather than
requiring the stronger `cocartesianFibrationOver` predicate. The Joyal node's full
signature and docstring were read: its exact `hoFunctor`/`MonoidalClosed.pre` test,
including `uliftFunctor` and enlargement `max u v`, is the conclusion here. It has
no separate named categorical-equivalence predicate to duplicate.

The following already-stated proof dependencies are imported non-publicly as the
stage-3 plan requires:

- `lem-cbc-equivalence-outer-horn-filling`: `Sheaf.CategoryTheory.EquivalenceOuterHornFilling`.
- `lem-cbc-mapping-simplex-universal-equivalence`: `Sheaf.CategoryTheory.MappingSimplexUniversalEquivalence`.
- `lem-coef-all-cofibrant-left-proper`: `Sheaf.CategoryTheory.AllCofibrantLeftProper`.
- `lem-coef-cartesian-mapping-simplex-presentation`: `Sheaf.CategoryTheory.CartesianMappingSimplexPresentation`.
- `lem-coef-infinity-cocartesian-arrow-projection`: `Sheaf.CategoryTheory.CocartesianArrowProjection`.
- `lem-coef-infinity-full-essential-image`: `Sheaf.CategoryTheory.InfinityFullEssentialImage`.
- `lem-coef-infinity-relative-joyal-factorization` currently has no Lean record, so it has no import yet. It is a proof prerequisite only, not a notion required to type this statement; its use remains in the full proof docstring.
- `lem-coef-joyal-quasicategory-characterizations`: `Sheaf.AlgebraicTopology.JoyalQuasicategoryCharacterizations`.

Edge cases checked before writing:

- For `N = 0` and `N = 1`, no inner i exists; the two inequalities express this
  directly and neither case needs a nonemptiness assumption on C.
- `N = 2`, `i = 1` gives exactly the first base case in HA. The base edge is 0 → 1.
- `N = 3`, `i = 2` gives the other base case, with edge 1 → 2. Both the first inner
  horn and the last inner horn `i = N - 1` are allowed for every applicable N.
- The empty simplicial set is allowed as C. Its lift condition is vacuous, and the
  canonical projection is the identity up to the unique isomorphism of empty sets.
- An empty preceding fiber is allowed. If it is inhabited the lift condition
  supplies the target object; we do not assume that any other fiber is inhabited.
- No lift data over other edges and no colimits in C are introduced. In particular
  the condition is weaker than assuming a cocartesian fibration over the simplex.
- `u` is arbitrary, and the testing universe `max u v` ranges over every
  enlargement, exactly matching the Joyal dependency; no universes are equated.

Searches for an existing statement (all repeated for this delivery):

- `msearch.py grep`: `cocartesian.*horn|coCartesian.*horn|horn.*categorical.*equiv`. Result: 0 hits; no matches.
- `msearch.py loogle`: `SSet.horn, SSet.InnerFibration`. Result: 0 hits; no matches.
- `msearch.py leanfinder`: `The inverse image of an inner horn under an inner fibration is a categorical equivalence when edges over the preceding edge have cocartesian lifts`. Result: 8 hits; SSet.modelCategoryQuillen.instHasLiftingPropertyιHornHAddNatOfNatOfFibration, SSet.Quasicategory.hornFilling, SSet.Quasicategory.hornFilling', CategoryTheory.Nerve.quasicategory, SSet.quasicategory_of_filler, SSet.Truncated.liftOfStrictSegal.hσ'₀, SSet.modelCategoryQuillen.J, SSet.KanComplex.hornFilling.
- `msearch.py leansearch`: `Pullback of an inner horn is a categorical equivalence under cocartesian edge lift hypotheses`. Result: 8 hits; CategoryTheory.IsPullback.lift, CategoryTheory.Functor.IsCocartesian.toIsHomLift, CategoryTheory.IsPullback.hasLiftingProperty, CategoryTheory.Functor.IsCocartesian.map.congr_simp, CategoryTheory.Limits.pullback.lift.congr_simp, CategoryTheory.Functor.IsStronglyCocartesian.toIsHomLift, CategoryTheory.Functor.IsCocartesian.map_isHomLift, CategoryTheory.Limits.pullback.lift'.

The LeanFinder hits fill horns into quasicategories or give Kan lifting properties;
none asserts this cocartesian pullback comparison. The LeanSearch hits concern
ordinary fibered categories and generic pullback maps, not simplicial cocartesian
edges. Loogle and the Mathlib grep return no match.

Source grep was also run with
`cocartesian.*horn|coCartesian.*horn|horn.*categorical.*equiv|cocartesian_inner_horn`
in `WeilConjectures/` and `lean/Sheaf/`. There are no upstream matches. Side-project
matches occur in descriptions of other notions, not an existing theorem with
these hypotheses: `CartesianBaseEquivalenceInvariance` discusses a horn assertion
inside its proof, but its declared theorem assumes a full cartesian fibration;
`RelativeExponentialRestriction` states an inner-fibration property of a relative
exponential. Their relevant text and declarations were inspected. A further grep
for `CocartesianInnerHorn|cocartesian_inner_horn|inner_horn_comparison|the project server`
in those sources and `dag/lean_names_upstream.json` found no existing declaration.
`grep -rn` for this node's exact id in upstream `WeilConjectures/` also had no hits.
There is no repair note for this item.

Validation: the delivered module was compiled with the prescribed `scompile.py`
wrapper, both as a sandbox file and at its library module path. Both passed
without errors or warnings (1.3 s and 1.4 s respectively). The final required
`deliver2.py --no-push` result is recorded below after it runs.

No `STATEMENT-DISPUTED` issue was found.

Dry run result: `deliver2.py Q97 lem-coef-infinity-cocartesian-inner-horn-comparison --no-push` printed `OK (dry run)` for commit `17f04c21f4`: compiles and passes preflight except for the independent second reading, which the second reader must write. Nothing was pushed.

## Second reading by Q97

I read the item node, Higher Algebra Lemma the project server (pp. 307--309), the three
statement dependencies, the declaration, and both citing nodes independently.
The node introduces the following data and clauses, and each has the indicated
Lean rendering.

1. Small simplicial sets, an integer (N), and an inner index (0<i<N) are
   rendered by `C : SSet.{u}`, `N : ℕ`, `i : Fin (N + 1)`, `hi : 0 < i`, and
   `hiN : i < Fin.last N`. The latter two inequalities are exactly the natural
   number inequalities in the node.
2. The quasicategory and map to the standard simplex are rendered by
   `[Quasicategory C]` and `q : C ⟶ (Δ[N] : SSet.{u})`, with
   `[InnerFibration q]`. The source calls this a map of infinity categories;
   maps from a quasicategory to a standard simplex are inner fibrations by the
   unique inner fillers in the nerve of the ordinal, and the node explicitly
   includes this interface.
3. For every object in the ((i-1))-fiber, the lift hypothesis is the `hlift`
   binder on `x : C _⦋0⦌` and the equation
   `stdSimplex.obj₀Equiv (q.app (op ⦋0⦌) x) = ⟨i.val - 1, by omega⟩`.
4. The required edge and endpoint are the existential `y` and `e`, with
   `C.δ 1 e = x` (source), `C.δ 0 e = y` (target), and the displayed equation
   placing `y` in the (i)-fiber.
5. The edge lies over (i-1\to i) through
   `SSet.yonedaEquiv.symm e ≫ q = SSet.stdSimplex.map
   (SimplexCategory.mkOfSucc ⟨i.val - 1, by omega⟩)`, and is cocartesian through
   `IsCocartesianEdge q (SSet.yonedaEquiv.symm e)`. This is the exact outer-horn
   definition from `Sheaf.CategoryTheory.InfinityFibrations` reexported by the
   recorded dependency.
6. The comparison map is the canonical `pullback.fst q (horn N i).ι`, whose
   source is the pullback of the horn and whose target is `C`; no arbitrary map
   is introduced.
7. Its categorical equivalence clause is the universal Joyal test
   `∀ (D : SSet.{max u v}), D.Quasicategory → ...IsEquivalence`, exactly the
   weak-equivalence conjunct in `SSet.exists_joyal_model_structure`, and its
   second conclusion is `Mono (pullback.fst q (horn N i).ι)`.
8. The final sentence of the node excludes cocartesian lifts over other edges
   and colimit assumptions; no such binders or instances occur in the Lean.

The signature is verbatim in the node's `lean.statement` field. I found no
mismatch and made no code or node change. The dependency declarations were
checked directly: `coneCategory` and the standard simplex/horn conventions are
from `Sheaf.CategoryTheory.EnhancedDiagramsCones`; `IsCocartesianEdge` is the
outer-horn lifting predicate from `Sheaf.CategoryTheory.InfinityFibrations`; and
the enlarged-universe equivalence test is from
`Sheaf.AlgebraicTopology.JoyalModelStructure`.

Edge cases are covered. If (N=0) or (N=1), the two strict inequalities give
no index (i), as in the source. (N=2,i=1) and (N=3,i=2) are both admitted,
including the last inner horn. The empty simplicial set and empty preceding
fiber make `hlift` vacuous; no nonemptiness is imposed. The zero-dimensional
fiber and all characteristic-like index cases are unrestricted. The universe
`u` is arbitrary, while `D : SSet.{max u v}` ranges over every enlargement;
there is no equality restriction on `u` and `v`.

My duplicate searches found no declaration in Mathlib, `WeilConjectures`, or
`lean/Sheaf`: exact-name and concept greps returned no match. The independent
`msearch.py` grep query for inner-horn/cocartesian comparison returned zero
hits. LeanFinder returned only generic quasicategory horn fillers and horn
colimit maps; these do not state this comparison. The source text was checked
against the local HA extract, including the source's descending-filtration
wording and its map-of-infinity-categories hypothesis.

The two citing nodes are `lem-coef-operadic-correspondence-kan-filling` and
`lem-coef-symmetric-operadic-left-horn-filling`; their uses remain valid because
both invoke precisely the canonical horn-pullback equivalence under the same
single preceding-edge cocartesian-lift condition. The relative Joyal
factorization node is used only in this item's proof plan, not as a statement
citer. Compilation with the required `scompile.py` wrapper succeeded for the
sandbox and library copies with no errors or warnings beyond the permitted
`sorry` declaration warning.
