## Worker report

The module `Sheaf.CategoryTheory.SmallCocartesianModel` states
`SSet.Enhanced.small_cocartesian_model`, with `sorry`, and constructs the canonical
restriction `SSet.Enhanced.smallCocartesianFiberMap` by `pullback.map`. The helper
contains real data and no postponed theorem. The original node statement and all
dependencies are unchanged; its `lean` record is added. The repair packet also
contains the minimal transitive dependency compilation repair described below.

Clause-by-clause correspondence:

- The small universe is `u`; the containing universe is `max (u + 1) v`.
  `S E : SSet.{max (u + 1) v}` puts both presentations in a common ambient
  universe, and covers any larger universe containing the small one.
- `S` is a small quasicategory: `[Quasicategory S]` and
  `hS : Presentability.IsSmall.{u, max (u + 1) v} S`. This is the dependency's
  actual simplicial-set smallness predicate, counting all nondegenerate simplices,
  not its essential-smallness predicate. It is independent of which universe
  houses the presentation. A small model can equivalently be represented by a
  degreewise small simplicial set in this ambient universe, without making all
  the over-base maps change universes. No universe equality is imposed.
- The given total space fits in the containing universe and is a quasicategory:
  the binder `E` and `[Quasicategory E]`. Quasicategorical total and base are part
  of the node's notion of cocartesian fibration, not an additional restriction.
- `p : E ⟶ S` and `hp : cocartesianFibrationOver p` give the inner fibration
  and cocartesian lifts from every prescribed source.
- Each fiber is equivalent to a small quasicategory:
  `hfib : ∀ s : S _⦋0⦌, Presentability.IsEssentiallySmall.{u, ...} (fiber p s)`.
  That recorded predicate existentially supplies an actual `u`-universe
  quasicategory and an equivalence after common-universe lifting.
- The output `E₀` is an actually small quasicategory:
  `Presentability.IsSmall.{u, ...} E₀ ∧ Quasicategory E₀`.
  This does not replace actual smallness by equivalence to something small.
- The output `p₀ : E₀ ⟶ S` satisfies `cocartesianFibrationOver p₀`.
- The output functor is the simplicial map `F : E₀ ⟶ E`.
  The witness `h : F ≫ p = p₀` is strict equality over the original base.
- `IsFunctorEquivalence F` says that F has a quasi-inverse and both coherent
  inverse natural equivalences, exactly as defined by the enhanced-diagram node.
- Every fiber comparison is the induced one:
  `∀ s, IsFunctorEquivalence (smallCocartesianFiberMap p₀ p F h s)`.
  The helper uses the recorded `fiber` objects on both sides and the identity
  on the point coordinate, F on the total-space coordinate and the identity on
  the base. Its commutative square is forced by h; no arbitrary fiber map occurs.
- `preservesCocartesianEdges p₀ p F h` is the recorded preservation predicate.
- `∀ e : Δ[1] ⟶ E₀, IsCocartesianEdge p (e ≫ F) → IsCocartesianEdge p₀ e`
  is reflection for every edge.
- No nonemptiness hypothesis occurs for the base, total space or any fiber.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.PresentableInfinityCategory`:
  `SSet.Presentability.IsSmall`, `SSet.Presentability.IsEssentiallySmall`.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.IsFunctorEquivalence` (and its underlying
  `AreNaturallyEquivalent`, with inverse equivalence-edge witnesses).
- `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases`:
  `SSet.Enhanced.cocartesianFibrationOver`; this publicly reexports
  `Sheaf.CategoryTheory.InfinityFibrations`, whose `fiber`,
  `IsCocartesianEdge` and `preservesCocartesianEdges` are used directly.
- Mathlib's `SSet.Quasicategory`, simplicial maps, standard simplex and
  `CategoryTheory.Limits.pullback.map` give the remaining primitives.

All currently recorded proof-dependency modules are imported privately (the
statement-dependency EnhancedDiagramsCones remains public): CocartesianStraightening,
InfinityFullEssentialImage, MarkedRelativeCartesianModel,
InfinityCocartesianMappingCriterion, EnhancedFunctorConeCalculus and
KanHomotopyPullbackInvariance. The proof dependency
`lem-coef-cocartesian-straightening-universe-change` has no Lean record in the
base and therefore no module to import yet. It is used only in the proof plan,
not to formulate this statement. The complete five-step DAG proof is rendered
in the theorem docstring. No missing statement notion or interface repair is needed.

Edge cases checked before writing and again on rereading:

- An empty base forces E empty degreewise; E₀ can be empty. All fiber and
  edge clauses are universally quantified and introduce no point choice.
- Empty fibers are permitted by `IsEssentiallySmall` (the empty quasicategory
  is a permitted witness), and the induced comparison is still the strict
  fiber restriction. No surjectivity of vertices onto S is assumed.
- Empty total space over a nonempty base is allowed, since lifts are required
  only from existing source vertices. The conclusion allows the empty E₀.
- Over a point the statement specializes to replacing an essentially small
  quasicategory by an actually small model, with its genuine fiber map.
- Universe sizes are not collapsed: the input E need not have small simplex
  sets, and no local-smallness hypothesis is added. Actual smallness of S
  and E₀ is expressed separately from essential smallness of input fibers.

Searches for an existing theorem:

- `msearch.py ... leanfinder` with query "A cocartesian fibration over a small
  quasicategory with essentially small fibers admits an equivalent small
  cocartesian fibration over the same base": eight hits, on ordinary
  `Functor.IsCocartesian` and `CostructuredArrow.essentiallySmall`, not this theorem.
- `msearch.py ... loogle 'CategoryTheory.SmallModel'`: twelve hits; SmallModel
  and equivSmallModel are for ordinary categories, not simplicial cocartesian
  fibrations and coherent equivalences. Their full signatures/docstrings were read.
- `msearch.py ... grep 'cocartesian.*small|small.*cocartesian|essentially.*small.*fiber'`:
  zero Mathlib hits. The ordinary-category cocartesian-edge definition and
  Mathlib quasicategory definition were read to distinguish their meanings.
- The same concept regex with `rg` in upstream `WeilConjectures` gives no
  hits; `grep -rn 'lem-coef-small-cocartesian-model'` there gives none.
- `rg` in `lean/Sheaf` finds straightening, space-transport classification and
  citations in SmallMonoidalFullSubcategory, but no small-model theorem.
  None gives the asserted strict equivalence, all fiber equivalences and edge
  reflection for general cocartesian fibrations.
- Exact-name searches for `SmallCocartesianModel`, `small_cocartesian_model`
  and `smallCocartesianFiberMap` in the side library, upstream Lean and
  `dag/lean_names_upstream.json` give no matches.

Source read online: Lurie's HTT PDF, Theorem the project server and Section 3.3.2;
Remark the project server gives smallness of the universal pullback over a small base,
and Remark the project server (*') gives the essentially-small-fiber classification,
with Definition the project server specifying the cocartesian dual.
The hosted PDF places printed p. 211 at zero-based PDF page 228.
WANTED: archival HTT copy in literature (none found in the provided archive).
No statement dispute or correction is required.

Validation: the prescribed scompile.py invocation compiled both the sandbox
module and its library-path version cleanly, in 1.5 s and 1.8 s respectively.

## Second reading by Q48

I reopened the node and module for a separate self-review pass; the independent
mathematical review is assigned to the maintainer by this dispatch brief.
I checked every hypothesis and output clause against the list above. In particular,
`IsSmall` (not `IsEssentiallySmall`) is used for S and E₀; the fiber map is the
canonical pullback map; h is strict over S; and reflection has the direction
from cocartesianness of F(e) back to that of e. No empty-base or empty-fiber
case is excluded. All universes and variables are explicit, the only postponed
proof is the node's theorem, and the helper is an actual construction. No mismatch
was found and no node statement was changed.

## Dependency modules

`lem-coef-space-valued-straightening`, module
`Sheaf.CategoryTheory.SpaceValuedStraightening`, is a transitive dependency of
the item's mandatory proof imports. The returned immutable-head compile and the
first repair dry run both fail at its `Diagrams` abbreviation: it depends on the
noncomputable canonical `smallSpaces`. The dependency module is retained in full
with the sole source change `abbrev Diagrams` to `noncomputable abbrev Diagrams`.
This preserves its actual internal functor simplicial set, all universe levels,
all signatures, every hypothesis and every conclusion. No data, proof, import or
mathematical statement is changed. Its node changes only in `lean`, recording
this compilation repair and the exact multiline theorem signature. The module
was compared against current source obtained through `scompile.py --source`;
it matches the shared source apart from its final blank line. The retained item
module and statement remain unchanged.

## Returned-delivery repair

The return's sole defect is reproduced by the initial prescribed dry run. The
noncomputability annotation above repairs that exact compiler diagnostic rather
than dropping the required proof-dependency imports. Self-review confirms that
the retained item still has its strict over-base equality, actual smallness,
canonical fiber restriction, fiber equivalences, and preservation and reflection
of cocartesian edges, including empty cases. Independent review remains with
the maintainer.

Repair validation: the prescribed `scompile.py` compiled both delivered files,
including their sandbox and library-path forms, cleanly. The repaired dependency
compiled in 3.2–3.5 s and the item in 2.4 s. A fresh comparison with the shared
node files shows that both node copies differ only in `lean`; both recorded
theorem signatures match their modules verbatim, and all source lines are at
most 100 characters. The dependency's complete source differs by exactly the
one noncomputability annotation shown above.
