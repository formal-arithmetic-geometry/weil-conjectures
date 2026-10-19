## Worker report

Item: `lem-coef-cartesian-core-right-fibration`. The delivery supplies
`Sheaf.CategoryTheory.CartesianCoreRightFibration`, defining the actual Cartesian-edge
subcomplex `SSet.Enhanced.cartesianCore` and stating
`SSet.Enhanced.cartesian_core_right_fibration`. The only postponed proof is this theorem,
whose proof is `sorry`; its docstring includes all four proof steps of the node.
The subcomplex has explicit degreewise data and an operator-closure proof, with no
postponed data or arbitrary choices. Both declarations are recorded in `lean.declarations`.
No node statement, dependency, or proof field is changed.

Source checked: Higher Topos Theory, Corollary the project server (printed page 122),
Proposition the project server (printed page 116 in the online edition), Corollary the project server,
and Remark the project server. The IAS URL failed in the web reader; the author's Harvard copy,
https://people.math.harvard.edu/~lurie/papers/HTT.pdf, was readable. The corollary
states the Cartesian-edge subcomplex and right-fibration assertion. The fiber and
transport clauses use the explicit expanded argument in this DAG node. The node's
source pagination for Proposition the project server differs from that online edition; its numbered
statement is the relevant equivalence/Cartesian-edge criterion. This is a bibliographic
observation, not a mathematical statement correction.

Hypothesis and clause correspondence:

- The fixed containing universe is the explicit `universe u`; both `E` and `B` are
  `SSet.{u}`. There are no size equalities beyond that convention and no ordinary-category
  or nerve restriction. `[Quasicategory E] [Quasicategory B]` renders the two
  quasicategory assumptions, `(p : E ⟶ B)` is the simplicial map, and
  `(hp : cartesianFibration p)` is exactly the Cartesian-fibration hypothesis.
- `cartesianCore p` has degree-`n` membership
  `∀ a : ⦋1⦌ ⟶ n.unop, pCartesianEdge p (SSet.yonedaEquiv.symm (E.map a.op s))`.
  Thus it retains precisely the simplices with all edges Cartesian. Constant maps
  test degenerate edges too; for a Cartesian fibration these are Cartesian. Its operator
  law tests the composite `a ≫ f.unop`, so the full simplicial subset is constructed.
- `rightFibration ((cartesianCore p).ι ≫ p)` says the restricted projection is a right
  fibration, using exactly the existing positive-index horn predicate.
- For every vertex `b : B _⦋0⦌`,
  `(cartesianCore p).preimage (pullback.snd (SSet.const (X := Δ[0]) b) p) =
  core (fiber p b)` gives the identification as an equality of subcomplexes of the original
  strict fiber. The left side is the fiber of the Cartesian-edge subset, viewed inside
  the original fiber: degreewise it selects pairs `(point,s)` with `p(s)=b` and `s`
  in the Cartesian core. This is canonically the degreewise fiber of the restricted
  projection. Equality is stronger data than an unspecified equivalence and represents
  the node's equality of simplicial subsets without choosing an isomorphism.
- Transport is quantified over every `b c : B _⦋0⦌` and `f : B _⦋1⦌`, with
  `B.δ 1 f = b` and `B.δ 0 f = c` fixing source and target. A given Cartesian transport
  consists of `T : fiber p c ⟶ fiber p b` and its entire coherent cylinder
  `h : Δ[1] ⊗ fiber p c ⟶ E`. The two `lift (SSet.const ... 0/1) (𝟙 _) ≫ h`
  equations fix its time-zero map to the included `T` and its time-one map to the
  original fiber inclusion. `h ≫ p = fst ... ≫ SSet.yonedaEquiv.symm f` fixes the
  whole base cylinder, not merely its vertices. The quantified `pCartesianEdge`
  condition on `lift (𝟙 Δ[1]) (SSet.const ... y) ≫ h` says that every vertical lift
  has the required Cartesian property. These are exactly the transport data specified
  in proof step 3; they do not impose a new assumption on `p`.
- The conclusion supplies `g : Δ[1] ⊗ (core (fiber p c)).toSSet ⟶
  (cartesianCore p).toSSet` and
  `Tcore : (core (fiber p c)).toSSet ⟶ (core (fiber p b)).toSSet`.
  The first equation, `g ≫ (cartesianCore p).ι = (Δ[1] ◁ (core (fiber p c)).ι) ≫ h`,
  specifies `g` as the actual restriction of the supplied cylinder. Hence it inherits
  the fixed base edge and time-one fiber inclusion, so is a right-fibration transport
  cylinder under the fiber-core identification. The second equation,
  `Tcore ≫ (core (fiber p b)).ι = (core (fiber p c)).ι ≫ T`, specifies its initial
  map as exactly the restriction of Cartesian transport to cores. These equations
  also imply equality of the time-zero maps in the Cartesian core: after inclusion
  in `E` they are the same restriction of `h`, and those inclusions are monic.
  Both equations are natural-transformation equalities in all degrees. The statement
  retains every choice of coherent transport cylinder, without selecting one from
  a mere existence theorem or replacing it by an arbitrary map.

Dependency declarations read and used:

- `def-cbc-enhanced-diagrams-cones`, module
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.core`,
  `SSet.Enhanced.IsEquivalenceEdge`, and the exposed Mathlib simplicial, quasicategory,
  product and simplex conventions. The existing core definition tests every ordinal
  map from `[1]` and has exactly the same operator-closure form used here.
- `def-coef-infinity-fibrations`, recorded module
  `Sheaf.CategoryTheory.InfinityFibrationsCartesianRepair`:
  `SSet.Enhanced.pCartesianEdge`. Through its public imports of
  `InfinityFibrationsOverSimplicialBases` and `InfinityFibrations`, this also supplies
  the existing `cartesianFibration`, `rightFibration`, `fiber`, `IsCartesianEdge` and
  `IsCocartesianEdge`. I read those original definitions, including the final-horn
  criterion and prescribed-target lift clause. The recorded interface is usable;
  it needs no repair.
- Nonpublic proof import `Sheaf.AlgebraicTopology.MarkedOppositeRelativeCalculus`:
  `SSet.Marked.Over.marked_opposite_relative_calculus` and its
  `OppositeRelativeCalculus.edge_reversal` and fiber comparison fields.
- Nonpublic proof import `Sheaf.CategoryTheory.InfinityCocartesianCompositionInitiality`:
  `SSet.Enhanced.cocartesian_composition_initiality` (composition, cancellation,
  degenerate edges). Its full theorem signature and proof docstring were read.
- Nonpublic proof import `Sheaf.CategoryTheory.CocartesianLocalGlobal`:
  `SSet.Enhanced.cocartesian_local_global`, especially its strict-fiber equivalence
  clause; its full theorem signature and proof docstring were read.
- Nonpublic proof import `Sheaf.CategoryTheory.RightFibrationFibers`:
  `SSet.Enhanced.rightFibration_fibers`, for the Kan-fiber consistency check in the
  node's proof. Its full theorem signature and proof docstring were read.
- Mathlib `SSet.Subcomplex.preimage` supplies the fiber subcomplex, while
  `CategoryTheory.CartesianMonoidalCategory.lift` and `fst` supply the actual endpoint,
  vertical-edge, and projection maps in the product cylinder.

Edge cases checked before writing:

- Empty total space and empty fibers: subcomplex membership and the fiber equality
  are empty degreewise. Empty cylinder domains have their unique maps; the theorem
  never assumes a fiber is inhabited.
- `p = 𝟙 B`: every edge is Cartesian, so the Cartesian core is all of `B`, with
  singleton vertex fibers. The right-fibration and transport clauses specialize correctly.
- Base a point: Cartesian edges are precisely equivalences of `E`, so the Cartesian
  core is the ordinary core; the projection is a right fibration of spaces.
- A nerve of an ordinary Grothendieck fibration: the fiber condition retains exactly
  fiber isomorphisms, and every Cartesian transport restricts to these isomorphisms.
- Dimension zero and degenerate edges are included by the constant ordinal test maps.
  Dimension-one horns require prescribed targets; inner and final two-horns use
  composition and cancellation respectively. No dimension-zero lifting condition
  accidentally asserts nonemptiness.

Searches (all fresh for this item):

- `msearch.py ... leanfinder "The Cartesian-edge simplicial subset of a Cartesian
  fibration is a right fibration with fiber the core"`: eight hits, including
  `SSet.modelCategoryQuillen.instCategoryWithFibrations`, Quillen horn-fibration facts,
  and ordinary `CategoryTheory.Functor.IsFibered.of_exists_isStronglyCartesian`.
  None states a quasicategorical Cartesian-core assertion or its transport clause.
- `msearch.py ... loogle "SSet.Quasicategory"`: twelve hits, including
  `SSet.Quasicategory`, inner-horn lifting lemmas, and two-truncated composition facts;
  no Cartesian core or right-fibration theorem.
- `msearch.py ... grep "cartesian.?core|right.?fibration" AlgebraicTopology`:
  zero hits in pinned Mathlib.
- `msearch.py ... leansearch "Cartesian core of Cartesian fibration is right fibration"`:
  eight ordinary `Functor.IsFibered`/`IsCartesian` hits. Their signatures quantify over
  ordinary categories and functors, so none supplies the quasicategorical statement.
- `rg -n` on `lean/Sheaf` and upstream `WeilConjectures` for
  `cartesianCore|cartesian.core|CartesianTransport|Right.*Transport|transport.*[Dd]atum|cartesian_core`:
  no existing Cartesian-core construction or exact theorem. Nearby Cartesian-transport
  predicates in `InfinityGrothendieckLimitsColimits` and `RelativeConePresheafFibers`
  encode unrelated enclosing results; this module uses only the concrete cylinder
  hypotheses specified by its own node, without redefining either predicate.
- `grep -rn "lem-coef-cartesian-core-right-fibration"` upstream `WeilConjectures`:
  no matches. `rg` for `cartesianCore|cartesian_core_right_fibration` in
  `dag/lean_names_upstream.json`, all pinned Mathlib, upstream source and `lean/Sheaf`:
  no matches. `tools/blueprint_refs.py search "Cartesian core"`: zero blueprint nodes.

Validation: `scompile.py Q05 lem-coef-cartesian-core-right-fibration` compiled the
module cleanly, including its private proof imports, with the prescribed 60-second
per-file limit (the delivered module took 2.3 seconds). No compiler warning or error.
All universes and variables are explicit, with `autoImplicit false`. All source lines
are at most 100 characters. There are no new DAG nodes, dependency repairs, statement
corrections, or statement disputes. The auxiliary subcomplex is the construction of
this lemma itself and belongs to this node under the authorized helper-declaration rule.

## Second reading by Q05

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
