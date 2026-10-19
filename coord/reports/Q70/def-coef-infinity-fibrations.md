## Worker report

`Sheaf.CategoryTheory.InfinityFibrations` states the definition node
`def-coef-infinity-fibrations`. Every definition has real data. There are no
postponed theorems, axioms, new DAG nodes, dependency replacements, or statement
corrections. The node copy changes only `lean`.

Clause-by-clause correspondence:

- Simplicial sets and maps are Mathlib `SSet.{u}` and its natural transformations.
  Standard simplices, horns and quasicategories are the primitives imported by
  the recorded dependency `Sheaf.CategoryTheory.EnhancedDiagramsCones`.
- The right lifting property is Mathlib `CategoryTheory.HasLiftingProperty i p`,
  used directly. Its field quantifies every commutative square `CommSq t i p v`
  and asserts that it has a lift. Thus it imposes both required filler equations,
  with no uniqueness requirement. It applies to the node's inclusions without
  imposing an unnecessary monomorphism hypothesis on the general Mathlib notion.
- Inner fibrations are the existing `SSet.InnerFibration p`. The underlying
  `innerHornInclusions` quantifies `Fin (n + 3)` at dimension `n + 2`, with
  `0 < i` and `i < Fin.last (n + 2)`: precisely all dimensions at least two
  and all strictly inner indices. This existing notion is not redefined.
- `leftFibration p` requires `HasLiftingProperty (horn n i).ι p` for each
  `1 ≤ n` and `i < Fin.last n`. The type `Fin (n + 1)` supplies `0 ≤ i`.
- `rightFibration p` requires the same lifting property for each `1 ≤ n`
  and `0 < i`. The type `Fin (n + 1)` supplies `i ≤ n`.
- `IsCocartesianEdge p e` quantifies `n ≥ 2`, a horn map `t`, base simplex
  `v`, and edge inclusion `a`. The square equation is
  `t ≫ p = (horn n 0).ι ≫ v`. The equation on `a` identifies the ordered
  initial edge using `SimplexCategory.mkOfSucc` at index zero, and `a ≫ t = e`
  is the prescribed restriction. The conclusion supplies `w` with both
  `(horn n 0).ι ≫ w = t` and `w ≫ p = v`.
- `IsCartesianEdge p e` has the same clauses for `horn n (Fin.last n)`;
  `mkOfSucc` at index `n - 1` selects exactly the ordered final edge.
  These horn conditions make sense for any simplicial map, and on an inner
  fibration are exactly the edge notions specified by the node. No claim for
  other maps is needed. Both fibration definitions explicitly require inner
  fibrations, so their edge tests have the prescribed context.
- `cocartesianFibration p` takes `[Quasicategory E] [Quasicategory B]` and
  conjoins `InnerFibration p` with the outgoing lift condition. For every
  source vertex `x`, endpoint `b` and base edge `α`, the two face equations
  say that `α` runs from `p(x)` to `b`. A lifted simplex `e` has source `x`,
  has image exactly `α`, and its Yoneda map is `IsCocartesianEdge`.
- `cartesianFibration p` takes the same quasicategory hypotheses and retains
  `InnerFibration p`. The base edge has source `b` and target `p(y)`; its
  lifted edge has target `y`, image exactly `α`, and is `IsCartesianEdge`.
  For a one-simplex, `δ 1` selects its source and `δ 0` its target.
- `fiber p b` is `pullback (SSet.const (X := Δ[0]) b) p`. The constant point
  map represents the singleton at the fixed vertex, including its degenerate
  simplices. Presheaf pullbacks are degreewise pullbacks. The factor order
  is `{b} ×_B E`, canonically the node's `E ×_B {b}` and consistent with the
  already recorded strict-fiber convention in `RightFibrationFibers`.
- `preservesCocartesianEdges` and `preservesCartesianEdges` take the common
  base `B`, maps `p`, `q`, a simplicial map `h`, and `h ≫ q = p`. They require
  the respective edge predicate of `e ≫ h` for every edge `e` with that
  predicate in the source. The commuting equation binds the over-base map;
  it is not an unconstrained map in place of a canonical construction.

Dependencies read and used:

- `def-weil-pbc-simplicial-set` is a Mathlib leaf. Its recorded matches are
  `SSet` (`Mathlib.AlgebraicTopology.SimplicialSet.Basic`), `SSet.degenerate`
  and `SSet.nonDegenerate` (`...Degenerate`), `SSet.Subcomplex`
  (`...Subcomplex`), and `SSet.Finite` (`...Finite`). Their signatures and
  docstrings were read. Only the simplicial set/map and subcomplex clauses
  are needed here; finiteness is not assumed.
- `def-cbc-enhanced-diagrams-cones` records
  `Sheaf.CategoryTheory.EnhancedDiagramsCones` and
  `SSet.Enhanced.coneCategory`. The full module and signature were read.
  Its imported `SSet.stdSimplex`, `SSet.horn`, and `SSet.Quasicategory`
  supply the precise notions this node uses; the cone construction itself
  is not required. Their Mathlib signatures and docstrings were also read.
- Additional existing primitives are `CategoryTheory.HasLiftingProperty`
  (`Mathlib.CategoryTheory.LiftingProperties.Basic`), `SSet.InnerFibration`
  (`Mathlib.AlgebraicTopology.Quasicategory.InnerFibration`), and
  `SimplexCategory.mkOfSucc` (`Mathlib.AlgebraicTopology.SimplexCategory.Basic`).
  No private copies or aliases of these notions remain.

Source check: opened Lurie's HTT PDF at
https://www.math.ias.edu/~lurie/papers/HTT.pdf . Definition the project server gives
exactly the three horn ranges. Remark the project server gives the final outer-horn
criterion, including `n ≥ 2` and the final ordered edge; its opposite is the
initial criterion. Definition the project server gives prescribed-target cartesian
lifting and defines cocartesian fibrations by passage to opposites.

Edge cases checked before the revision:

- No dimension-zero horn or nonemptiness condition is imposed. Dimension-one
  left/right tests are included, respectively indices zero and one.
- Dimension two is included for both outer-edge tests. The initial edge
  is the face opposite vertex two in `horn 2 0`; the final edge is the face
  opposite vertex zero in `horn 2 2`. In higher dimensions each ordered
  edge likewise lies in one of the retained faces. Consequently the map
  `a` exists and is unique since the horn inclusion is monic; the restriction
  condition cannot be vacuous because an edge is absent from the horn.
- Both filler equations are retained, so filling in the total space alone
  does not suffice. Degenerate edges and arbitrary specified endpoints are
  included. Empty total spaces and empty fibers are permitted; lift clauses
  quantify vertices in the total space, without inventing one.
- `u` is arbitrary and explicitly bound. All sets live in the common fixed
  simplicial-set universe, as in the dependency. No finite, inhabited, Kan,
  or quasicategory hypotheses are imposed on left/right fibrations or fibers.

Searches rerun using `msearch.py Q70 def-coef-infinity-fibrations`:

- LeanSearch: `Left and right fibrations of simplicial sets and cartesian
  cocartesian edge horn lifting` returned eight model-category/Kan hits.
  Reading `SSet.modelCategoryQuillen.J` and its fibration definition shows
  that they test all positive horns, not the specified left/right ranges.
- LeanFinder: `Left right cartesian cocartesian fibrations of simplicial sets
  with outer horn edge lifting` returned eight horn-filling/Kan candidates;
  none defines the remaining relative edge or fibration notions.
- Loogle: `"InnerFibration", "HasLiftingProperty"` returned no hits;
  the focused query `"InnerFibration"` returned twelve hits, including the
  exact existing `SSet.InnerFibration`, used directly.
- Mathlib grep: `LeftFibration|RightFibration|CocartesianFibration|CartesianEdge|
  initialEdge|finalEdge` in `AlgebraicTopology` returned no hits. Direct
  reading found `mkOfSucc`, which replaces the earlier custom edge helpers.
- `rg -n` for the node id and the left/right/cartesian/cocartesian names in
  `WeilConjectures` and `lean/Sheaf` found no definition of this item's
  remaining notions. Existing `RightFibrationFibers` and related consumer
  modules state their horn conditions directly. Mathlib's ordinary-category
  `Functor.IsCocartesian` was read: its unique Hom-set factorization is not
  this arbitrary simplicial-map notion.

Earlier-attempt repairs: removed the redundant `HasHornLift` alias and custom
`initialEdge`/`finalEdge` constructions; supplied source-bearing docstrings for
every remaining definition; expressed edge restriction through its explicit
factorization inside the horn; refreshed the node copy from the shared node and
recorded the actual UTC date and exact signature. The old sandbox's purported
second-reading text was not retained: the independent reader follows this worker.

Validation: `scompile.py Q70 def-coef-infinity-fibrations` compiled this file
as both a sandbox module and its actual library module, with no errors or
warnings. No `sorry` occurs. There is no `STATEMENT-DISPUTED` issue.

## Second reading by Q70

Independent reader: I did not author this module. I read the sandbox node and
Lean together, the two statement-dependency records and their declarations,
coord/brief-stage2.md, delivery-errors H, and the worker report. There is no
repair note for this item. This delivery has no new nodes, dependency modules,
or statement_change to audit. The only node field changed from the shared base
is lean. I found no mathematical mismatch and left the Lean unchanged.

My list of the node's objects, hypotheses, and clauses, with their rendering:

1. Objects are simplicial sets E and B and a natural transformation p. Each
   definition binds `{E B : SSet.{u}} (p : E ⟶ B)`; the preservation definitions
   additionally bind F. Mathlib Basic.lean defines SSet as the Type-valued
   contravariant functor category. The standard simplex is uliftYoneda and the
   horn is the subfunctor whose image omits a vertex other than i. These are the
   exact primitives imported by EnhancedDiagramsCones. Verdict: exact; no
   category, ring, or finiteness hypothesis has been substituted.
2. Right lifting for K included in L means every commuting square admits w with
   both equations. Existing `CategoryTheory.HasLiftingProperty i p` quantifies
   every `CommSq f i p g`; CommSq.HasLift contains Nonempty LiftStruct, with
   `i ≫ l = f` and `l ≫ p = g`. Existence imposes no uniqueness. Verdict: exact
   on the inclusions in the node, using the existing general definition.
3. Inner fibrations test dimensions at least two and 0 < i < n. The module uses
   existing `SSet.InnerFibration p`, whose mem field is innerHornInclusions.rlp.
   The generators have dimension n+2 and i : Fin (n+3), with strict inequalities
   at both ends. This includes all and only the required inner horns. Verdict:
   exact, without a second definition of inner fibration.
4. Left fibrations test n >= 1 and 0 <= i < n. `leftFibration` quantifies n,
   `i : Fin (n+1)`, `1 ≤ n`, and `i < Fin.last n`, then the lifting property.
   Fin supplies the lower bound. Verdict: exact, including the initial one-horn.
5. Right fibrations test n >= 1 and 0 < i <= n. `rightFibration` uses the same
   binders with `0 < i`; Fin supplies the upper bound. Verdict: exact, including
   the final one-horn.
6. For an inner fibration, a cocartesian edge e has every initial outer-horn
   filler with prescribed ordered edge {0,1}. `IsCocartesianEdge p e` quantifies
   n, `2 ≤ n`, t, v, and a, with the square equation, the equation identifying
   a inside the horn, and `a ≫ t = e`. `mkOfSucc` at zero sends vertices 0 and 1
   to 0 and 1. Its existential w obeys both filler equations. Verdict: exact.
   The predicate itself is available for any p; on the inner fibrations named
   by the node it is precisely the required condition, with no extra premise
   or omitted horn test. This extension of the predicate's domain does not
   alter its value on the node's domain.
7. Cartesian edges use the final horn and ordered edge {n-1,n}.
   `IsCartesianEdge` replaces zero by Fin.last n and uses mkOfSucc at n-1.
   I read mkOfSucc's actual function: it sends zero to i.castSucc and one to
   i.succ, giving n-1 and n under `2 ≤ n`. The square, edge restriction, and
   both filler equations are retained. Verdict: exact, with the same domain
   observation as in item 6.
8. For quasicategories E,B, a cocartesian fibration is inner and lifts every
   base edge starting at p(x) to a cocartesian edge starting at prescribed x.
   `cocartesianFibration` binds `[Quasicategory E] [Quasicategory B]`, conjoins
   `InnerFibration p`, and quantifies x, b, alpha with the two base face
   equations. Its e has `E.δ 1 e = x`, image alpha, and the relative edge
   predicate via yonedaEquiv. Here δ 1 is source and δ 0 target. The remaining
   lifted endpoint maps to b by naturality and the base equation. Verdict:
   exact; the quasicategory assumptions are those explicitly in the node.
9. A cartesian fibration instead lifts b -> p(y) with prescribed target y.
   `cartesianFibration` has those same quasicategory and inner clauses, reverses
   the endpoint equations, requires `E.δ 0 e = y`, and uses IsCartesianEdge.
   Verdict: exact, for every vertex, every base edge, and every prescribed target.
10. The strict fiber at b is the degreewise pullback with the constant point.
    `fiber p b` is `pullback (SSet.const (X := Δ[0]) b) p`. I read const's app:
    it sends every simplex to the degeneracy of b in that degree. Δ[0] has one
    simplex in each degree, so this is exactly the simplices of E mapping to
    that degeneracy, with their restricted operators. Factor order is the
    canonical swapped presentation of E times_B {b}; this is also the exact
    presentation already used by rightFibrationFiberMap and
    rightFibration_fibers in RightFibrationFibers. Verdict: exact strict fiber,
    rather than the path-based Enhanced.homotopyFiber of the dependency.
11. A map h over the common base preserves each kind of edge iff every source
    edge of that kind maps to one of the same kind. Each preservation definition
    takes p,q,h and `h ≫ q = p`, then quantifies every e and tests e ≫ h with the
    corresponding relative predicate. Verdict: exact; no converse, essential
    surjectivity, or chosen lift is required.

Source reading: I opened the actual HTT PDF online at the node's URL, reading
Definition the project server (printed p.53), Definition the project server (p.115), Remark the project server
(p.116), the cocartesian dual convention preceding Proposition the project server (p.118),
and Definition the project server (p.121). The first passage is for arbitrary simplicial
sets. The edge criterion assumes inner fibrations and is exactly the final
outer-horn test for n >= 2. Reversing the order gives the initial test. HTT's
fibration definition is available more generally, and the node explicitly
specifies its application to quasicategories; the Lean uses that stated domain.
No Stacks tag defines this item's infinity-categorical notions. For the
simplicial-set dependency I also read Stacks simplicial.tex at
 definition-simplicial-object and definition-terminology-simplicial-sets. For the
other dependency I read Scholze's archived PDF, printed pp.13-15, Definitions
2.1-2.2, including the inner-horn characterization. No standing Noetherian,
nonempty, Kan, field, or characteristic assumption occurs in these passages.

Edge cases: n=0 contributes no left/right lifting tests, and n=1 contributes
exactly index zero for left and index one for right. Relative edge tests start
at n=2, where the distinguished initial edge is a retained face opposite
vertex 2 and the final edge is a retained face opposite vertex 0. For every
larger n the initial edge still omits vertex 2 and the final edge omits vertex
0; those are retained faces. Thus their maps a into the horns really exist,
and are unique because the inclusion is monic: the universal quantification
over a does not make the restriction test vacuous. Degenerate edges are
included. Empty E, empty B when a map exists, and empty fibers are allowed;
none of the definitions asserts an inhabitant of E. Identity maps satisfy the
filler tests by taking the base filler itself. For a map to a point the outer
edge criteria have the expected equivalence-edge meaning. There is no indexed
product, scheme, ring characteristic, or integer coefficient parameter here.
The explicitly bound universe u is arbitrary, exactly as for the dependency's
fixed simplicial-set universe; differently sized inputs can inhabit their
common larger universe. No unbound variable, extra size equality, finiteness,
or inhabited instance appears.

Independent searches, using words different from the author's search:

- LeanFinder via msearch.py: `A simplicial map with lifting against nonfinal
  horns, and relative coCartesian arrows detected by prescribed first edges`.
  Eight hits: all-horn J, Quasicategory, boundary I, strict Segal constructions,
  and ordinary horn filling. Reading J in CategoryWithFibrations.lean confirms
  it tests all positive horns, hence does not supply left/right fibrations.
- Loogle via msearch.py: `"HasLiftingProperty", "horn"`. One hit, the Kan
  fibration all-horn lifting instance, again not these notions.
- LeanSearch via msearch.py: `Relative cartesian arrows in simplicial sets and
  lifting of edges with a fixed source or target`. Eight hits, including fixed
  top/bottom lifting predicates, ordinary Functor.IsCartesian/IsStronglyCocartesian,
  and RelativeMorphism. I read the ordinary cartesian/cocartesian classes:
  their unique factorization in ordinary Hom sets is not the relative
  simplicial edge condition. The general square lifting notion is already used.
- rg, case-insensitive, for `cartesian.?edge|co.?cartesian.?fibration|
  left.?fibration|right.?fibration|strict.?fiber` on all named Mathlib
  AlgebraicTopology sources, all upstream WeilConjectures, and all project
  lean/Sheaf. There is no existing definition of the remaining predicates.
  The project hits are consumer theorems with explicit horn hypotheses and
  strict pullback expressions. RightFibrationFibers supplies a fiber map,
  not a competing fiber definition. The existing InnerFibration was opened
  and used directly. These searches support retaining this module; no exact
  existing declaration covers the item as a whole.

H5/H6/H8/H9 check: every definition has real data; no theorem, axiom, or sorry
is introduced. The omega terms discharge finite-index bounds inside actual
edge inclusions, not postponed mathematical claims. Every declaration has a
source/blueprint docstring. This definition node has empty proof and
proof_deps, so no proof-plan docstring or proof-only import is missing. The
namespace, topic path, public dependency imports, 100-character Lean line
limit, explicit universe, and autoImplicit=false conform. All nine definitions
are listed in lean.declarations, and lean.statement was checked verbatim
against the main signature through its return type.

Changes from this second reading: appended this independent audit only. No
mathematical or interface repair was needed; the worker's correct Lean and
node binding are retained. Prescribed scompile.py compiled both the sandbox
and actual library module successfully with no errors or warnings. Delivery
preflight and push follow this audit.
