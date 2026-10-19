## Worker report

The module states the Kerodon outer-horn characterization of equivalence edges in a quasicategory. It defines `IsInitialHornEdge` and `IsFinalHornEdge` to render the canonical edges `[0,1]` and `[n-1,n]` by their endpoint values in the horn simplex, then states both extension implications and both converses for every `n ≥ 2`. The quasicategory hypothesis is `[SSet.Quasicategory Q]`; fillers are maps `Λ[n,i] ⟶ Q` extending as `σ₀ = Λ[n,i].ι ≫ σ`; equivalence is the dependency declaration `SSet.Enhanced.IsEquivalenceEdge`.

The statement dependency is `Sheaf.CategoryTheory.EnhancedDiagramsCones`, declaration `SSet.Enhanced.IsEquivalenceEdge`. The proof dependency import is `Sheaf.AlgebraicTopology.PushoutJoinSaturation`, declaration `SSet.Enhanced.pushout_join_weak_saturation`; the boundary-cell dependency is a Mathlib node and has no Lean import record.

Edge cases checked include `n = 2`, where the canonical endpoint predicates describe the two edges of the outer triangles, and the requirement `n ≥ 2`, which ensures the endpoint indices exist and the edge is genuinely extremal. The predicates quantify over all horn 1-simplices with the specified endpoint values; in a standard simplex monotonicity makes this the unique edge `[0,1]` or `[n-1,n]`.

Searches made: LeanFinder/LeanSearch/Loogle and Mathlib/project grep for outer-horn equivalence criteria, coslice left fibrations, and horn extension; no exact declaration was found. Mathlib provides only primitive `SSet.Quasicategory.hornFilling` for inner horns. The existing project declaration supplies equivalence edges but no outer-horn theorem.

## Earlier second reading (a previous round; superseded)

Read the node and module independently. The Lean has the quasicategory binder, both orientations, `n ≥ 2`, the forward extension clauses, and converses quantified over every dimension and every horn map. `IsInitialHornEdge` and `IsFinalHornEdge` match the node's extremal edges by endpoint values; no hypotheses or conclusion clauses were added or omitted. The proof is `sorry` as required for stage 2.

## Second reading by Q14

I independently opened the sandbox node, the module, the current dependency node records,
and the dependency declaration sources. The source is Kerodon, not Stacks: I read
https://kerodon.net/tag/019F, Theorem the project server, directly. Its standing hypothesis is that
C is an infinity-category (a quasicategory); it introduces an arbitrary edge u, with
n >= 2 in both lifting conditions. There is no nonemptiness, finiteness, or Kan hypothesis.
No statement_change or repair note exists for this item. No new definition nodes or
dependency modules are supplied by this delivery.

The statement inventory and clause-by-clause match are:

1. Object Q, an arbitrary quasicategory: `{Q : SSet.{u}} [Quasicategory Q]`.
   PASS. I read Mathlib Quasicategory/Basic.lean, including the class and hornFilling:
   this is precisely inner-horn filling, not all-horn filling.
2. Standard simplices and horns: `(Δ[n] : SSet.{u})`,
   `(Λ[n, (0 : Fin (n + 1))] : SSet.{u})`, and
   `(Λ[n, (Fin.last n)] : SSet.{u})`. PASS. I read StdSimplex.lean and Horn.lean:
   objEquiv identifies simplices with monotone maps; horn membership means an omitted
   vertex other than i, and horn_eq_iSup identifies the union of all faces other than i.
3. Dimension hypothesis: `(n : ℕ), 2 ≤ n →` in each of the four clauses. PASS.
   It is neither a fixed-dimension claim nor a claim about dimensions zero and one.
4. Initial edge [0,1]: `IsInitialHornEdge e` asserts that `stdSimplex.asOrderHom e.1`
   has values 0 and 1 on the two elements of Fin 2. PASS. For n >= 2, the literal 1
   in Fin (n+1) is the actual vertex 1. This edge exists in the zeroth horn: the
   union of its image {0,1} with the missing-face index {0} omits vertex 2.
   A monotone map out of [1] is determined by these two values; stdSimplex.ext and
   subtype proof irrelevance ensure uniqueness of the horn edge. Thus the universal
   edge predicates in the statement are equivalent to evaluation at the canonical edge,
   and are not vacuous.
5. Final edge [n-1,n]: `IsFinalHornEdge e` asserts endpoint values `⟨n - 1, by omega⟩`
   and `Fin.last n`. PASS. For n >= 2 the edge exists in the final horn, since its
   image union {n} omits vertex 0. The same uniqueness argument applies. The proof
   inside the Fin constructor only verifies a bound and introduces no mathematical
   assumption or postponed theorem.
6. Equivalence edge: `IsEquivalenceEdge Q (σ₀.app _ e)` and `IsEquivalenceEdge Q f`.
   PASS. I opened def-cbc-enhanced-diagrams-cones and EnhancedDiagramsCones.lean:
   this is exactly one inverse g and two 2-simplices t,s with short edges (f,g) and
   (g,f), and long edges the degenerate identities at the source and target of f.
   The dependency supplies real data, with no extra instance needed.
7. Initial-horn forward implication: the first conjunct quantifies over every n >= 2
   and every `σ₀ : Λ[n,0] ⟶ Q`; if its unique initial edge is an equivalence, it
   concludes `∃ σ : Δ[n] ⟶ Q, σ₀ = Λ[n,0].ι ≫ σ`. PASS: equality is exact restriction
   equality of simplicial maps, with all prescribed faces retained.
8. Final-horn forward implication: the third conjunct has the identical pattern at
   `Fin.last n`, with `IsFinalHornEdge`. PASS, including the final-edge orientation.
9. Initial converse: the second conjunct begins `∀ (f : Q _⦋1⦌)` and assumes that
   for every n >= 2 and every initial horn whose unique initial edge maps to f,
   the stated extension exists; it concludes `IsEquivalenceEdge Q f`. PASS. The
   quantifiers range over all dimensions and horn maps, in the source's order.
10. Final converse: the fourth conjunct has the same quantifiers and conclusion for
    the final edge and final horn. PASS. Each converse is available independently;
    the conjunction does not require both lifting properties as a single premise.

Edge cases: n = 2 includes the edges 01,02 of the initial horn and 02,12 of the
final horn, exactly as Kerodon requires. Dimensions zero and one are excluded only
by the source's n >= 2. The helper definitions being typeable also at n = 0,1 adds
no cases to the theorem. The empty quasicategory is allowed: there is no Nonempty
binder, no edge f, and no map from these nonempty horns into it. For Δ[0], the
unique edge is degenerate and every horn extends. In the nerve of 0 -> 1, the
nonidentity edge fails the final converse premise already on the triangle with
vertices (1,0,1) and prescribed edges 02 = id_1 and 12 = u; it fails the initial
premise dually. Thus neither converse is a tautological filler assertion. The
universe u is arbitrary and shared only by these simplicial sets; finite standard
simplices are lifted by Mathlib's existing universe-polymorphic construction. No
scheme, ring, characteristic, zero object, or index-set assumptions occur here.
All variables and universes are bound explicitly under autoImplicit false.

Independent searches (using msearch.py as prescribed, plus direct rg):

- LeanFinder: `A quasicategory edge is invertible if every horn missing its last
  face with that terminal edge extends to a simplex`. Eight hits, including
  Truncated.HomotopicR/L, Edge, quasicategory_of_filler and Quasicategory₂; no
  arbitrary-dimensional outer-horn equivalence criterion.
- LeanSearch: `Equivalence morphisms in infinity categories characterized by lifting
  outer horns`. Eight hits: Quillen fibration lifting, general HasLiftingProperty,
  and ordinary categorical cocartesian-map statements. None has this type.
- Loogle: `"horn", "IsIso"`. One hit, SSet.objEquiv_symm_notMem_horn_of_isIso.
  I opened Horn.lean: this concerns an isomorphism in the simplex category and
  nonmembership in a horn; it is not an equivalence edge in Q.
- Direct rg across all Mathlib, WeilConjectures, lean/Sheaf and the upstream-name
  index for `019F`, `outer.horn`, horn with iso/invert/equivalence, and the proposed
  declaration names. No exact match or name collision. The existing prism extension
  is a different, relative product statement and uses this item as a proof dependency;
  it is not a replacement. Existing consumers only cite this theorem in proof plans.
- I also inspected `horn.edge`, `horn.primitiveEdge`, `stdSimplex.edge`, objEquiv,
  asOrderHom and ext. The first and third construct an edge with given endpoints;
  primitiveEdge applies only to inner horns. None defines the two endpoint predicates
  or states the outer-horn criterion. The predicates here use existing Mathlib horns
  and order maps and do not introduce a second horn, simplex, or equivalence notion.

Proof interfaces checked: PushoutJoinSaturation.lean supplies the actual ordered join,
canonical pushout.desc comparison, WeaklySaturated closure condition, and the two
weak-saturation assertions needed by proof steps 2--4. I read its node and signatures;
no replacement is needed. The boundary-cell node binds Mathlib
SSet.relativeCellComplexOfMono in SimplicialSet/Skeleton.lean; I opened its construction
and confirmed the relative skeletal filtration and nondegenerate-cell indexing. I
added that Mathlib module as a proof import. EnhancedDiagramsCones is a public statement
import; PushoutJoinSaturation and Skeleton are ordinary proof imports.

Mismatches repaired: the file lacked the copyright/module header and used an ordinary
import for its statement dependency. I supplied the header and made that dependency
import public. The statement docstring only named proof dependencies and did not contain
the node's proof; I replaced it with all seven proof steps, including the explicit
2-/3-horn converse, extension closure, pushout-join generator calculation, coslice
left fibrations, inverse-triangle/lifting arguments, final filler, and order reversal.
The node's mathematical statement, theorem signature, and helper definitions are
unchanged. There are no hollow definitions, private/local aliases, or proved theorems;
the sole theorem's entire proof is sorry. All Lean lines are at most 100 characters.
The node's lean.statement is verbatim the signature before :=.

Validation: scompile.py Q14 lem-cbc-equivalence-outer-horn-filling
lean/Sheaf/CategoryTheory/EquivalenceOuterHornFilling.lean compiled both sandbox and
library contexts cleanly (2.1 s and 2.2 s), with no diagnostics. This is the only
delivered Lean file.
