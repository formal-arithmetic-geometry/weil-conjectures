## Worker report

The module `Sheaf.AlgebraicTopology.MarkedCocartesianLifting` states
`SSet.Enhanced.markedCoanodyne_rlp_iff_cocartesianFibration` with proof `sorry`.
It uses the marked simplicial set whose underlying simplicial set is `E`, whose
marked 1-simplices are `T`, and whose degenerate edges are supplied by `hT`.
The map to `SSet.Marked.sharp B` has underlying map `p` and therefore preserves
all markings.  The left side is exactly
`SSet.Marked.markedCoanodyne.rlp` of this marked map, so its lifting problems
are commutative squares of marked maps and their diagonals preserve markings.

The hypotheses and clauses are rendered as follows.  `E` and `B` are small
simplicial sets in one universe, `p : E ⟶ B`, and the typeclass binders
`[Quasicategory E] [Quasicategory B]` express that they are quasicategories.
`T : Set (E.obj (op ⦋1⦌))` is the set of marked edges.  The hypothesis
`hT : ∀ x : E.obj (op ⦋0⦌), E.σ 0 x ∈ T` says every degenerate edge is marked
and is used as the `degenerate` field of `SSet.Marked`.  The left hand side is
lifting against every member of the recorded marked coanodyne class.  The
right hand side conjoins `cocartesianFibration p` with the assertion that for
every edge represented by `e : E.obj (op ⦋1⦌)`, membership in `T` is equivalent
to `IsCocartesianEdge p (SSet.yonedaEquiv.symm e)`.  Yoneda converts the marked
1-simplex into the edge map `Δ[1] ⟶ E`, so this is exactly that `T` is the set
of `p`-cocartesian edges.  The declared `cocartesianFibration` supplies the
inner-fibration condition and a cocartesian lift over every base edge from
every prescribed source, as required by the node.

The statement dependency declarations used are:

* `Sheaf.AlgebraicTopology.MarkedCoanodyne`,
  `SSet.Marked.markedCoanodyne` (including the marked-map category, `sharp`,
  and the four marked coanodyne generating families).
* `Sheaf.CategoryTheory.InfinityFibrations`,
  `SSet.Enhanced.cocartesianFibration` and
  `SSet.Enhanced.IsCocartesianEdge`.

The proof dependency `lem-cbc-inner-fibration-equivalence-outer-horn-lift` is
stated in `Sheaf.CategoryTheory.InnerFibrationEquivalenceOuterHornLift` and is
imported privately.  The saturation proof dependency uses Mathlib's
`CategoryTheory.MorphismProperty.rlp_llp_rlp`, imported privately from
`Mathlib.CategoryTheory.MorphismProperty.LiftingProperty`. The two remaining
proof dependencies, cocartesian composition/initiality and the core Kan
fibration theorem, have no recorded Lean declaration yet, so no additional
import is available for them.

I checked the edge cases named by the definitions and source: the empty total
simplicial set, the identity map with sharp marking, the base point, dimensions
`n = 1` and `n = 2` in the initial-horn condition, empty Kan complexes, and the
walking isomorphism over a point (which correctly fails the Kan-core marking
lifting condition when its nondegenerate edge is unmarked).  The degenerate
edge condition is explicit, so zero and degenerate edges cannot be omitted.
The Yoneda conversion keeps the full 1-simplex universe and does not restrict
edge objects.

Searches for an existing declaration were made with:

* `msearch.py ... leanfinder "marked coanodyne right lifting property
  cocartesian fibration exactly cocartesian edges"`: only ordinary-category
  `IsCocartesian` and unmarked horn declarations; no match.
* `msearch.py ... loogle "marked coanodyne, cocartesian fibration,
  Quasicategory"`: no hits (`marked` is not a Loogle identifier).
* `msearch.py ... grep "marked.?coanodyne|marked.?cocartesian"
  AlgebraicTopology`: no hits in Mathlib.
* `rg -n "markedCoanodyne|marked coanodyne|cocartesianFibration|
  markedCoanodyne_rlp"` over the source and project: only the two recorded
  dependency declarations and no theorem with this lifting equivalence.
* `grep -rl 'lem-coef-infinity-marked-cocartesian-lifting' dag/nodes`: only
  this node and its own references; no duplicate statement node.

No existing declaration says the marked quasicategorical assertion, so a new
statement module was necessary.  No node fault or `STATEMENT-DISPUTED` flag
was found.

The independent second reader will supply the second-reading section.

Source check: I opened HTT online and read Proposition the project server and Remark
the project server with Definition the project server. Their opposite-category dual agrees with
the displayed equivalence and the dependency generators.

Additional searches: `msearch.py ... leansearch "Marked cocartesian fibrations
characterized by right lifting against marked coanodyne extensions"` returned
only ordinary cocartesian and general model-category lifting declarations.
`msearch.py ... loogle '"Cocartesian"'` returned ordinary-category hom-set
lifting predicates, not this simplicial statement.  The source tree and
`dag/lean_names_upstream.json` contain neither this item id nor the proposed
name nor `markedCoanodyne`.  I read Mathlib's `MorphismProperty.rlp` and
`rlp_llp_rlp`; the former quantifies over all marked-map squares through
`HasLiftingProperty`.  Its module is imported as a proof dependency.

Final compilation through `scompile.py` succeeded without errors or warnings.
UTC record date from `date -u +%F`: 2026-10-16.

## Second reading by NX

I independently read the shared node, the delivered module, both statement-dependency
nodes and their recorded source modules, and the worker report. There is no
`statement_change`, no new definition node, and no dependency module in this delivery.
The only node change relative to the shared copy is its `lean` record. No repair note
exists for this item.

Source check: I opened [HTT](https://www.math.ias.edu/~lurie/papers/HTT.pdf),
Definition the project server, Definition the project server, Proposition the project server and its proof
(printed pages 149–150), and Remark the project server (printed page 151).
The sharp-target specialization and reversal of simplex order give this node's
cocartesian assertion. The source uses marked simplicial maps; no finiteness,
nonemptiness, field or characteristic hypothesis is implicit. The node explicitly
works with small quasicategories, as does the Lean. This is an HTT source, not a
Stacks result, so there is no Stacks `.tex` passage for this item.

My object/hypothesis/conclusion checklist, matched with the actual signature:

1. Small simplicial sets `E` and `B`: `{E B : SSet.{u}}`, with `universe u`
   explicitly bound. Verdict: exact; both are small in the chosen universe.
2. Both are quasicategories: `[Quasicategory E] [Quasicategory B]`.
   Verdict: exact, with no additional category or fibration instance assumed.
3. An arbitrary simplicial map from the total space to the base: `(p : E ⟶ B)`.
   Verdict: exact; inner fibrancy is a conclusion on the right, not a hypothesis.
4. A set of total-space edges containing every degenerate edge:
   `(T : Set (E.obj (op ⦋1⦌)))` and
   `(hT : ∀ x : E.obj (op ⦋0⦌), E.σ 0 x ∈ T)`.
   Verdict: exact; `σ 0` gives all degenerate 1-simplices.
5. The marked total space and sharply marked base:
   `{ underlying := E, marking := T, degenerate := hT } : SSet.Marked.{u}`
   and `SSet.Marked.sharp B`. The marked arrow is
   `⟨p, fun _ _ ↦ Set.mem_univ _⟩`. Verdict: exact; its underlying map is
   precisely `p`, and sharpness makes its marking-preservation proof valid for
   every `p` and `T` without adding a hypothesis.
6. Left conclusion: `SSet.Marked.markedCoanodyne.rlp` of that marked arrow.
   Verdict: exact. I read `MorphismProperty.rlp` in Mathlib's
   `CategoryTheory/MorphismProperty/LiftingProperty.lean` and
   `HasLiftingProperty` in `CategoryTheory/LiftingProperties/Basic.lean`:
   this quantifies over every coanodyne marked arrow and every commutative
   square, with a diagonal in the marked category satisfying both triangle
   equalities. In particular the specified base map is retained.
7. Right conclusion, first clause: `cocartesianFibration p`.
   Verdict: exact. I opened `Sheaf.CategoryTheory.InfinityFibrations`:
   its definition conjoins Mathlib `InnerFibration p` with a cocartesian lift
   of every specified base edge from every prescribed source. Its source
   face is `δ 1`, and the base-edge equality is strict.
8. Right conclusion, second clause:
   `∀ e : E.obj (op ⦋1⦌), e ∈ T ↔
     IsCocartesianEdge p (SSet.yonedaEquiv.symm e)`.
   Verdict: exact equality of the two edge sets, not only one inclusion.
   Yoneda represents exactly the given 1-simplex as a map `Δ[1] ⟶ E`.
   The recorded edge predicate tests all initial outer horns of dimension
   at least two with ordered edge `{0,1}` fixed and both filler equalities
   over the base. No mapping-space substitute is used.
9. The outer connective is `↔`, whose right side is the conjunction of
   items 7 and 8. Verdict: both directions and every clause are present,
   with the objects and marking quantified before the equivalence.

Dependency identity check: I read the `Marked` structure, its `Hom` and category
instance, and `sharp` in `MarkedPointCartesianModel.lean`, as well as
`initialMarkedSimplex`, `initialMarkedHorn`, `coanodyneGenerators`, and
`markedCoanodyne` in `MarkedCoanodyne.lean`. The marked category preserves
marked edges. Its coanodyne class uses inner flat horns, positive-dimensional
initial marked horns, the consecutive-edge triangle marking extension, and
`K.flat → K.sharp` for every small Kan complex, with the recorded weak
saturation. These are the node's dependencies, not private definitions or
unmarked anodynes. The imported `InnerFibrationEquivalenceOuterHornLift`
states the required relative initial-horn assertion with the base simplex
fixed. The saturation Mathlib proof dependency is imported privately.
The composition/initiality and core-Kan proof-dependency nodes currently have
no recorded Lean module, so the worker correctly did not invent imports for them.

Edge cases: empty `E` is allowed, and both lift conditions have no prescribed
source there. Empty `B` is allowed (a map to it forces empty `E`). For the
identity, every edge is relatively cocartesian, so sharp marking is exactly
what the equivalence requires. For a map to a point, the right marking is the
equivalence edges; a walking isomorphism with only degeneracies marked fails
family (iv), as required. Initial horns start in dimension one: their source
vertex supplies lifts from the prescribed source; dimension two tests the
initial edge already present in the horn. There is no dimension-zero outer-horn
requirement. Empty Kan complexes are included, and their marking extension is
an identity. There is no nonempty index set, zero-object, scheme, coefficient,
or characteristic parameter to restrict. The arbitrary universe `u` is shared
by the recorded simplicial and marked categories; no extra universe equality
or size hypothesis has been imposed. All variables are explicitly bound under
`autoImplicit false`.

Independent duplicate searches on this reading:

- `msearch.py NX lem-coef-infinity-marked-cocartesian-lifting leanfinder
  "marked cocartesian lifting coanodyne"`: eight hits, all ordinary-category
  `Functor.IsCocartesian` or `IsStronglyCocartesian` facts. Their displayed
  types concern Hom-set lifts, not marked simplicial maps.
- `msearch.py ... loogle '"Quasicategory", "lifting"'`: three hits, namely
  `quasicategory_of_hasLiftingProperty`, `Quasicategory.hasLiftingProperty`
  and `quasicategory_iff_hasLiftingProperty`. Their types concern unmarked
  inner horns and a terminal target, not this equivalence.
- `msearch.py ... grep
  'marked.?coanodyne|cocartesianFibration|IsCocartesianEdge'
  AlgebraicTopology`: zero hits in Mathlib.
- `rg` for the theorem name, `markedCoanodyne`, and cocartesian/marked variants
  in Mathlib, `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`,
  `dag/lean_names_upstream.json`, and shared `lean/Sheaf`: the exact theorem
  is absent. Shared occurrences define the recorded dependencies or use
  cocartesian edges. I also opened `MarkedRelativeCartesianModel.lean` and
  `MarkedAnodyneLiftingCalculus.lean`: they state different model-structure
  or cartesian/absolute lifting packages, not this coanodyne equivalence.
  DAG searches find the existing node and its consumers, not a duplicate.

Docstring/proof check: the sole theorem has proof `sorry`, as stage 2 requires.
There are no definitions with postponed data, helper theorems, private copies,
local notation or local instances. The module and theorem cite the source and
this blueprint id. The theorem docstring retains all five node proof steps:
generator reduction; inner horns, lift existence and reverse marking inclusion;
initial-horn converse; triangle composition; and Kan marking via equivalence
outer-horn lifting followed by saturation. No clause was weakened or proved.
Every Lean line is within 100 characters. I compared the extracted signature
with `lean.statement` as strings: they are verbatim equal.

Mismatches found: none. Changes made: only this second-reading report; the
Lean statement, its proof docstring, dependencies and node statement are retained.
`python3 /home/ubuntu/weil-launcher-nt/scompile.py NX
lem-coef-infinity-marked-cocartesian-lifting
lean/Sheaf/AlgebraicTopology/MarkedCocartesianLifting.lean` succeeded for the
sandbox and library module, with no errors or warnings. There are no sibling
modules to compile. The delivery dry run is the remaining packaging check.
