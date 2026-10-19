## Worker report

Item: `lem-coef-infinity-cocartesian-prism-comparison`, Q85 stage 2.
Module: `Sheaf.CategoryTheory.InfinityCocartesianPrismComparison`.
Main declaration: `SSet.Enhanced.cocartesian_prism_comparison`.

The module constructs both prism pushouts and their canonical comparison maps, and
states their categorical equivalence with the main theorem and four compatibility lemmas with `sorry`. Every definition has real
data. There are no other postponed theorems, new nodes, dependency repairs, or
statement changes. All 19 declarations are listed in `lean.declarations`.

Source checked directly: [Higher Algebra](https://people.math.harvard.edu/~lurie/papers/HA.pdf),
Lemma 2.4.4.6, printed p. 308 (PDF index 307), the two displayed maps immediately
following the choice of h. The displays are exactly the node's A and B maps.
The invoked general comparison is [Higher Topos Theory](https://people.math.harvard.edu/~lurie/papers/HTT.pdf),
Definition 3.2.2.6 and Proposition 3.2.2.7(2), printed p. 180 (PDF index 197
in the currently served edition). Read their mapping-simplex formulas and all
three quasi-equivalence conditions. The underlying unit record and both the
inherited biduality section and the current exceptional-adjoint statement were
also read. The item is a subargument, not a unit statement. The complete five-step
DAG proof is included in the theorem docstring. Its three additional proof-only
modules are imported without `public`.

Hypothesis and clause correspondence:

- Small simplicial sets, standard simplices and quasicategories are Mathlib's
  `SSet.{u}`, `Δ[n]`, and `SSet.Quasicategory`, publicly reexported by the recorded
  enhanced-diagram dependency. Both universes `u v` are explicitly declared and
  `autoImplicit` is false.
- The map p is `(p : C ⟶ Δ[2])`. The total quasicategory hypothesis is
  `[Quasicategory C]`, and the inner-fibration hypothesis is `(hp : InnerFibration p)`.
- `prismFiber p j` is exactly the existing `SSet.Enhanced.fiber p` at
  `stdSimplex.obj₀Equiv.symm j`; no new fiber convention is introduced. Its factors
  are ordered as point ×_base C, exactly as the recorded `fiber` declaration.
  `prismFiberInclusion p j` is its canonical `pullback.snd`.
- `prismEdge01` and `prismEdge12` are the existing face maps `stdSimplex.δ 2` and
  `stdSimplex.δ 0`. `prismFace01 p` and `prismFace12 p` are their pullbacks along p,
  so these are C_01 and D = C_12 with the interval coordinate retained.
- The transport is `(h : prismFiber p 0 ⊗ Δ[1] ⟶ C)`. Mathlib's cartesian tensor
  is the degreewise product. The node writes Δ¹ × C_0; exchanging the two
  coordinates gives precisely the chosen C_0 × Δ¹ convention, with no restriction
  on h. `hbase` says h followed by p is the interval projection followed by edge 01.
- `hzero : SSet.ι₀ ≫ h = prismFiberInclusion p 0` is exactly the entire zero-end
  restriction being the inclusion, not merely a condition on vertices.
- `(F : prismFiber p 0 ⟶ prismFiber p 1)` with
  `hone : SSet.ι₁ ≫ h = F ≫ prismFiberInclusion p 1` identifies F with the endpoint
  restriction. This does not add a mathematical hypothesis: `hbase` factors the
  endpoint through the strict fiber and its inclusion is monic, so the stated F
  is the unique endpoint restriction. The source itself names this functor F.
- `hcocart` quantifies over every vertex `x : (prismFiber p 0) _⦋0⦌` and asserts
  `IsCocartesianEdge p (lift (SSet.const x) (𝟙 Δ[1]) ≫ h)`. This is the actual
  vertical edge, using the recorded horn-cocartesian predicate and the product
  map whose first coordinate is x and second coordinate is the identity interval.
- The fiber-one inclusions into the two edge pullbacks are actual `pullback.lift`
  maps. Their interval coordinates are respectively 1 (in edge 01) and 0 (in
  edge 12), both representing the global vertex 1; their total coordinates are
  `prismFiberInclusion p 1`. This orientation was checked explicitly.
- `prismPushoutA p F` is `pushout SSet.ι₁ F`, with the first leg mapping C_0 to
  its top cylinder endpoint. `prismPushoutB p F` is
  `pushout SSet.ι₁ (F ≫ prismFiberOneToFace12 p)`. These are the two actual
  categorical pushouts of presheaves, computed degreewise as required.
- `prismTransportToFace01 p h hbase` is the canonical `pullback.lift` of h with
  its specified interval coordinate. `prismComparisonA` is `pushout.desc` from
  this map and the fiber-one inclusion into C_01; `prismComparisonB` is
  `pushout.desc` from h and the inclusion D → C. Their compatibility proofs use
  `hone`, pullback uniqueness, and the endpoint identities. Neither comparison
  is an arbitrary parameter, a choice from existence, or inferred from the
  theorem being stated.
- The conclusion is a conjunction, first for `prismComparisonA p h F hbase hone`
  and then for `prismComparisonB p h F hone`. Each uses exactly the recorded
  Joyal weak-equivalence condition: for every `Z : SSet.{max u v}` that is a
  quasicategory, restriction on internal functors after `uliftFunctor.{v,u}`
  induces an equivalence on `hoFunctor`. Thus arbitrary enlargements of the
  testing universe are included. There is no alternative categorical-equivalence
  predicate or choice of a model structure in the statement.
- No lifts over edges 12 or 02, no cocartesian-fibration structure on p, and no
  nonempty-fiber assumptions occur.

Dependency declarations read and used:

1. `Sheaf.CategoryTheory.EnhancedDiagramsCones` publicly exposes Mathlib's `SSet`,
   `stdSimplex`, `Quasicategory`, degreewise cartesian tensor and internal hom.
   The module docstring and corresponding definitions were read.
2. The recorded `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases`
   publicly reexports `Sheaf.CategoryTheory.InfinityFibrations`. Its complete
   interface was read: `InnerFibration`, `IsCocartesianEdge`, and `fiber` are
   the predicates and construction used here. Its `cocartesianFibrationOver`
   predicate is not imposed: the node only assumes an inner fibration.
3. `Sheaf.AlgebraicTopology.JoyalModelStructure`,
   `SSet.exists_joyal_model_structure`: read its full signature and docstring.
   Its exact enlarged-universe weak-equivalence test is used in both conclusions.
4. Proof-only `Sheaf.CategoryTheory.InfinityCocartesianCompositionInitiality`,
   `SSet.Enhanced.cocartesian_composition_initiality`: its degenerate-edge clause
   is used in step 2 of the included proof plan.
5. Proof-only `Sheaf.CategoryTheory.CartesianMappingSimplexPresentation`,
   `SSet.Enhanced.SimplexChain`, `mappingSimplex`, its operators and marking:
   used for the reversed length-one mapping-simplex identification in step 3.
6. Proof-only `Sheaf.CategoryTheory.MappingSimplexUniversalEquivalence`,
   `SSet.Enhanced.mapping_simplex_universal_equivalence`: its full assumptions
   and signature were read; step 4 applies it twice with n = 1 and T = Δ¹.

Edge cases checked mathematically before finalization:

- C empty: all fibers, products, faces and pushouts are empty; both comparisons
  are isomorphisms. The vertexwise cocartesian condition is vacuous as intended.
- C_0 empty with C possibly nonempty: there are no simplices with a vertex over
  zero (otherwise that vertex would inhabit C_0). Thus C_01 is C_1 and C is D;
  both pushouts reduce to the displayed last factors, and comparisons are
  isomorphisms. No chosen object of C_0 is used by any definition.
- C_1 empty forces C_0 empty through the specified transport. This is allowed,
  and C_2 may still be arbitrary.
- C_2 empty is allowed: D reduces to C_1 and the maps specialize to the interval
  comparison without requiring any outgoing edge from C_1.
- p = identity of Δ² and standard h: A → C_01 is an isomorphism and B → C is
  the spine/inner-horn map Λ²_1 → Δ². The endpoint used to attach D is its zero
  endpoint (global vertex 1), as prescribed, rather than its terminal vertex 2.
- Quasicategory tests range over `max u v`; no site/coefficient equality or
  extra smallness, fibrancy of A or B, or universe restriction was introduced.

Searches for existing declarations (all run in this task):

- `msearch.py ... leanfinder` query: “Chosen cocartesian transport over the
  two-simplex gives categorical equivalences from mapping cylinder pushouts to
  the total simplicial set”. Eight hits, including `SSet.horn₂₁.isPushout`,
  the other two-dimensional horn pushouts, and `HomotopicalAlgebra.Precylinder.trans`.
  The horn results construct a base horn; the cylinder result glues two model
  category precylinders. None asserts either of these total-space equivalences.
- `msearch.py ... loogle` query: `"SSet", "Cocartesian"`. Zero hits.
- `msearch.py ... grep` query:
  `cocartesian.*prism|mapping.?cylinder.*equiv|prism.*comparison`, restricted to
  `AlgebraicTopology`. Zero hits.
- `msearch.py ... leansearch` query: “The two prism pushout maps obtained from
  a chosen cocartesian transport over a triangle are categorical equivalences”.
  Eight hits on ordinary pushout isomorphisms and ordinary-category cocartesian
  factorization, including `pushout.map_isIso`, `pushout.congrHom` and
  `CategoryTheory.Functor.IsCocartesian.fac`; none has the required simplicial
  cocartesian-edge or Joyal hypotheses/conclusions.
- `rg` searched upstream `WeilConjectures/`, Mathlib's `AlgebraicTopology`, the
  shared project's `lean/Sheaf`, and `dag/lean_names_upstream.json` for the item
  id and `cocartesian.*prism|prism.*comparison|prismFiber|prismPushout`.
  No existing statement or conflicting declaration was found. The existing
  `CocartesianInnerHornComparison` proves the inverse-image inner-horn assertion;
  its docstring contains this prism argument but its signature has no chosen h
  and states neither pushout comparison. It therefore cannot be rebound here.
  The mapping-simplex comparison is more general and requires constructing the
  reversed chain and verifying its hypotheses, so is retained as the proof dependency.
- `searches.jsonl` retains the unmodified msearch records, timestamps, hit names,
  and result digests. Their queries and results are reproduced above.

No statement dispute or node fault was found. The node copy changes only `lean`.
The final signature is recorded verbatim, and the main theorem and its four named compatibility obligations have `sorry` proofs.
Single-file validation uses only the prescribed `scompile.py` wrapper; no global
build or direct shared-repository mutation was performed.

## Second reading by Q85

Independent maintainer reading of immutable delivery
`41dd9d2bde753dfb2080e3439526d0d638b8f7c0`, 2026-10-18.
This replaces the author's explicitly non-independent final pass. I read the
item, all three statement-dependency nodes, their actual imported declarations,
the three proof-only dependency interfaces, the complete delivered module and
report, and HA 2.4.4.6 p. 308 plus HTT 3.2.2.6 and 3.2.2.7(2) p. 180 online.

The clause-by-clause correspondence in the Worker report is correct. In particular:
`SSet.{u}`, `p`, `[Quasicategory C]`, and `hp` give precisely the small total space
and inner fibration. `prismFiber` reuses `fiber`; the two face pullbacks use
`δ 2` and `δ 0`. Exchanging product factors explains the cylinder convention.
`hbase`, `hzero`, and vertexwise `hcocart` express the three conditions on h.
`F` with `hone` is its uniquely determined fiber-one restriction, not extra
transport data. The face-12 inclusion uses interval vertex 0, the global vertex 1.
The pushouts attach the top endpoint along F and its face-12 inclusion.
`pullback.lift` and `pushout.desc` define the prescribed comparison maps, without
arbitrary maps or existential choices. The two conclusion conjuncts use exactly
the enlarged-universe `hoFunctor` restriction test in the Joyal dependency.
The universes u and v remain independent; `max u v` includes every enlargement.
No lifts over 12 or 02, nonempty fibers, or fibrancy of A or B are assumed.

The five proof steps are sound: the monotone-vertex horn calculation covers the
two-dimensional exceptional case for the collapse 0,1,2 → 0,1,1; pullback
restriction gives the interval fibration; degenerate-edge cocartesianness is
available with its required quasicategory assumptions; reversal produces the
displayed chains with opposite fibers; the explicit mapping-simplex operators,
marking and identity fiber maps satisfy the comparison theorem. Taking opposites
preserves the exact functor-test equivalences. No unstated DAG prerequisite or
universe repair is needed.

Checked empty C, empty C_0, empty C_1 (forcing empty C_0), empty C_2, and the
identity map of Δ² (an isomorphism and the inner-horn inclusion). No edge case
is excluded. Independent rg searches in Mathlib AlgebraicTopology, upstream
WeilConjectures, and project Sheaf found no duplicate prism statement; the
inverse-horn comparison and ordinary-category cylinder results are different.
The worker also records LeanSearch, LeanFinder, Loogle and grep searches.

Mechanical corrections: move the four inline pullback/pushout compatibility
proofs into named `sorry` lemmas with source, blueprint and proof-plan docstrings,
as required by the review's no-local-proof gate. They belong to this node's
specified canonical constructions and are listed in lean.declarations; no new
mathematical notion, hypothesis or main conclusion is introduced. Definitions
retain their actual data. Correct the two corrupted source references above.
The main lean.statement is unchanged and verbatim equal to the source signature.
All 19 declarations have docstrings, every proof body is sorry, autoImplicit is
false, and no Lean line exceeds 100 characters.

Compiler reproduction through the prescribed scompile.py wrapper, using each
complete file separately against the side overlay and server confirmation:
original sandbox 2.5 s / library 2.4 s; replacement sandbox 2.3 s / library 2.6 s;
both calls exited 0 with no errors or warnings printed. This confirms the
worker's recorded successful per-file validation. No global build, direct ssh,
branch change, live Lean write, claim, delivery or merge was performed.

Verdict: FIX for the proof-organization and report corrections only; the
mathematical statement and canonical constructions are accepted.
