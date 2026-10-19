## Worker report

Item: `lem-coef-infinity-cartesian-edge-transitivity`.
Module: `Sheaf.CategoryTheory.CartesianEdgeTransitivity`.
Declaration: `SSet.Enhanced.isCartesianEdge_iff_comp_of_isCartesianEdge`.

The module states precisely the existing node, with a single postponed theorem
and no new definitions. Only the node's `lean` record changes. Its docstring
contains all five steps of the node's mapping-space/pasting proof and names
each proof dependency. No repair note for this item is present.

Clause-by-clause correspondence:

- A fixed universe: explicitly declared `universe u` and `{A D B : SSet.{u}}`.
- Three quasicategories: `[Quasicategory A]`, `[Quasicategory D]`,
  `[Quasicategory B]`, using Mathlib's inner-horn filling classes.
- Simplicial maps `a : A → D`, `b : D → B`: `(a : A ⟶ D) (b : D ⟶ B)`.
- Both maps inner fibrations: `[InnerFibration a] [InnerFibration b]`.
- An arbitrary edge `h : u → v` of `A`: `(h : Δ[1] ⟶ A)`.
  The endpoint vertices are exactly its restrictions to vertices 0 and 1;
  writing them separately would introduce redundant endpoint equations.
- Its image is `b`-cartesian: `(hh : IsCartesianEdge b (h ≫ a))`.
- The first condition in the conclusion: `IsCartesianEdge a h`.
- The second condition: `IsCartesianEdge (a ≫ b) h`, since category notation
  `a ≫ b` is the simplicial map `b ∘ a`.
- The two directions are exactly `↔`. There is no requirement for cartesian
  lifts of any other edge.

Dependency declarations and imports:

- `def-cbc-enhanced-diagrams-cones`: public import
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`, its recorded
  `SSet.Enhanced.coneCategory` is not needed for this statement. The module
  publicly provides Mathlib's `SSet`, `SSet.Quasicategory`, `SSet.stdSimplex`
  and simplicial-map category. These primitives are used directly as the
  dependency's docstring prescribes; there is no copied quasicategory notion.
- `def-coef-infinity-fibrations`: public import its currently recorded module
  `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases`. Its
  `SSet.Enhanced.cocartesianFibrationOver` is the arbitrary-base extension;
  the module publicly reexports `Sheaf.CategoryTheory.InfinityFibrations`,
  including `SSet.Enhanced.IsCartesianEdge`, and Mathlib's
  `SSet.InnerFibration`. Read the entire original edge definition: the
  final outer horn is `horn n (Fin.last n)` and the distinguished edge
  is `{n-1,n}`, so this is the cartesian orientation in the item.
- Proof-only import `Sheaf.CategoryTheory.RightPinchComparison`:
  `SSet.Enhanced.right_pinch_comparison`.
- Proof-only import `Sheaf.CategoryTheory.InfinityHomBifunctorFunctoriality`:
  `SSet.Enhanced.infinity_hom_bifunctor_functoriality`.
- Proof-only import `Sheaf.CategoryTheory.InfinityHomotopyPullbackPasting`:
  `SSet.Enhanced.homotopy_pullback_pasting_specified` (and its strict form).
- `lem-coef-infinity-cartesian-mapping-criterion` currently has no `lean`
  record or Mathlib match, so there is no module to import for that proof
  dependency. It supplies no object needed to type the present statement.
  Its future proof-only import is for the maintainer to add after it lands,
  as prescribed in stages/2-statements.md section 3, rule 7. No missing
  statement prerequisite or helper is being deferred by this delivery.

Source checked directly: [Kerodon Corollary the project server, Tag 01TU](https://kerodon.net/tag/01TU),
assertion (1), on 2026-10-17. It is the same cancellation assertion for inner
fibrations of simplicial sets; the node explicitly restricts to quasicategories,
which the Lean binders retain. The source's lower-square/pasting proof agrees
with the five-step proof recorded in the node. No statement fault or dispute.

Edge cases checked mathematically before writing:

- Empty `A`: there is no edge `Δ[1] ⟶ A`; the universal statement is vacuous,
  without imposing nonemptiness on any quasicategory or mapping space.
- `a` the identity: its image is precisely `h`; the hypothesis makes the
  composite-side condition true, while every edge is cartesian over identity.
- `b` the identity: every image edge is cartesian over identity and the two
  conditions coincide, up to the identity law.
- `B` a point: its cartesian edges in `D` are equivalences. The assertion
  specializes to cancellation over an equivalence, consistent with the source.
- Degenerate edges and empty mapping spaces are allowed. No invertibility,
  Kan-fibration, cartesian-fibration or object-surjectivity assumption is added.
- The common universe is arbitrary, matching the fixed-universe node; no
  independent smaller testing universe occurs in the signature.

Searches performed through `msearch.py NR lem-coef-infinity-cartesian-edge-transitivity`:

- LeanFinder: `For inner fibrations of quasicategories a and b, if a(h) is
  b-cartesian then h is a-cartesian if and only if h is cartesian for the composite`.
  Eight hits; ordinary-category `IsStronglyCartesian.of_comp`, `.comp`, and
  `IsFibered.comp` dominate. Read `FiberedCategory/Cartesian.lean:288-337`
  and `Fibered.lean:45-85`: they compose two arrows for one ordinary functor,
  not two inner fibrations. None is an exact match.
- Loogle: `"SSet", "cartesian"`. Zero hits.
- Grep: `[Cc]artesian|[Cc]ocartesian|[Tt]ransitiv` under
  `AlgebraicTopology/Quasicategory`. Three hits: a cartesian-closed-category
  comment and left/right edge-homotopy transitivity; no cartesian-edge theorem.
- LeanSearch: `Cartesian edge cancellation for a composite of two inner
  fibrations of quasicategories`. Eight hits, again ordinary fibered-category
  composition, composition of truncated edges and general fibrations; no match.
- `rg` in slopmaster2 `WeilConjectures`, shared `lean/Sheaf`, Mathlib and
  `dag/lean_names_upstream.json` for the proposed name and cartesian/transitivity
  patterns. No existing declaration of this statement. The existing
  `CartesianFibrationPullback` uses transitivity in its proof docstring but
  states the componentwise-cartesian pullback criterion, a different theorem.
- `rg` for `IsCartesianEdge` located the existing dependency definition and its
  consumers, reused here. `grep -rn` for this exact node id in upstream
  `WeilConjectures` found no match. Raw remote search results are preserved
  in the sandbox `searches.jsonl` generated by the prescribed wrapper.

Validation: `scompile.py NR lem-coef-infinity-cartesian-edge-transitivity`
compiled this module separately at both sandbox and library paths, cleanly
(1.2 s and 1.4 s). Every universe and variable is explicitly bound;
`autoImplicit` is false. The only theorem has `by sorry`, as required.

## Second reading by NR

This is the worker's second pass, with both the node copy and final Lean module
open; no separate agent was started, as the dispatcher's brief forbids it.
The maintainer performs the independent delivery review.

Rechecked all three quasicategory instances, both inner-fibration instances,
the arbitrary edge, the image hypothesis `IsCartesianEdge b (h ≫ a)`, the
orientation of composition `a ≫ b`, and both sides of the `↔` against the
unchanged node statement. Endpoint vertices are intrinsic to the chosen
simplex map. The cartesian predicate is the recorded final-horn predicate,
not an ordinary-category or cocartesian replacement. Rechecked the common
universe, the lack of nonemptiness requirements and all five docstring proof
steps. No mismatch found and no changes were needed after this pass.
