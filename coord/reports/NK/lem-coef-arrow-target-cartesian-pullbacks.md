## Worker report

This is a stage-2 statement delivery for
`lem-coef-arrow-target-cartesian-pullbacks`. The module is
`lean/Sheaf/CategoryTheory/ArrowTargetCartesianPullbacks.lean`; the main declaration is
`SSet.Enhanced.arrow_target_cartesian_pullbacks`. Its only postponed proof is the named
main theorem. All helper definitions have actual data and source/blueprint docstrings.

Source checked: Lurie, Higher Topos Theory, Lemma the project server, printed pp. 531–532,
https://www.math.ias.edu/~lurie/papers/HTT.pdf, and the following discussion of transport.
The item is an auxiliary node, and its statement is retained verbatim.

Hypotheses and clauses, read against the node:

- A quasicategory in one fixed universe is `(C : SSet.{u}) [Quasicategory C]`, with
  `universe u` explicit and `autoImplicit false`. The arrow-quasicategory structure is
  produced as `∃ hArr : Quasicategory ((ihom Δ[1]).obj C)` in the conclusion, rather
  than assumed.
- Every cospan has a limiting cone is precisely
  `hC : ∀ F : (horn.{u} 2 2).toSSet ⟶ C,
  ∃ β : (coneCategory F) _⦋0⦌, IsLimiting F β`.
  This outer 2-horn has exactly the edges 0→2 and 1→2. There is no quantification
  over all diagram shapes, and hence no assumption of an empty-diagram limit.
- `Arr(C) = Fun(Δ¹,C)` is Mathlib's internal hom `(ihom Δ[1]).obj C`.
  `arrowTargetEvaluation C` is the dependency's `evaluation Δ[1] C` at vertex 1.
- Target evaluation is a Cartesian fibration is the first conjunct
  `cartesianFibration (arrowTargetEvaluation C)` of
  `ArrowTargetCartesianPullbacksStatement`.
- The coherent square of an edge `e` is its own `MonoidalClosed.uncurry e`,
  restricted along `arrowSquareCoordinates` from the published ordered-square nerve.
  Its first coordinate is the arrow direction and its second is the transformation
  direction. `ArrowPullbackSquare e` reuses
  `HomotopicalAlgebra.PointedModel.IsPullbackSquare (arrowSquare e)`.
  This fixes the apex (0,0), the cospan vertices (1,0), (0,1), (1,1), and the cone
  transformation supplied by that very square. It does not merely ask for a limit
  of the entire square diagram or for some unrelated cone on its cospan.
- The second conjunct is, for every arrow-category edge `e`,
  `IsCartesianEdge (arrowTargetEvaluation C) e ↔ ArrowPullbackSquare e`.
- The final conjunct `ArrowTargetFiberUniqueness C` quantifies over `c,c',f,y`
  with `δ 1 f = c'`, `δ 0 f = c`, and `t(y) = c`. It supplies a pullback lift
  `e₀` with `δ 0 e₀ = y` and `t(e₀) = f`, whose own square is a pullback and
  which is Cartesian. Its source arrow is therefore the projection P→c' from
  the limiting cospan cone P=z×_c c'.
- For EVERY Cartesian lift `e` with the same exact base edge `f` and target `y`,
  the definition supplies an edge `q` in `fiber (arrowTargetEvaluation C) c'`.
  The two equations using `pullback.snd` identify its source with `δ 1 e` and
  its target with `δ 1 e₀`, respectively, after the fiber inclusion. Finally
  `IsEquivalenceEdge (fiber (arrowTargetEvaluation C) c') q` states equivalence
  IN that fiber. Thus both endpoints are tied to these actual lifts, and the
  base of the equivalence is exactly c', not an unspecified vertex of C.
- The pullback and limiting predicates are the enhanced infinity-categorical
  ones. Neither a terminal object nor presentability is assumed. Pullback lifts
  are propositionally existential for each cospan; no global choice of objects
  or maps is installed.

Dependency declarations used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.evaluation`,
  `coneCategory`, `IsLimiting`, `IsEquivalenceEdge`, and their underlying comma
  constructions.
- `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases`: publicly reexports
  the original `SSet.Enhanced.IsCartesianEdge`, `cartesianFibration`, and `fiber`.
  The repaired arbitrary-base cocartesian interface is not needed here.
- `Sheaf.CategoryTheory.PointedModelStability`:
  `HomotopicalAlgebra.PointedModel.squareShape`, `cospanInSquare`, `squareCone`,
  and `IsPullbackSquare`. Its predicate is built from the published
  `HomotopicalAlgebra.FiniteReedy.IsLimitEdge`, tying the cone to both the apex
  and transformation. These helpers require no model-category hypotheses.
  Its already-landed node `lem-coef-pointed-model-stability` is added to
  `stmt_deps` solely to reuse these definitions. A dependency traversal found no
  path from that node back to this item. No dependency record is rewritten.
- `Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex`:
  `SSet.prodStdSimplex.objEquiv`, for the actual coordinate map.
- All eight stated proof dependencies are imported non-publicly:
  `EnhancedFunctorConeCalculus` (`enhanced_functor_cone_calculus`),
  `ArrowMorphismSquare` (`arrow_morphism_square`),
  `InfinityCartesianMappingCriterion` (`infinity_cartesian_mapping_criterion`),
  `CartesianMappingFiber` (`cartesian_mapping_fiber`),
  `InfinityHomotopyPullbackPasting` (`homotopy_pullback_pasting`),
  `IsofibrationExponentiation` (`isofibration_exponentiation`),
  `InfinityMappingComposition` (`mapping_composition`), and
  `InfinityTerminalPullbackCriterion` (`infinity_terminal_pullback_criterion`),
  each under `Sheaf.CategoryTheory` and namespace `SSet.Enhanced`.
  The theorem docstring records the four steps of the current node's proof.

Edge cases checked by reading the definitions:

- The empty quasicategory satisfies the cospan hypothesis vacuously; all lift
  conclusions are vacuous. No hidden terminal object is imposed. Likewise a
  two-object discrete category has pullbacks of all its cospans without a
  terminal object, so an all-diagrams hypothesis would be an erroneous strengthening.
- For a one-object terminal category all clauses reduce to its unique edges.
  Identity base edges allow the identity lift; the formula also covers every
  other Cartesian lift over that identity, with the same fixed endpoints.
- In ordinary category nerves, the square predicate fixes the actual commuting
  cone and specializes to the usual pullback universal property; an arbitrary
  limiting cone on the whole square would fail this check.
- Universe u is arbitrary. The ordered-square nerve is lifted into u; the
  intervals, horn, internal hom, fibers and all equivalence edges remain in u.

Searches for reuse (2026-10-17):

- `msearch.py ... leanfinder "Target evaluation on the arrow quasicategory is a
  Cartesian fibration when all cospans have pullbacks"`: eight ordinary-category
  fibration/lift hits, including `Functor.IsFibered.isStronglyCartesian_of_isCartesian`
  and `HasFibers.pullbackMap.isCartesian`; none states the quasicategory theorem.
- `msearch.py ... loogle '"IsCartesianEdge", "Quasicategory"'`: zero hits.
- `msearch.py ... grep 'arrow.*[Cc]artesian|target.*[Cc]artesian' AlgebraicTopology`:
  zero hits.
- `rg` in Mathlib, `WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for all seven proposed declaration names: no
  collisions. `grep -rn` for this node id in `WeilConjectures`: no hits.
- Searches of the side library for ordered squares, `IsPullbackSquare`,
  `coneCategory`, and target evaluation found the reused declarations listed
  above. The current live source query through `scompile.py --source` for
  `Sheaf.CategoryTheory.ArrowTargetCartesianPullbacks` found no existing module.

No new DAG node, dependency replacement, statement correction, or disputed statement
is introduced in this stage-2 delivery.

## Repair of returned delivery

H1: This delivery really contains the Lean module and its item `lean` record,
including the verbatim theorem signature and all seven declaration names. It no
longer refers to a nonexistent module from an earlier delivery.

H2 and stage-1 routing: The returned immutable head 40ac5bd90462 was a stage-1
re-split and must be routed to stage-1 review by the maintainer, as the return
instructs. This stage-2 packet does not reproduce its proof/status/split_report
changes or introduce its new statement node. The current shared item still has
its original four-step proof and `status: unsplit`; this delivery copies those
fields unchanged and changes only `lean` and the permitted addition of an
already-landed definition dependency to `stmt_deps`. In particular it does not
claim the re-split has landed. `lem-coef-arrow-pullback-mapping-rectangle` is not
silently bundled into this packet: its separate stage-2 delivery belongs after
its stage-1 creation/review. The main theorem docstring follows the currently
published item's proof dependencies, all of which are imported.

H3: The main hypothesis is cospan-only (`horn 2 2`), and the conclusion gives an
equivalence in the fiber at c' whose endpoint equations refer to the actual
sources of e and e₀. Both lift edges have the same specified base edge and target.
The pullback predicate also fixes the actual square's apex and cospan cone.

## Second reading by NK

The dispatcher explicitly forbids starting other agents; this section is an
explicit self-check, not a claim of independent review. The maintainer performs
the independent immutable-head reading. I reopened the node and full module,
checked every clause as above, and compared the repaired cospan and fiber
quantifiers against the return. The former all-diagrams hypothesis, unrelated
fiber equivalence, and whole-square limit test are absent. There are no new
statement nodes and no proof-field changes in this packet.

## Compilation

The prescribed per-file `scompile.py NK lem-coef-arrow-target-cartesian-pullbacks`
check compiled both its private sandbox wrapper and the actual library module
without errors or warnings. The final direct compile ran the sandbox wrapper in 2.4 s and the library module
in 2.8 s. The prescribed `deliver2.py ... --no-push` then returned
`OK (dry run): commit 06fba93204 passes the preflight and compiles; nothing pushed`.
It staged exactly this report, the item node record, and the module. The delivery
wrapper supplies the authoritative per-file compilation evidence; it will be
rerun after this evidence-only report update before the final push.
