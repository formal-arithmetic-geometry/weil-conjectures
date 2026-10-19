## Worker report

The module `Sheaf.AlgebraicTopology.CocartesianThreeHornFaceConservation` states
`SSet.Enhanced.cocartesian_three_horn_face_conservation`, with `sorry` as its entire
proof. Its only other declaration, `threeHornFaceInclusion`, constructs the actual
inclusion of an allowed face into the horn using Mathlib's `Subcomplex.homOfLE`.
It contains real data and no postponed theorem. No new node, dependency repair, or
statement correction is needed; only the item's `lean` field changes.

Hypotheses and conclusion, in node order:

- Small simplicial sets are `E T : SSet.{u}`. `horn 3 2` is exactly Lambda^3_2,
  and `(horn 3 2).ι` is its inclusion into `Δ[3]`.
- The given map is `r : E ⟶ (horn 3 2).toSSet`; `[InnerFibration r]` means
  the right lifting property against every inner horn, without a quasicategory
  assumption on E or the horn.
- `hlift` quantifies over every `x : E _⦋0⦌` whose image has label 1, expressed
  by `stdSimplex.obj₀Equiv ((r ≫ (horn 3 2).ι).app (op ⦋0⦌) x) = 1`.
  Its witness `e : E _⦋1⦌` has source `E.δ 1 e = x`.
  The equality of simplicial maps from `Δ[1]` says that the image edge is exactly
  `stdSimplex.map (SimplexCategory.mkOfSucc (n := 3) 1)`, the ordered edge 1→2.
  Thus its target is necessarily over 2 without an additional hypothesis.
  `IsCocartesianEdge r (SSet.yonedaEquiv.symm e)` is the dependency's outer-horn
  lifting condition over the arbitrary base; it requires no quasicategory instance.
- `[Quasicategory T]` and `t : T ⟶ Δ[3]` give precisely the specified target
  and its map. `[Mono w]` for `w : E ⟶ T` is a simplicial monomorphism, hence
  degreewise injective. `hw : w ≫ t = r ≫ (horn 3 2).ι` is `tw = ιr`.
- `hequiv` is the literal enlarged-universe categorical-equivalence testing
  expression in `SSet.exists_joyal_model_structure`: every quasicategory
  `C : SSet.{max u v}` gives an equivalence after restriction on the ordinary
  homotopy categories of internal functor simplicial sets. The same expression
  is used in the conclusion; `u v` are both explicitly declared.
- `J : Finset (Fin 4)` represents every subset of the four vertices, with
  `hJ : J.Nonempty` and exactly the disjunction of the three containments in
  `hface`. No face is restricted to being maximal.
- `stdSimplex.face J` is Mathlib's full ordered face, consisting degreewise
  of maps with image contained in J. `threeHornFaceInclusion J hface` maps
  this same face into the horn. Its three cases use complements of 3, 1, 0,
  respectively, which are the faces 012, 023, 123 of Lambda^3_2.
- The source of `pullback.map r (threeHornFaceInclusion J hface) t
  (stdSimplex.face J).ι w (𝟙 _) (horn 3 2).ι ...` is exactly E×_H Delta^J,
  and its target is T×_{Delta^3} Delta^J. The coordinate maps are w and the
  identity on Delta^J; the base map is the horn inclusion. The two required
  commutativities are `hw.symm` and the inclusion identity. This is the induced
  map w_J itself, not a chosen substitute. The conclusion is categorical
  equivalence alone, with no isomorphism clause or preservation assumption.

Recorded statement dependency declarations used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones` publicly imports Mathlib's
  `SSet`, `stdSimplex`, `horn`, `Quasicategory`, and the internal functor
  simplicial set construction. The source and docstrings of these interfaces
  and the recorded `SSet.Enhanced.coneCategory` were read; no cone construction
  is needed by this particular consumer.
- `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases` publicly
  reexports `Sheaf.CategoryTheory.InfinityFibrations`, including
  `SSet.Enhanced.IsCocartesianEdge`, and Mathlib's `SSet.InnerFibration`.
  The recorded `cocartesianFibrationOver` is the all-edges condition; this
  lemma uses the recorded constituent edge predicate for the one edge 12,
  exactly as required by its statement.
- `Sheaf.AlgebraicTopology.JoyalModelStructure`,
  `SSet.exists_joyal_model_structure`, supplies the precise testing expression
  using `hoFunctor`, `MonoidalClosed.pre`, and `uliftFunctor`.

The stated proof dependency modules `CoherentNerveComparison`,
`InfinityCocartesianMappingCriterion`, `PinchedRigidificationResolution`, and
`RigidificationEquivalenceDetection` are imported without `public` as the
stage-3 plan. The two proof dependencies
`lem-coef-derived-space-module-coyoneda` and
`lem-coef-directed-three-face-mapping-pushout` have no recorded Lean module
in the base and therefore cannot be imported yet. Neither is needed to type
this statement. The docstring reproduces all eight DAG proof steps, including
the places where those two supporting assertions will be used.

Source inspection: downloaded the cited HA.pdf to this sandbox and read printed
pp.330–332 (PDF pages 330–332). Lemma the project server has the same arbitrary-base inner
fibration and cocartesian-lift hypothesis, but asserts an existence statement
with a pullback square. The present node explicitly is an agent-formulated
supporting face comparison, not an invocation or restatement of that lemma.
The Lean docstrings preserve that distinction and the node's mapping-module
proof rather than claiming the printed K2 construction proves this comparison.

Edge cases checked before finalizing: all four singleton faces, all six edges,
and the three allowed triangles occur; the missing triangle 013 and the whole
simplex do not satisfy hface. Empty J is excluded exactly by hJ. E and face
fibers may be empty; `hlift` remains vacuous over an empty fiber at 1, as in the
node, and no nonemptiness assumption on T or any fiber is introduced. Arbitrary
u and enlarged testing universe max u v are retained. No assumption that E or H
is a quasicategory, or that t is an inner fibration, appears. No mathematical
counterexample or additional node fault was found.

Searches actually run with msearch.py (Q62, this item):

- LeanFinder: “A categorical equivalence from an inner fibration over a three
  horn with cocartesian lifts restricts to categorical equivalences on its
  faces”: eight hits, all ordinary horn inclusion/desc lemmas, no match.
- Loogle: `"SSet", "cocartesian"`: zero hits.
- Mathlib grep: `(cocartesian|coCartesian).*(horn|equivalence)|(horn|equivalence).*(cocartesian|coCartesian)`
  in AlgebraicTopology: zero hits.
- LeanSearch: “Categorical equivalence of an inner fibration over a three horn
  restricts to equivalences on faces with cocartesian lifts”: eight hits, on
  ordinary category cocartesian maps and horn desc lemmas, no match.
- Direct rg in upstream WeilConjectures and the shared lean/Sheaf tree for the
  item id, `threeHorn`, `three_horn`, `faceConservation`, and `face_conservation`:
  no declaration of this assertion. Direct searches for the two chosen full
  declaration suffixes in upstream, Mathlib, and `dag/lean_names_upstream.json`
  found no collision. The upstream-name lookup had no binding for this item.
  Searches of the shared library identified the existing inner-horn comparison,
  but that statement starts with a quasicategory over the simplex and asserts
  equivalence of the inverse horn inclusion, not equivalence of each inverse
  face under the given localization. It is not a match for this node.

Validation: scompile.py compiled the delivered file as both a sandbox module
and its final library module with no errors or warnings (about 1.3 and 1.4 s).
The first compile identified two overlong lines, both repaired before the clean
compile. The only theorem remains entirely `sorry`; the helper definition is
fully constructed. Every variable and universe is explicitly bound.

## Second reading by Q62

This is the worker's own second reading; the dispatcher explicitly prohibited
starting another agent, and the maintainer provides the independent review.
I reopened the node and signature and compared all clauses as enumerated above.
In particular I checked that the source pullback is over H itself, the target
pullback is over Delta^3, the comparison uses the actual map w on its first
coordinate, and the cocartesian hypothesis uses only the edge 12. The helper's
face indices 3,1,0 give exactly 012,023,123. The source label condition uses
vertex 1 and the edge target is vertex 2, since mkOfSucc 1 has those endpoints.
The signature includes the nonempty condition on J and retains all singleton
and empty-fiber cases. Testing categorical equivalence uses the same expression
and universes in the hypothesis and conclusion. The only textual mismatch found
was an obsolete module-docstring sentence claiming both pullbacks were formed
over the ambient simplex; it was corrected to describe the actual pullbacks.
No statement, dependency list, or proof-plan change was needed.
