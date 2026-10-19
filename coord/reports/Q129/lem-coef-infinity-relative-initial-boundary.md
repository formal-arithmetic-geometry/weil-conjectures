## Worker report

The module `Sheaf.CategoryTheory.RelativeInitialBoundary` defines
`SSet.Enhanced.IsRelativeInitial` and `SSet.Enhanced.IsRelativeFinal` exactly as the
node introduces them, and states
`SSet.Enhanced.relative_initial_final_iff_boundary_fillers`. The theorem has one
`sorry`; both definitions have complete data. The two definitions belong to the
notion explicitly introduced in this node, so no new definition node is needed.
The item JSON changes only in `lean`. There is no statement correction or dispute.

Source read: [Kerodon 02WS](https://kerodon.net/tag/02WS), Corollary the project server,
conditions (1) and (3), and [Kerodon 02WR](https://kerodon.net/tag/02WR), Proposition
the project server, including its mapping-space interpretation and opposite dual.
02WS explicitly requires an inner fibration between quasicategories, fixes the
first vertex, and excludes dimension zero. The final clause is its opposite dual.
The expanded six-step DAG proof is retained in the theorem's docstring: relative
right slice, its inner-horn calculation, fiberwise Kan fibrations, the two fiber
criteria, the boundary/join correspondence including its dimension-zero slice
case, and the natural pinch/opposite comparison.

Hypotheses and clauses, in node order:

| Node text | Lean rendering |
| --- | --- |
| Simplicial sets and quasicategories | `{X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]`, with the universe `u` explicitly declared. |
| Boundary is the union of proper faces | Mathlib `boundary`, written `∂Δ[n + 1]`; `boundary_eq_iSup` identifies it with the union of all faces. No new boundary definition is introduced. |
| `p : X → Y` is an inner fibration | `(p : X ⟶ Y) [InnerFibration p]`; Mathlib's class is right lifting against all inner horns. |
| Specified vertex `x` | `(x : X _⦋0⦌)`. |
| `p`-initial means all outgoing mapping maps are weak equivalences | `IsRelativeInitial p x := ∀ z, IsWeakHomotopyEquivalence (mappingSpaceMap p x z)`. The codomain is definitionally `mappingSpace Y (p.app _ x) (p.app _ z)`. |
| Initiality iff every positive boundary problem fills | The first `↔` in the theorem. `n : ℕ` indexes the dimension `n+1`, so exactly every positive dimension occurs. |
| Boundary and base maps | `a : (∂Δ[n + 1] : SSet.{u}) ⟶ X`, `b : (Δ[n + 1] : SSet.{u}) ⟶ Y`. |
| Commutative square | `a ≫ p = (boundary (n + 1)).ι ≫ b`. |
| Boundary first vertex is `x` | `(boundary.ι (Fin.last (n + 1)) ≫ a).app _ (stdSimplex.obj₀Equiv.symm 0) = x`. The face omitting the last vertex sends its vertex zero to the original vertex zero. |
| Filler over the specified base | `∃ c : Δ[n+1] ⟶ X, c ≫ p = b ∧ ...`. The base map is fixed, not merely homotopic. |
| Filler restricts to the whole boundary | `(boundary (n + 1)).ι ≫ c = a`, equality of simplicial maps. |
| `p`-final means all incoming maps are weak equivalences | `IsRelativeFinal p x := ∀ z, IsWeakHomotopyEquivalence (mappingSpaceMap p z x)`. |
| Finality iff the final-vertex boundary condition | The second `↔`, independent of the first, with the same square and both filler equations. Its endpoint is `(boundary.ι (0 : Fin (n + 2)) ≫ a).app _ (stdSimplex.obj₀Equiv.symm (Fin.last n)) = x`. Face zero sends vertex `n` to the original last vertex `n+1`. |
| No dimension-zero requirement | Only dimensions `n+1` appear. There is no vertex-surjectivity hypothesis or conclusion on `p`. |

Dependency interfaces read and reused:

- The sole statement dependency, `def-cbc-enhanced-diagrams-cones`, records
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`. I read its full mapping-space
  construction, `mappingSpaceMap`, realization-based
  `IsWeakHomotopyEquivalence`, and the recorded main declaration `coneCategory`
  with its docstring. The statement uses precisely those right-pinched mapping
  spaces and canonical maps; it does not replace them by ordinary Hom sets.
- Mathlib `SSet.Quasicategory` (Quasicategory/Basic.lean:39),
  `SSet.InnerFibration` (Quasicategory/InnerFibration.lean:70),
  `SSet.boundary` (SimplicialSet/Boundary.lean:37), `boundary_eq_iSup` (line 44),
  and `boundary.ι` (line 169) were read, including their signatures and docstrings.
  The last is the standard face map lifted to the boundary, as its equation
  `boundary.ι_ι` confirms.
- Stated proof dependencies are imported without `public`:
  `Sheaf.CategoryTheory.JoinSliceRightFibration` (`joinSlice_right_fibration`),
  `Sheaf.CategoryTheory.InfinityFibrations` (`rightFibration`),
  `Sheaf.AlgebraicTopology.KanFibrationFiberCriterion`
  (`kan_fibration_fiber_criterion`),
  `Sheaf.CategoryTheory.RightFibrationContractibleFibers`
  (`SSet.rightFibration_of_contractible_fibers`), and
  `Sheaf.CategoryTheory.RightPinchComparison` (`right_pinch_comparison`).
  The Mathlib leaf `def-weil-pbc-trivial-kan-fibration` is imported through
  `Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations`, whose `I.rlp`
  is the recorded boundary-lifting predicate. The unstated proof dependency
  `lem-cbc-right-fibration-space-fiber` has no module record to import; no part
  of its notion is needed to elaborate this item's statement.

Edge cases checked before the final statement:

- Dimension one (`n=0` in Lean): the last face of the interval is vertex zero,
  and the zeroth face is vertex one. Thus both endpoint tests are correct,
  including the case `Δ[0]` used to evaluate these faces.
- No zero-dimensional requirement: for `p = id_X`, all mapping maps and all
  square fillers are identities/forced, even when `X` has many components.
  An inclusion of one component into a discrete quasicategory can satisfy
  both relative conditions at its vertex without being surjective on vertices;
  the positive-dimensional encoding allows this example.
- For `Y = Δ[0]`, the conditions recover ordinary initial/final mapping-space
  contractibility and boundary extensions.
- Empty mapping spaces remain allowed; they are never assumed inhabited.
  A chosen vertex `x` excludes an empty `X` only in the intended conditional
  way: the theorem has no instantiations without such a vertex.
- One vertex can be relative initial without being relative final (the initial
  vertex of the nerve of `[1]` over a point). Therefore the theorem uses a
  conjunction of two separate equivalences, never a single equivalence with
  the conjunction of both boundary predicates.
- Universe `u` is arbitrary. Every binder is explicit and `autoImplicit false`
  is set; no size equality is added.

Actual searches for an existing statement (all run for this item):

- `msearch.py ... leanfinder "For an inner fibration of quasicategories a relative
  initial object is equivalent to filling every positive dimensional simplex
  boundary with that first vertex"`: 8 hits, including `SSet.modelCategoryQuillen.J`,
  `I`, `quasicategory_of_filler`, `Quasicategory.hornFilling`, and
  `KanComplex.hornFilling`. Their displayed types define horn fillers or the
  boundary family, not the relative mapping-space criterion.
- `msearch.py ... loogle '"SSet.InnerFibration"'`: 6 hits, the class and its
  defining property plus the internal-Hom pullback inner-fibration instance.
  I read InnerFibration.lean:29-117. None characterizes relative vertices.
- `msearch.py ... grep 'relative.?initial|initial.*boundary|boundary.*initial'
  AlgebraicTopology`: 0 hits.
- `msearch.py ... leansearch "Relative initial objects of an inner fibration of
  quasicategories are characterized by boundary lifting at the initial vertex"`:
  8 hits, all ordinary initial objects/cofibrant objects/bifibrant objects;
  none mentions mapping spaces of quasicategories or this relative criterion.
- `rg` for the same relative/boundary vocabulary in upstream `WeilConjectures`,
  project `lean/Sheaf`, and `dag/lean_names_upstream.json` found only unrelated
  homological initial pages and boundaries. A literal item-id search of upstream
  `WeilConjectures` found no occurrence. The project's
  `TerminalBoundaryExtension.lean` was read: it is the absolute final-object
  case and has no prescribed base simplex, so is not an exact match.
- Literal searches for `IsRelativeInitial`, `IsRelativeFinal`, and
  `relative_initial_final_iff_boundary_fillers` in Mathlib, upstream and
  `lean/Sheaf` found no existing declaration.

Validation: `scompile.py Q129 lem-coef-infinity-relative-initial-boundary` compiled
`RelativeInitialBoundary.lean` as both sandbox and library module, with no errors
or warnings (the expected postponed theorem is the sole `sorry`). The first draft
attempt to apply a boundary map directly to a standard-simplex vertex failed its
typecheck; the final statement uses the canonical face inclusions above.

## Second reading by Q129

I independently read the repository node, this sandbox's node and complete Lean module,
the dependency node `def-cbc-enhanced-diagrams-cones` and its recorded module, and the
Mathlib definitions used below. I also opened the recorded proof-dependency signatures.
There is no repair note for this item. The sandbox node changes only `lean`; it has no
`statement_change`, new nodes, or dependency repair modules to audit.

Source check: [Kerodon 02WS](https://kerodon.net/tag/02WS), Corollary the project server,
explicitly assumes an inner fibration of infinity categories and identifies relative
initiality with lifting the specified boundary squares for positive dimensions and a
fixed first vertex. [Kerodon 02WR](https://kerodon.net/tag/02WR), Proposition the project server,
identifies the slice comparison through the maps on its mapping-space fibers; the
final assertion is the opposite dual. These are Kerodon sources, not Stacks tags.
There is no additional finiteness, nonemptiness, field, characteristic or size hypothesis.

Object/hypothesis/conclusion checklist, in node order:

| Node object or clause | Exact Lean rendering and verdict |
| --- | --- |
| Simplicial sets X,Y | `{X Y : SSet.{u}}`, with `universe u` explicitly bound. Correct: the same small simplicial-set category as the dependency. |
| X,Y are quasicategories | `[Quasicategory X] [Quasicategory Y]`. Correct: Mathlib's class requires exactly the inner-horn extensions, without outer-horn or nonempty conditions. |
| Boundary is the union of proper faces | `∂Δ[n + 1]` is Mathlib `boundary`; its definition is the non-surjective simplices and `boundary_eq_iSup` is precisely that union. Correct; no replacement definition. |
| Inner fibration p | `(p : X ⟶ Y) [InnerFibration p]`. Correct: `innerFibrations := innerHornInclusions.rlp` and the class supplies that predicate. No Kan-fibration assumption. |
| A specified vertex x | `(x : X _⦋0⦌)`. Correct: vertex data, not an arbitrary object of the ordinary category of simplicial sets. |
| Relative initiality tests every outgoing mapping map | `IsRelativeInitial p x := ∀ z : X _⦋0⦌, IsWeakHomotopyEquivalence (mappingSpaceMap p x z)`. Correct: the dependency's actual right-pinched spaces, canonical postcomposition map, and realization weak equivalence. |
| Initiality iff filling | First `↔` in `relative_initial_final_iff_boundary_fillers`. Correct: both implications, independent of finality. |
| Every n>0, every boundary a, every base simplex b | `∀ (n : ℕ) (a : (∂Δ[n + 1] : SSet.{u}) ⟶ X) (b : (Δ[n + 1] : SSet.{u}) ⟶ Y)`. Correct: dimension n+1 ranges over all and only positive dimensions; a and b precede the square and endpoint hypotheses. |
| Square commutes | `a ≫ p = (boundary (n + 1)).ι ≫ b →`. Correct: equality on the whole boundary. |
| First boundary vertex is x | `(boundary.ι (Fin.last (n + 1)) ≫ a).app _ (stdSimplex.obj₀Equiv.symm 0) = x →`. Correct: `boundary.ι_ι` identifies this face with δ_(n+1), which sends vertex zero to zero. |
| A filler for that same b | `∃ c : (Δ[n + 1] : SSet.{u}) ⟶ X, c ≫ p = b ∧ ...`. Correct: a genuine simplex map with exact projection, not a homotopy or an unspecified base map. |
| It extends that same a | `(boundary (n + 1)).ι ≫ c = a`. Correct: exact restriction to the entire boundary. |
| Relative finality tests every incoming map | `IsRelativeFinal p x := ∀ z : X _⦋0⦌, IsWeakHomotopyEquivalence (mappingSpaceMap p z x)`. Correct: same spaces and weak-equivalence notion, with reversed arguments. |
| Finality iff last-vertex boundary filling | Second `↔`, with the same dimension, maps, square and two filler equations. Correct: `(boundary.ι (0 : Fin (n + 2)) ≫ a).app _ (stdSimplex.obj₀Equiv.symm (Fin.last n)) = x` evaluates δ_0 at vertex n, yielding original vertex n+1. |
| Both characterizations, no relation imposed between them | The conclusion joins the two equivalences with `∧`. Correct; it does not assert equivalence of initiality and finality. |
| No dimension-zero requirement | Only dimensions `n+1` occur in either clause. Correct: p is never required to be surjective on vertices. |

I read `mappingSpace` and `mappingSpaceMap` in EnhancedDiagramsCones.lean, not only
the recorded main declaration `coneCategory`. Its degree-n data are simplices of
dimension n+1 with constant initial face and prescribed final vertex; its operators
append the new final vertex. `mappingSpaceMap` is postcomposition by p in every
degree. `IsWeakHomotopyEquivalence` tests path components and every positive based
homotopy group of geometric realization. Thus neither the objects nor the canonical
maps have changed meaning through a superficially similar dependency name.
The relative predicates are real Prop definitions of the notions explicitly introduced
in this node; both are listed in `lean.declarations`. No independent notion or missing
statement prerequisite needs a new node.

I checked the imported proof interfaces: `joinSlice_right_fibration` includes the
explicit strict-fiber identification with these mapping spaces;
`rightFibration` is right-horn lifting; `kan_fibration_fiber_criterion` uses the same
weak-equivalence predicate; `SSet.rightFibration_of_contractible_fibers` concludes
`modelCategoryQuillen.I.rlp`; `right_pinch_comparison` specifies its canonical map by
the prism formula, including naturality and actual homotopy inverses. Mathlib's `I`
is exactly the family of all boundary inclusions. The one proof dependency without
a declaration, `lem-cbc-right-fibration-space-fiber`, is not a statement dependency
and introduces no missing object into this signature, so there is no module to import.

Edge cases: Lean n=0 is geometric dimension one. The initial test uses δ_1 of
Δ[1] at the sole vertex of Δ[0], and the final test uses δ_0, so they select the two
correct endpoints even in this smallest case. Geometric dimension zero is absent.
For p=id, the chosen b is already a filler whenever the square commutes. An inclusion
of one component of a discrete quasicategory satisfies both relative conditions at
its vertex without surjectivity on all base vertices, as required. Empty mapping
spaces are permitted, and a map between empty mapping spaces can be a weak equivalence.
An empty X simply has no x at which to instantiate the theorem; no global Nonempty
instance was added. Over Δ[0], this recovers the ordinary initial/final conditions.
For the nerve of [1] over a point, its first vertex is initial but not final,
confirming that the two equivalences must remain separate. Ring characteristic,
zero modules, schemes and index sets do not enter this statement. The universe u is
arbitrary and no additional universe equation or unbound variable appears.

Independent searches, using different terminology as well as the declaration names:

- `msearch.py Q129 lem-coef-infinity-relative-initial-boundary leanfinder` with
  "A vertex is initial over a simplicial map when all maps from it on mapping
  spaces are weak equivalences, characterized by extending boundaries over a fixed
  base simplex": 8 hits. I read their displayed types. `I`, `J` and
  `boundary_ι_mem_I` give boundary/horn families only; `Subcomplex.isInitialBot`
  and truncated-simplex initiality concern ordinary category theory;
  `RelativeMorphism.ofSimplex₀` constructs a relative vertex. None is this theorem.
- Loogle query `"SSet", "HasLiftingProperty", "boundary"`: 0 hits.
- LeanSearch query "Relative terminal vertex of an inner fibration and extending
  boundaries with prescribed last vertex": 8 hits. Returned types concern fibrant
  objects, terminal objects, ordinary cocones, or the all-horn fibration instance;
  none characterizes a relative vertex.
- msearch grep query `under.?category|over.?category|cofinal|coinitial`, restricted
  to AlgebraicTopology/Quasicategory: 0 hits.
- Direct `rg` across Mathlib AlgebraicTopology, upstream WeilConjectures, project
  lean/Sheaf and `dag/lean_names_upstream.json` for relative initial/final names
  and initial/final/terminal boundary vocabulary found no existing declaration
  of this item. Additional CategoryTheory searches found only unrelated relative
  limit/colimit presentations. I opened `TerminalBoundaryExtension.lean`: it is
  absolute terminality, without p or a prescribed b. I also opened
  `CartesianInitialBoundaryLift.lean`: it is a fiberwise cartesian application
  with extra data and hypotheses, not this equivalence. Its `boundarySource`
  helper does not duplicate either relative predicate in this delivery.

H5/H6/H8/H9 checks: the only postponed proof is this node's named theorem, with
`by sorry`; both definitions contain complete data and no new theorem is proved.
The source and blueprint tags occur on the module and all three declarations.
The theorem's docstring carries all six node proof steps, including the m=0 slice
case, both exact equations and the opposite/pinch comparison. The module obeys
100-column lines and has no local notation, private API, extra instance, or
unbound variable. `lean.statement` is verbatim equal to the theorem signature.

Mismatches found: none. I preserved the correct Lean and node record and added
this independent reading only. Validation results are recorded below.

Second-reader validation: `scompile.py Q129 lem-coef-infinity-relative-initial-boundary` compiled the delivered `RelativeInitialBoundary.lean` as both sandbox and library module cleanly (1.2 seconds each), with no diagnostics. A direct signature comparison confirmed the node record is verbatim, and every Lean line is at most 100 characters.
