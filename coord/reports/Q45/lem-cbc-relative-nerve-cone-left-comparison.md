## Worker report

Item: `lem-cbc-relative-nerve-cone-left-comparison`, group Q45, 2026-10-17.
Module: `Sheaf.AlgebraicTopology.MarkedRelativeNerveConeComparison`.
Main declaration:
`SSet.MarkedRelativeNerveCone.marked_relative_nerve_cone_left_comparison`.

The theorem states `Nonempty Statement.{u}`. Its witnesses are the established,
fully normalized unmarked comparison and point-cone calculation, their marked lift,
and its explicit point normalization. This is an unconditional existence theorem;
no unmarked-comparison, model-structure, fibrancy, cofibrancy, or Kan hypothesis is
added to the caller. All constructions and equalities can be projected from its
witness. No definition chooses data from this theorem or any existence theorem.
The main theorem is the only postponed theorem in the module, with proof `sorry`.
Its docstring contains all ten proof steps from the node.

The node's statement, proof, proof dependencies, status and source are unchanged.
Its statement dependencies gain two already landed nodes:
`lem-coef-unmarked-relative-nerve-cone-comparison`, to reuse its normalized
underlying comparison rather than duplicate its cone/comma construction, and
`lem-coef-marked-cone-generator-calculations`, to name its actual normalized
point augmentation. These are recorded declarations on `newtargets-dag`; neither
node is delivered or modified. No new node or dependency repair module is needed.

### Hypotheses and clauses

- Nested universes and small ordinary categories: the module declares `universe u`
  explicitly and quantifies over `C : Cat.{u,u}`. Its diagrams take values in
  `Marked.{u}`; the collection of all such diagrams inhabits larger universes
  automatically. This allows every small category by enlarging `u`, with no
  equality between independent site universes imposed. No auto-bound variables
  or universes are used (`set_option autoImplicit false`).
- The marked simplicial set `p : X -> N(C)` is exactly
  `X : Marked.Over (nerve C)`, the recorded slice over the sharply marked nerve.
  There is no restriction on the total simplicial set or its marking beyond
  containing degeneracies. All fields quantify over every such `X`.
- The strict diagram `L_C` is `Diagrams.L`, an ordinary functor from this slice
  to `C ⥤ Marked`. `L_objects` identifies it with `sliceValue`.
- The pairs `(x,g : p(x_last) -> c)` and their simplicial operators are the
  existing unmarked `A.F` values used as `sliceValue.underlying`. The recorded
  `RelativeNerveCone.Diagrams.F_objects`, `fst_eq` and `snd_eq` identify these
  with the actual `pullback X.hom (nerveMap (Over.forget c))`; this is precisely
  `X ×_{N(C)} N(C/c)`, the equivalent description expressly allowed by the node.
  A simplex in `N(C/c)` over `p(x)` is a commuting triangle at every vertex, so
  its final arrow determines all the others. Restricting to the final vertex
  `theta(s)` changes the label to `g ∘ p(x_theta(s) -> x_r)`. Thus neither the
  last face nor a degeneracy is replaced by a label-preserving operator.
- An `L_C` edge is marked exactly when its `X` projection is marked:
  `sliceValue.marking := {e | (A.fst ... c).app _ e ∈ X.left.marking}`.
  `sliceValue.degenerate` uses projection naturality and the given degeneracy
  marking of `X`, with real proof data and no postponed definition obligation.
- Postcomposition of the label is enforced by `L_actions`, which fixes the
  underlying map to `A.F`'s action. The latter has the two projection equations
  `F_action_fst` and `F_action_snd`, the second using `nerveMap (Over.map f)`.
  `L_maps` likewise fixes maps induced by slice maps, retaining the label.
- The counit `epsilon_C` is the existing `A.counit` from the unmarked package.
  Its `counit_objects` and `counit_arrows` specify every simplex of the
  coherent-realization counit into `oppositeCategory (discreteCategory C)`.
  This is the same coherent realization and discrete coefficient category as
  in the straightening dependency, not an abstract substitute base map.
- The formula for `T_C` is `Diagrams.T` with `T_objects = coneValue`.
  `coneValue` applies `MarkedCone.markedValue (discreteCategory C) A.counit`
  to `Marked.Over.opposite.obj X`, then applies `oppositeValue` to its value.
  Thus both the input opposite and the final valuewise opposite are present.
  The marked cone value is exactly the recorded cone-pushout construction.
- The marked opposite uses the existing `Marked.Over.opposite`, extracted at
  a point by `oppositeValue`, and the same functor on maps by
  `oppositeValueMap`. It reverses simplex operators and transports each marked
  edge, as the dependency specifies. `doubleOppositeIso` is the canonical
  simplicial double-opposite isomorphism with that same marking.
- The strict action and the input maps of `T_C` are fixed by `T_actions` and
  `T_maps` to `opFunctor.map` of the existing unmarked cone action and maps.
  They cannot be arbitrary maps between the correct objectwise values.
- The transformation `a_C` is `Diagrams.comparison : T ⟶ L`. Its type includes
  naturality both in the input `X` and in the coefficient object `c`.
  `comparison_underlying` fixes its underlying map to the existing normalized
  `A.alpha`, followed by the final opposite and canonical double-opposite
  removal. Consequently this is the subset-maximum cone comparison itself,
  rather than an unspecified natural weak equivalence. The unmarked witness
  is the full `RelativeNerveCone.ComparisonStatement`, including its normalized
  subset-cube quotient, minimum map in reversed coordinates, all base changes
  and colimit extension.
- Every component is an absolute marked-model weak equivalence:
  `Diagrams.weak : ∀ X c, Marked.weak ((comparison.app X).app c)`.
  This uses the recorded sharp-mapping test definition for the absolute model;
  it is not merely a weak homotopy equivalence or a relative equivalence.
- For `u : C ⥤ D`, `N(u)_!` is precisely
  `Marked.Over.push (nerveMap u)`, the recorded base-postcomposition functor.
  `TargetChange.T_unit` and `L_unit` are the canonical units into the diagrams
  after this base change. Their underlying maps are fixed by
  `T_unit_underlying` and `L_unit_underlying` to the unmarked cone-pushout and
  comma-projection units, respectively. Thus these encode the stipulated
  canonical identifications, not arbitrarily chosen Kan extension units.
- The ordinary left Kan extension requirement is `TargetChange.T_kan` and
  `L_kan`, each using Mathlib's `Functor.IsLeftKanExtension` for the displayed
  unit. Its universal object is initial in `Functor.LeftExtension`; equivalently,
  maps out correspond bijectively to `Nat(H, u ⋙ G)`. This gives exactly the
  two displayed `u_!` isomorphisms, without selecting a global Kan functor.
- Agreement of `u_!a_C` with `a_D` is `TargetChange.comparison_square`, the
  equality after precomposing the two canonical Kan units. Kan universality
  makes this equivalent to the equality under those isomorphisms.
  `T_natural` and `L_natural` also state naturality of these units in `X`.
- Identities and composites are `ComparisonStatement.T_identity`, `L_identity`,
  `T_composite` and `L_composite`. They fix the universal units, so also fix
  the induced comparison isomorphisms and their compatibility with the square.
  Heterogeneous equality is used only for objects related by functor laws,
  base-map composition, or canonical endpoint transports.
- The terminal category is represented by `RelativeNerveCone.ordinal 0`, whose
  single object is `ULift.up (0 : Fin 1)`. `pointInput` gives the constant base
  map for every marked input. `Statement.point` is a `PointNormalization`.
  Its `baseIso` identifies the terminal discrete enriched index with the
  realized point, and `coneIso` identifies the actual two cone pushouts.
  `cone_leg` and `base_leg` fix that isomorphism on both pushout legs.
  `source_formula` fixes `sourceIso` to its hom map followed by opposite;
  `target_formula` fixes `targetIso : L_*(X) ≅ X` to the comma projection.
  Finally `PointNormalization.comparison` equates the component of `a_*`,
  after these identifications, with
  `oppositeValueMap (K.augmentation (oppositeValue X))` followed by
  `doubleOppositeIso X`. Here `K` is the existing `MarkedCone.PointCalculation`,
  whose augmentation is specified by the quotient-cube maximum and every
  coend summand. This explicitly renders the point normalization from the node.

### Dependency declarations read and reused

- `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`:
  `SSet.Marked`, `Marked.Hom`, the marked category, and `Marked.weak`;
  read `CartesianModelStatement` and `marked_point_cartesian_model`, including
  their docstrings and full theorem signature. The absolute weak predicate is
  the interface used directly; no new model structure is introduced.
- `Sheaf.CategoryTheory.MarkedRelativeCartesianModel`:
  `SSet.Marked.Over`, `Over.push`, `Over.opposite`, `Over.oppositeObject`;
  read the full `marked_relative_cartesian_model` signature and the relevant
  slice/opposite definitions and docstrings.
- `Sheaf.CategoryTheory.SimplicialProjectiveModelCalculus`:
  read `SimplicialDiagramEnrichment`, `ProjectiveSimplicialModelStructure`,
  `SimplicialQuillenEquivalence`, and the full
  `simplicial_projective_model_calculus` signature and proof docstring.
  The proof uses its projective model/left Kan calculus, while the statement
  uses ordinary strict diagrams for discrete ordinary indices.
- `Sheaf.CategoryTheory.CoherentNerveComparison` and its infrastructure:
  read `CoherentNerveComparisonStatement`, the discrete-nerve normalization,
  `SCat`, and `coherent_nerve_comparison`. The canonical counit is reused via
  the normalized unmarked package, using the same coherent realization.
- `Sheaf.CategoryTheory.MarkedConeStraighteningQuillen`:
  read `cone`, `ConeAdjunction`, `BaseChange`, `IndexChange`, `Statement`,
  `toPointSlice`, and `marked_cone_straightening_quillen`, with their full
  signatures/docstrings. The marked cone value is the dependency's existing
  `MarkedCone.markedValue`; its definition and markings were also read in
  `Sheaf.AlgebraicTopology.MarkedConeExternalProduct`.
- Added landed dependency
  `Sheaf.AlgebraicTopology.UnmarkedRelativeNerveConeComparison`:
  read the node and the complete module, in particular `RelativeNerveCone.Diagrams`,
  `TargetChange`, `SimplexNormalization`, `ComparisonStatement`, and
  `unmarked_relative_nerve_cone_comparison`. These specify the actual counit,
  pullbacks, actions, maps, subset-flag comparison and canonical Kan units.
- Added landed dependency
  `Sheaf.AlgebraicTopology.MarkedConeGeneratorCalculations`:
  read its node, `PointCubeComparison`, `pointCubeMap`, `PointCalculation`,
  and `marked_cone_generator_calculations`. Its augmentation is retained with
  the existing underlying `Straightening.markedPoint` construction from
  `Sheaf.AlgebraicTopology.MappingSimplexConeFibers`.
- Mathlib's `Functor.IsLeftKanExtension` and its universal-unit definition
  were read in `Mathlib.CategoryTheory.Functor.KanExtension.Basic`.
  `SSet.opFunctorCompOpFunctorIso` was read in
  `Mathlib.AlgebraicTopology.SimplicialSet.Op`.
- All recorded statement dependencies are public imports. All recorded proof
  dependencies with modules are imported, together with the two Mathlib
  proof-dependency modules for boundary cells and small-object factorization.

### Edge cases checked

- Empty `C`: the functor categories and all natural transformations are still
  defined; objectwise requirements have no object to test, and no `Nonempty C`
  or selected coefficient object is assumed.
- Empty total `X`: both cone/comma diagrams have empty values, and no simplex,
  final vertex or label is chosen by any definition in this delivery.
- Dimension zero: the comma diagram uses the only vertex as last vertex, with
  arbitrary labels; the existing counit and simplex normalization include zero.
- The last face: commuting triangles in the slice precompose the label by the
  final base edge, including when that edge is an identity. Repeated vertices
  and degeneracies use the same nerve operators, not a separate approximation.
- Dimension one, both minimal and sharp marking: the only marking condition in
  the comma value is the input edge's marking. The cone marking is the existing
  coning-edge marking; opposite transports it exactly. Empty label sets are allowed.
- The terminal category: both legs of the actual cone-pushout isomorphism and
  both source/target identifications are fixed, and the comparison is equated
  with the existing normalized augmentation, retaining both opposites.
- Change of category is unrestricted: it may be nonfaithful, nonfull, or
  identify objects. The units and Kan properties make no injectivity, equivalence,
  fibrancy or projective-cofibrancy assumption on it or the input.
- Identity and composite changes retain arbitrary marked inputs; no case is
  silently removed by a selected Kan extension or a chosen replacement.

### Searches and source check

All searches used the prescribed `msearch.py Q45 <item>` wrapper where applicable.

- LeanFinder: `marked simplicial set cone straightening comparison slice pullback
  relative nerve ordinary category`: eight hits on strict Segal/coskeletal,
  nerve-adjunction and Cech-nerve declarations, none this marked comparison.
- Loogle: `SSet, CategoryTheory.nerve, CategoryTheory.Over`: zero hits.
- Mathlib grep: `straightening|[Rr]elative[Nn]erve` in `CategoryTheory`: zero hits.
- LeanSearch: `marked straightening relative nerve cone slice pullback comparison`:
  eight hits on ordinary pullback comparisons/Cech nerves, no marked comparison.
- `rg` on the named upstream `WeilConjectures` and project `lean/Sheaf` trees
  for relative nerve, slice diagram and cone left comparison found the existing
  `UnmarkedRelativeNerveConeComparison` module. It provides the unmarked half,
  not the marked weak equivalence asserted by this item; it is reused rather
  than copied. The exact item-id grep in upstream found no declaration.
- Exact proposed namespace/declaration/module-name searches in upstream,
  `lean/Sheaf`, and `dag/lean_names_upstream.json` found no existing match.
- Read HTT online at `https://www.math.ias.edu/~lurie/papers/HTT.pdf`, checking
  Remarks the project server and the project server and Lemma the project server(2). The marked result is the
  natural lift of the unmarked comparison, and its component equivalences use
  the absolute marked model. The point normalization is the one already
  formalized in the generator-calculation dependency. No source-based correction
  to the item's statement was needed, and no statement dispute was found.

### Validation

The module compiled cleanly through `scompile.py` after the core construction and
again after the explicit point normalization; both the sandbox and library-path
checks passed. No warnings were printed. The main theorem is intentionally `sorry`
for stage 2. A final prescribed `deliver2.py --no-push` dry run is run before the
READY handoff. No global build or direct git command was run, and all worker
writes are confined to the item sandbox.

## Second reading by Q45

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
