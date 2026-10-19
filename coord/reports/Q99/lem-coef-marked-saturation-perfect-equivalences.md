## Worker report

`Sheaf.AlgebraicTopology.MarkedSaturationPerfectEquivalences` states
`SSet.Marked.marked_saturation_perfect_equivalences`; its only proof is `sorry`.
It introduces no definitions. The statement of the DAG node is unchanged.

The node's hypotheses and conclusions are rendered as follows:

- The input universe is `u`; `v` is the additional testing-universe level. Both are explicitly
  declared, and `autoImplicit` is disabled. `Marked.{u}` is the recorded category of small marked
  simplicial sets, whose maps preserve marked edges. The size-convention dependency is recorded
  as metatheoretic (`convention: true`), so it supplies no declaration to import.
- The class called `W` is exactly the existing `SSet.Marked.weak`: for every `C : SSet.{u}`,
  `Quasicategory C` implies `Enhanced.IsWeakHomotopyEquivalence
  (mapSharpPre f (natural C))`. The underlying weak homotopy equivalence uses realization,
  bijection on path components, and bijections on every positive based homotopy group.
- `∃ (T : Marked.{u} ⥤ Marked.{u}) (η : 𝟭 Marked.{u} ⟶ T)` supplies the replacement functor and
  one natural transformation. Functoriality and naturality are part of these types.
- For every `X`, `∃ Q : SSet.{u}, Quasicategory Q ∧ T.obj X = natural Q` is precisely
  `T(X) = Q_X^natural`, with no chosen quasicategory or nonemptiness hypothesis on the input.
- `transfiniteCompositions.{u} finiteMarkedGenerators.pushouts (η.app X)` expresses actual
  successive finite attachments in the input universe. Mathlib's transfinite composition includes
  the continuous tower and its colimit cocone; each successor map is a pushout of a generator.
  Q02's `finiteMarkedGenerators` consists of (i), (ii), (iii), and `flatToMarked
  markedEquivalenceDetector`, with no family (iv). Coproduct attachments in the node's proof can
  be serialized by well-ordering their input-universe set of summands. The expression does not
  allow retracts of such towers.
- `PreservesFilteredColimits T` is the preservation clause. The abbreviation fixes both shape
  universes to the hom universe `u` of `Marked.{u}`.
- `∀ X, weak (η.app X)` is the mapping-test clause for all units.
- For arbitrary `f : X ⟶ Y`, `weak f ↔ ∃ QX QY, ...` names quasicategories and identifies the two
  replacement objects with their natural markings, then asserts `Enhanced.IsFunctorEquivalence
  (T.map f).val`. The `.val` is the underlying simplicial functor. The recorded equivalence
  predicate supplies a simplicial inverse and equivalence edges from both composites to the
  identities in the corresponding internal functor simplicial sets.
- `isomorphisms Marked.{u} ≤ weak` includes every isomorphism. Three separate universally
  quantified implications give each of the three two-out-of-three cases for arbitrary composable
  `f` and `g`.
- `IsStableUnderFilteredColimits.{u, u} weak` is closure under small filtered colimits of arrows.
  Mathlib states this via colimit source and target cocones and the induced commuting arrow;
  colimits in `Arrow` are computed by these two cocones.
- `∃ G : MorphismProperty Marked.{u}, G.IsSmall.{u} ∧ G ≤ weak ∧ ...` gives an input-universe
  small set of generating arrows, all belonging to `W`. For every `weak f`, the witnesses
  `J : Type u`, `SmallCategory J`, `IsFiltered J`, `F : J ⥤ Arrow Marked.{u}`, and `c : Cocone F`
  give its small filtered diagram; `∀ j, G (F.obj j).hom` restricts every diagram object to the
  generating set; `Nonempty (IsColimit c)` is its universal property; and
  `Nonempty (c.pt ≅ Arrow.mk f)` identifies the colimit with the requested arrow.
- Finally every `X` and every `C : SSet.{max u v}` satisfying `Quasicategory C` obey the same
  realization-based mapping test for `mapSharpPre (enlargeMap.{u, v} (η.app X)) (natural C)`.
  `enlargeMap` applies degreewise `ULift` to the underlying simplicial map and transports the
  existing marking, so this tests the same unit in every larger testing universe.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.IsFunctorEquivalence`,
  `AreNaturallyEquivalent`, `IsEquivalenceEdge`, and `IsWeakHomotopyEquivalence`. I also read
  the dependency's recorded `coneCategory` declaration and docstring.
- `Sheaf.AlgebraicTopology.MarkedAnodyneLiftingCalculus`: the recorded
  `marked_anodyne_lifting_calculus`, and the definitions `flatToMarked`, `finalMarkedHorn`,
  `triangleMarkingMap`, `markedEquivalenceDetector`, and `markedSaturation`. Its imported
  `Sheaf.AlgebraicTopology.MarkedPointCartesianModel` supplies `SSet.Marked`, `natural`, `weak`,
  `mapSharpPre`, and `enlargeMap`; their full definitions and docstrings were inspected.
- `Sheaf.AlgebraicTopology.FiniteMarkedFibrancyCriterion`: `finiteMarkedGenerators` and the
  recorded `finite_marked_fibrancy_criterion`. This existing, landed node is added to `stmt_deps`
  so the theorem uses the unique finite generator family rather than a private duplicate.
- Mathlib `MorphismProperty.transfiniteCompositions`, `MorphismProperty.pushouts`,
  `MorphismProperty.IsSmall`, `MorphismProperty.IsStableUnderFilteredColimits`,
  `Limits.PreservesFilteredColimits`, `Arrow`, `Cocone`, and `IsColimit` supply the existing
  attachment, size, and colimit interfaces. Their size binders were checked in source.

The available proof dependencies are imported without `public`: `KanQuillenRightProper`,
`JoyalQuasicategoryCharacterizations`, `CategoricalEquivalencesSmallGeneration`, and
`AccessibleArrowInverseImage`. The other stated proof dependencies are already public imports.
`lem-coef-joyal-filtered-equivalences` has no Lean record in the current DAG, so there is no module
for that proof-only dependency to import. The module's docstring carries all seven DAG proof steps,
including that future input. No missing notion is needed to type the statement.

Edge cases checked: an empty marked simplicial set is allowed, as are empty testing
quasicategories. No inhabitedness assumption is imposed on either. A filtered indexing category is
nonempty by `IsFiltered`, as required by the node's filtered-colimit convention; an empty diagram
is not incorrectly allowed as a filtered presentation. Inner horns have `0 < i < n`, so no spurious
zero- or one-dimensional inner horns occur. `finalMarkedHorn 0` is the final one-dimensional horn;
the triangle and finite detector keep their prescribed markings and all degenerate edges. Identity
maps are allowed as transfinite compositions of shape `Fin 1`, covering a construction needing no
attachments. The small generating family need not have finite endpoints. Every map and every pair
of composable maps is quantified without a monomorphism or fibrancy restriction. `v = 0` includes
testing in the input universe, and arbitrary `v` gives all enlargements. No additional universe
parameter is left for small generation or filtered closure.

Searches rerun in this worker session:

- `msearch.py`, LeanFinder, `Finite marked simplicial saturation detects equivalences and is a
  perfect class`: eight hits, including `SSet.Finite.instIsFinitelyPresentable` and generic
  simplicial-set declarations; none states this marked replacement/perfectness theorem.
- `msearch.py`, Loogle, `"Marked", "PreservesFilteredColimits"`: zero hits.
- `msearch.py`, grep, `marked.*saturat|IsPerfect|perfect.*class`, Mathlib `AlgebraicTopology`:
  zero hits.
- `rg` for the theorem name, finite generator name, and node identifier over Mathlib,
  `WeilConjectures/`, `dag/lean_names_upstream.json`, and project `lean/Sheaf`: no existing theorem;
  the unique `finiteMarkedGenerators` is Q02's declaration. The marked-model module mentions the
  item as a proof input but does not state this theorem. Concept searches for marked saturation
  and perfect equivalences found the existing calculus and unrelated perfect-complex material.

Source checked online: [Lurie, Higher Topos Theory](https://www.math.ias.edu/~lurie/papers/HTT.pdf),
Proposition the project server proof (1), Proposition the project server over a point, Definition A.2.6.12, and
Corollary A.2.6.14. The source supplies the attachment construction and the detector; the explicit
seven-step DAG proof elaborates its point case and size claims. No source or node statement
correction is needed, and no `STATEMENT-DISPUTED` issue remains.

Repairs to the inherited attempt: replaced saturation (which permitted retracts) by actual
transfinite pushout attachments; fixed `G.IsSmall.{u}` and filtered-closure universes explicitly;
added the available proof imports and all seven proof steps; refreshed the node from the current
repository so no protected `lean_audit` field changes; corrected the report's obsolete private
finite-generator name and its statement about filtered-category nonemptiness. The prior second
reading concerned an earlier signature and was removed; the independent second reader will read
the final result. There are no new nodes or dependency modules in this delivery.

Validation: the final module passed `scompile.py` with no errors or warnings. Only this module and
the item node are delivered, with the node changed solely in `lean` and the added landed dependency.

## Second reading by Q99

I reread the item node, its source places, the copied node record, and
`Sheaf.AlgebraicTopology.MarkedSaturationPerfectEquivalences.lean` independently.
The objects and hypotheses match as follows. The universe `u` is the universe of
`SSet.Marked.{u}` and `v` is the independent enlargement level. The marked category,
mapping object, natural marking, enlargement map, and class `W` are the recorded
declarations from `MarkedPointCartesianModel`: `weak f` unfolds to
`Enhanced.IsWeakHomotopyEquivalence (mapSharpPre f (natural C))` for every
`C : SSet.{u}` with `Quasicategory C`. The existential functor and unit are
`T : Marked.{u} ⥤ Marked.{u}` and `η : 𝟭 Marked.{u} ⟶ T`, so functoriality and
naturality are included by their types.

The first conclusion clause is rendered by
`∀ X, transfiniteCompositions.{u} finiteMarkedGenerators.pushouts (η.app X) ∧
∃ Q : SSet.{u}, Quasicategory Q ∧ T.obj X = natural Q`. This is the source's
successive pushout attachment construction and the natural-marked quasicategory
replacement. `finiteMarkedGenerators` is the recorded declaration from
`FiniteMarkedFibrancyCriterion`, now correctly included in `stmt_deps`; it contains
exactly the three finite families and the finite equivalence detector specified by the
node. The following clauses render `PreservesFilteredColimits T`, `∀ X, weak (η.app X)`,
and, for every `f : X ⟶ Y`, the equivalence between `weak f` and the existence of
quasicategories `QX,QY` with the displayed replacement equalities and
`Enhanced.IsFunctorEquivalence (T.map f).val`. The equalities identify that underlying
map with the source's map `QX → QY`.

The remaining perfectness clauses match one-for-one: `isomorphisms Marked.{u} ≤ weak`,
the three implications for composable `f,g` (the three two-out-of-three directions),
`IsStableUnderFilteredColimits.{u,u} weak`, and the existential small generating
property. In the last property, `G.IsSmall.{u} ∧ G ≤ weak` gives the small subset of
`W`; the `J : Type u`, `SmallCategory`, `IsFiltered`, cocone, objectwise `G`, colimit,
and arrow-isomorphism witnesses are exactly the filtered presentation in the node.
The final universal clause is the larger-universe mapping test, using
`C : SSet.{max u v}` and `enlargeMap.{u,v}`. No hypothesis is added, dropped, or
strengthened, and quantifier order is unchanged.

Source check: the construction and filtered-colimit functor are in HTT Proposition
the project server(1) (PDF pp. 158--159, lines 9283--9299), the pointwise equivalence detection
is Proposition the project server, and perfectness is Definition A.2.6.12 and Corollary A.2.6.14
(PDF p. 842, lines 52459--52481). These source clauses agree with the node's seven
proof steps and the Lean rendering.

Edge cases were checked directly: empty marked simplicial sets and empty
quasicategories are permitted; no input inhabitedness is assumed; `v = 0` gives the
input-universe test; arbitrary `v` gives every larger testing universe; `n = 0` and
`n = 1` introduce no invalid inner horns, while the final marked horn and detector
retain their prescribed markings; identity maps are allowed by the transfinite
composition predicate; filtered indexing is correctly nonempty through `IsFiltered`;
the small generating family may be empty only when the stated generation clause is
satisfied. No characteristic, Noetherian, finiteness, or universe-equality hypothesis
appears.

Searches were rerun with `msearch.py` (LeanFinder and LeanSearch queries for finite
marked saturation/perfect equivalences), Loogle (quoted marked-equivalence and
filtered-colimit names), and `rg` over Mathlib, `WeilConjectures/`, `lean/Sheaf/`, and
`dag/lean_names_upstream.json`. Hits were generic simplicial finite-presentability,
accessibility, or unrelated perfect-complex declarations; no existing theorem or
duplicate notion was found. The source checkout likewise has no declaration.

The only inherited record mismatch was that the Lean statement names
`finiteMarkedGenerators` while the old base node omitted its definition node from
`stmt_deps`; the sandbox node adds the landed
`lem-coef-finite-marked-fibrancy-criterion` dependency. No Lean signature or source
statement change was needed. Compilation with `scompile.py` is clean (no errors and no
warnings), and the module contains only the named theorem with its permitted `sorry`.
