## Worker report

Repair of the stage-2 return on immutable head `9c301e145c77`, points A–D.
The module is `Sheaf.CategoryTheory.TrivialFibrationFractionModel`; its only postponed
statement is `CategoryTheory.TrivialFibrationFractions.trivial_fibration_fraction_model`.
All other declarations construct the fraction category or specify its comparison properties.
The one theorem has a `sorry` proof; no definition contains `sorry`.

The saved packet and report were inspected first and the prescribed initial dry run was
started. Self-check found that the saved module still had every hammock defect named in
return A. That check was not a semantic pass. Its preflight eventually reported stale
`lean.declarations` and `lean.statement` while the repair was being made. Those records
are regenerated from the repaired file for the final dry run. The sandbox node's
non-Lean fields initially matched the current shared node. The repaired node retains
current base fields, with only `lean` and the two authorized landed `stmt_deps` additions.

### Return repairs

A: The conclusion now existentially quantifies `L : SSet` and
`q : FiniteReedy.largeNerve C ⟶ L`. It uses the exact landed `IsLocalization`,
`object`, `EquivalentObjects` and `Composes` declarations. It existentially supplies
maps `c x y` directly from enlarged fraction nerves into the right-pinched mapping
spaces, and asserts that these maps are weak homotopy equivalences. The entire
hammock import and the helpers `middleColumn`, `fractionPath`, `FractionComparison`
and `FractionNaturality` are removed. There are no enriched hammock, locally Kan
replacement, reduction, or hammock universality conditions. The docstring now follows
all seven steps of the current node's horn-completion/local-comma proof.

B: `lem-coef-infinity-pinch-comparison` is added to `stmt_deps` for the exact
`arrowMappingSpace`, `arrowMappingSpaceInclusion` and `rightPinchPrism` declarations.
The existing landed `def-coef-coherent-localization-interface` is also added for
`FiniteReedy`'s localization definitions, as return A asks. These additions are
allowed by brief-stage2 §5 (STMT_DEPS MAY GAIN LANDED NODES). No edge to
`lem-coef-hammock-infinity-localization` is added. No node statement is corrected.

C: Both stated proof dependencies are now non-public imports:
`Sheaf.CategoryTheory.EnhancedFunctorConeCalculus` and
`Sheaf.CategoryTheory.NerveNaturalHomotopyEquivalence`. The inner pushout-product
Mathlib match is also a non-public proof import. Proof-only nodes with no recorded
Lean declaration on the current shared base remain named in the seven-step proof
plan: horn-completion-point-colimit, edge-inverting-anodyne-extension,
localization-homotopy-category and terminal-local-kan-corepresentability.

D: `mapFractions`, `mapTotalFractions` and `LocalizationNaturality` have source
`C : Type u`, `[Category.{v} C]` and target `D : Type w`, `[Category.{z} D]`.
The theorem quantifies the target category at those independent universes. All
simplicial sets in a naturality square use the containing universe `max u v w z t`.
The degreewise lift parameter is also that containing universe, so no hidden
identity between different ULift constructions or equality of category universes
is imposed. `largeNerveMap` applies the ordinary functor to the actual simplex and
then lifts it. It is a real, degreewise natural map, not a chosen comparison.

### Each hypothesis

- Small ordinary category: `C : Type u`, `[Category.{v} C]`. It is small in a
  containing universe; object and arrow universes are independent.
- All isomorphisms are in `W`: `hWiso : MorphismProperty.isomorphisms C ≤ W`.
- Two-out-of-three for `W`: `[W.HasTwoOutOfThreeProperty]`, whose actual Mathlib
  signature includes composition and both cancellation directions. The previous
  redundant `[W.IsMultiplicative]` API binder is removed.
- `T ⊆ W`: `hTW : T ≤ W`.
- All isomorphisms are in `T`: `hTiso : MorphismProperty.isomorphisms C ≤ T`.
- Composition closure of `T`: `[T.IsMultiplicative]`. Its identity condition
  follows from the explicit inclusion of isomorphisms and adds no mathematical case.
- Pullbacks of each `T`-arrow along every arrow exist: `[T.HasPullbacks]`, the
  relative Mathlib class, not `[HasPullbacks C]`.
- The resulting projection is in `T`: `[T.IsStableUnderBaseChange]`.
- The split data for each `w : a ⟶ b` in `W`: `hsplit` existentially gives exactly
  `z`, `s : a ⟶ z`, `p : z ⟶ a`, `r : z ⟶ b`, and the four conjuncts
  `s ≫ p = 𝟙 a`, `s ≫ r = w`, `T p`, `T r`. Mathlib composition is diagrammatic.
  No functorial factorization or choice of these data appears.

### Each conclusion and the objects it uses

- `R_T(x,y)` is `FractionCategory T x y`, a type synonym of the existing Mathlib
  `T.RightFraction x y`. Its object fields are precisely apex `X'`, denominator
  `s`, membership `hs : T s`, and numerator `f`.
- `FractionHom a b` consists of an apex map `hom` and exactly the equations
  `hom ≫ b.s = a.s` and `hom ≫ b.f = a.f`. The category instance composes these
  maps. No marking is imposed on the morphism. The main theorem explicitly asserts
  `W h.hom` for every such `h`, as the node states; two-out-of-three with `hTW`
  and the denominator triangle yields this property.
- `∃ L q` is the asserted localization, with no requirement on its presentation.
  `IsLocalization W q` includes the quasicategory condition and inversion of `W`.
  For each quasicategory in the containing universe it identifies the entire
  coherent functor simplicial set with the full subcomplex on `W`-inverting diagrams.
  The factor is the actual precomposition map and is `IsFunctorEquivalence`.
  Unrestricted coherent transformations and their higher simplices are retained.
- Essential surjectivity is `∀ l, ∃ x, EquivalentObjects L (object q x) l`.
  It uses equivalence edges with those endpoints and does not require strict
  vertex surjectivity.
- Each `c x y` is an actual simplicial map from the degreewise enlarged nerve of
  the exact fraction category into `mappingSpace L (object q x) (object q y)`.
  The conjunct `∀ x y, IsWeakHomotopyEquivalence (c x y)` is the stated equivalence
  of weak homotopy types, with the recorded geometric-realization definition.
- `Postcomposition T q c` supplies composition by the localized target arrow
  on those mapping spaces. The full simplicial square with `postcompose T x g`
  commutes by `AreNaturallyEquivalent`. Every vertex of that composition map
  satisfies `Composes e.val (localizedEdge q g) (p.app _ e).val`, so the map is
  linked to the actual arrow `g`, not an unrelated map of the correct type.
- `TotalFractionCategory T x` is the real category of varying-target spans.
  `TotalFractionHom` has an apex map and target map, the denominator triangle,
  and the numerator square. `targetProjection`, `targetFiber`, `targetNerveMap`
  and `mapTotalFractions` use exactly these data.
- `CoherentTargets T q c` supplies a single simplicial arrow diagram on this
  total category for each `x`. Its source evaluation is constant at `object q x`;
  its target evaluation is `targetNerveMap T x ≫ q`. It therefore retains each
  chain of target maps and all its higher compatibilities. `TargetComparison`
  requires that restriction to each fiber factor through the fixed-endpoint
  arrow mapping space and agree, by a coherent equivalence there, with `c x y`
  converted by the exact `rightPinchPrism` formula in every degree.
- `LocalizationNaturality W T q c D` quantifies every relative functor `F : C ⥤ D`
  preserving `W` and `T`. For a target localization and its coherent fraction
  comparison, it gives `Q : L ⟶ K` with an equivalence edge `η` between `q ≫ Q`
  and the enlarged nerve of `F` followed by `q'`. This is exactly the functor
  induced by localization universality, rather than an arbitrary unconnected map.
  It gives coherent source and target arrow diagrams realizing the same `c` and
  `c'`, and an equivalence edge `ξ` between their actual functor images on the
  total fraction category. Both endpoint evaluations of `ξ` equal the
  transformations obtained by restricting that very `η`: along the constant
  source-object map and along the target projection, respectively. Restriction
  to fixed-target fibers followed by the canonical pinch equivalences is thus
  the mapping-space naturality square with the prescribed endpoint transport.
  This formulation keeps all coherent target diagrams; it does not force strict
  equality between the vertices `Q(qx)` and `q'(Fx)`. Target comparisons are
  inputs with `CoherentTargets` and `FractionFormula`; applying this theorem to
  a second category satisfying its hypotheses supplies those inputs.
- `FractionFormula T q c` uses the landed `Composes`: the consecutive edges are
  the localized denominator and the comparison image, and the long edge is
  the localized numerator. Its face convention is δ₂, δ₀, δ₁. Since `q` inverts
  `T ⊆ W`, this says precisely `[c(t,f)] = q(f)q(t)⁻¹` in the homotopy category.
- The last conjunct gives, for every mapping-space vertex `e`, an actual fraction
  `a` with `π₀.mk (c(a)) = π₀.mk e`. Equality of components of this mapping space
  is the node's homotopy relative to endpoints. Its objects and components are
  used directly; no ordinary localization replaces the specified `hL` convention.

### Dependency declarations and sources read

`Sheaf.CategoryTheory.EnhancedDiagramsCones`: full signatures and docstrings of
`IsEquivalenceEdge`, `mappingSpace`, `mappingSpaceMap`, `AreNaturallyEquivalent`,
`IsFunctorEquivalence`, `evaluation`, `fullSubcomplex`, `diagramVertex`, and
`IsWeakHomotopyEquivalence` were read. The existing definitions are reused.

`Sheaf.CategoryTheory.FiniteReedyLocalization`: the full definitions and docstrings
of `largeNerve`, `Inverts`, `localDiagrams`, `IsLocalization`, `object`,
`EquivalentObjects`, and `Composes` were read. These are the declarations recorded
by `def-coef-coherent-localization-interface`; no finite-Reedy localization theorem
is a hypothesis or a conclusion of this item.

`Sheaf.CategoryTheory.RightPinchComparison`: the full signatures, docstrings, and
prism implementation of `arrowMappingSpace`, `arrowMappingSpaceInclusion`,
`rightPinchPrism` and `right_pinch_comparison` were read. The existing canonical
conversion, including its fixed endpoints, is used.

The statements and records of all current proof dependencies were read.
The stated proof modules are imported as described under return C. Mathlib's
`RightFraction`, nerve constructions, two-out-of-three, multiplicativity,
relative pullbacks and base-change stability signatures and docstrings were inspected.

Source checked online: [Cisinski, Higher Categories and Homotopical Algebra](https://cisinski.app.uni-regensburg.de/CatLR.pdf),
Definition 7.1.2 and Proposition 7.1.3 (PDF pages 338–339), Theorem 7.2.8 and
Remark 7.2.10, especially (the project server) and (the project server) (pages 350–351), and Theorem
7.2.16 (page 353). These provide coherent localization, the span weak homotopy
model, the component formula, and the pullback-stable calculus. The new proof
plan follows the current node, not the returned hammock proof.

### Edge cases

Checked before and after repair: empty `C` (no nonemptiness assumption), empty
fraction or mapping spaces (no artificial span exists), identity spans and identity
denominators (no reduction restriction), discrete categories and `T=W=isomorphisms`,
`T=W`, zero and degenerate nerve simplices, and distinct object/arrow universes
on both sides of a relative functor. Only `T`-pullbacks are assumed. The coherent
comparison on endpoints allows arbitrary localization models rather than silently
requiring their vertices to be strictly identical.

### Searches

Retained searches from the saved packet: LeanFinder for the nerve of trivial-fibration
spans modeling localization mapping spaces (eight unrelated nerve hits); Loogle
`Localization, nerve` (no hits, unknown `nerve`); Mathlib grep `Fraction|Cocycle|Hammock`
(twenty-five ordinary-fraction/cohomology hits); LeanSearch for category of cocycles,
acyclic fibrations and localization mapping spaces (eight unrelated hits); upstream
and side-project grep for fractions, hammocks, and the exact item id; blueprint/DAG
search for a separate commuting-apex fraction-category definition (none).

Repair searches rerun with `msearch.py`:
- LeanFinder: “Coherent infinity localization has mapping spaces modeled by nerves
  of categories of trivial fibration fractions”: eight hits, including ordinary nerve
  quasicategory and nerve adjunction declarations, none is this theorem.
- Loogle: `RightFraction, nerveMap`: no hits; the service reported unknown
  `RightFraction`, recorded as an unsuccessful query, not evidence of nonexistence.
- Mathlib grep `Fraction|Cocycle|Hammock` in `CategoryTheory`: twenty-five hits;
  the existing ordinary `RightFraction` is reused, and no infinity-space theorem matches.
- `rg` of `lean/Sheaf` and the read-only slopmaster2 `WeilConjectures` for the item
  declaration and new helper stems found no duplicate declaration. The upstream
  search for the exact item id had no occurrence. Related right-fibration coherent
  target predicates are specific to right-fibration data, not this fraction category.

No new node, dependency module, statement correction, or disputed statement.
The node's natural-language statement is unchanged. Every helper belongs to the
fraction notion introduced by this node and is listed in `lean.declarations`.
The repaired complete module compiled through `scompile.py`, at both sandbox and
library paths, in 2.0 seconds each with no errors or warnings. The final delivery
dry run below verifies the exact synchronized node signature and server preflight.
No direct Git command, live-source edit, global build, or push is performed.

## Earlier second reading (a previous round; superseded)

The independent reading retained with returned head `9c301e145c77` applies to the
superseded hammock version and does not approve this repaired statement. The maintainer's
return overrides its previous no-mismatch conclusion. This repaired packet is for the
separate second reader specified in the brief; that reader must independently review the
new signature, helper predicates, A–D repairs, and hypothesis/clause correspondence above,
and replace this historical status with their reading before delivery.

## Second reading by Q05

I independently read the current shared node, the sandbox node and complete module,
return A–D in `coord/returns/Q05.md`, the three statement-dependency records and their
actual declarations, and the current proof-dependency records. This reading concerns
the repaired existential-localization version, not the historical hammock version.
No repair-note file for this item was present. No new definition node, dependency
module or statement correction is included, so H12/H13 and the correction citer audit
do not apply.

Source: I opened [Cisinski, Higher Categories and Homotopical Algebra](https://cisinski.app.uni-regensburg.de/CatLR.pdf)
and read Definition 7.1.2, Proposition 7.1.3, the standing assumptions 7.2.1,
Definitions 7.2.2 and 7.2.6, Theorem 7.2.8, Remark 7.2.10, Definition 7.2.14,
Lemma 7.2.15, Theorem 7.2.16, Corollary 7.2.18 and Definition 7.2.20
(PDF pages 338–355). This is not a Stacks result; the node explicitly says so.
The source's standing infinity-category/isofibration assumptions apply to the nerves
here: containing every isomorphism makes the wide subcategory isofibration condition
hold. Source pullback closure includes existence and invariance under isomorphism;
the Lean relative pullback class plus stability, composition and all isomorphisms
express exactly that. The split equation implies equality of the saturations of T
and W, which is the hypothesis used in Corollary 7.2.18. No finite-limit, terminal-object,
model-category or functorial-factorization assumption is imported as a theorem binder.

The list below was made from the node before checking its rendering. Each verdict is
against the actual definitions, not just the names.

| Node object, hypothesis or conclusion | Lean rendering and verdict |
| --- | --- |
| Small ordinary category A, allowing size enlargement | `C : Type u`, `[Category.{v} C]`, `largeNerve C`; exact, with independent object and arrow universes. The containing universe is `max u v w z t`. |
| W contains all isomorphisms | `hWiso : MorphismProperty.isomorphisms C ≤ W`; exact. |
| W has two-out-of-three | `[W.HasTwoOutOfThreeProperty]`; exact. Mathlib includes composition and both cancellation directions. |
| T is a subclass of W | `hTW : T ≤ W`; exact. |
| T contains all isomorphisms | `hTiso : MorphismProperty.isomorphisms C ≤ T`; exact. |
| T is closed under composition | `[T.IsMultiplicative]`; exact, since its identity clause follows from the explicit isomorphism hypothesis. |
| Pullbacks of each T arrow along every arrow exist | `[T.HasPullbacks]`; exact. I read its `hasPullback` field; it requires the marked leg only, not all pullbacks in C. |
| Each resulting projection belongs to T | `[T.IsStableUnderBaseChange]`; exact. Its `of_isPullback` field applies to any pullback square. |
| Every w admits z, s, p, r with ps = 1, rs = w and p,r in T | `hsplit` binds these objects and arrows in this order and asserts `s ≫ p = 𝟙 a ∧ s ≫ r = f ∧ T p ∧ T r`; exact diagrammatic composition, without functorial choices. |
| R_T(x,y) objects are marked-denominator spans | `FractionCategory T x y := T.RightFraction x y`; exact reuse of Mathlib data `X'`, `s`, `hs`, `f`, with no quotient. |
| R_T morphisms are all commuting apex maps | `FractionHom.hom`, `.left`, `.right`, and `fractionCategory`; exact equations `h ≫ b.s = a.s` and `h ≫ b.f = a.f`. No T or W restriction is imposed on the morphism type. |
| These apex maps automatically belong to W | The explicit conjunct `∀ x y a b h, W h.hom`; exact. Both denominator legs lie in W and two-out-of-three applies to `.left`. |
| There exist L and q, with L a quasicategory and q inverting W | `∃ L q, IsLocalization W q ∧ ...`; exact. I expanded the recorded `FiniteReedy.IsLocalization`, whose first two conjuncts are these assertions. No hammock object or localization theorem is required. |
| q is essentially surjective | `∀ l, ∃ x, EquivalentObjects L (object q x) l`; exact. The recorded predicate is an equivalence edge with those two endpoints, not equality of vertices. |
| Restriction is an equivalence onto the full W-inverting functor category for every E, including transformations | The remaining `IsLocalization` conjunct quantifies every quasicategory in the containing universe. The factor `e` satisfies `e ≫ localDiagrams.ι = (MonoidalClosed.pre q).app E` and `IsFunctorEquivalence e`; exact. `localDiagrams` is the full simplicial subcomplex and keeps all higher simplices. |
| NR_T(x,y) naturally models the specified mapping space | `∃ c : ∀ x y, largeNerve (FractionCategory T x y) ⟶ mappingSpace L (object q x) (object q y)` and `∀ x y, IsWeakHomotopyEquivalence (c x y)`; exact weak homotopy types, with the recorded right-pinched mapping space and realization definition of weak equivalence. |
| Naturality under postcomposition in y | `Postcomposition T q c`; exact. It uses the actual functor `postcompose T x g`; the square commutes by `AreNaturallyEquivalent`. The map `p` is linked to composition by the actual edge `localizedEdge q g` through `Composes`, not just selected by its type. |
| Coherent compatibility with target diagrams | `CoherentTargets T q c` and `TargetComparison`; exact. A single arrow diagram A on the entire `TotalFractionCategory T x` has constant source `qx` and target `targetNerveMap T x ≫ q`. Its fiber comparisons factor through `arrowMappingSpace` and agree with c through the specified `rightPinchPrism` formula. Thus this is full simplex data on all chains of target maps, not unrelated vertex squares. |
| Naturality under functors preserving W and T | `∀ D [Category D], LocalizationNaturality W T q c D`; exact. F preserves W and T separately, and `mapFractions`/`mapTotalFractions` apply F to the actual data. The induced Q is linked to F by the equivalence edge η. The equivalence ξ of the total arrow diagrams has both endpoint evaluations equal to the restrictions of that same η, so it retains the prescribed endpoint transport. No equality of localization vertices, pullback preservation or equality of category universes is required. |
| The component of (t,f) is q(f)q(t) inverse | `FractionFormula T q c`; exact. `Composes (localizedEdge q a.s) (c(a)).val (localizedEdge q a.f)` uses faces 2,0,1 of a two-simplex. Since q(t) is an equivalence, this is precisely the claimed equality in the homotopy category. |
| Every arrow is homotopic relative to endpoints to a fraction | The final `∀ x y e, ∃ a, SSet.π₀.mk (c(a)) = SSet.π₀.mk e`; exact. These are components of the fixed-endpoint mapping space itself, in accordance with the node's convention for hL. |

I opened the actual implementations of `IsEquivalenceEdge`, `mappingSpace`,
`mappingSpaceMap`, `AreNaturallyEquivalent`, `IsFunctorEquivalence`, `fullSubcomplex`,
`evaluation`, `diagramVertex` and `IsWeakHomotopyEquivalence` in
`EnhancedDiagramsCones.lean`; `largeNerve`, `Inverts`, `localDiagrams`,
`IsLocalization`, `object`, `EquivalentObjects` and `Composes` in
`FiniteReedyLocalization.lean`; and all five recorded declarations in
`RightPinchComparison.lean`. The prism collapses its one-end to the last vertex,
matching the mapping-space initial-face convention. The use of `noncomputable` in
some predicates is due to existing pullback/internal-hom constructions, not a
choice of data from a postponed existence theorem.

Edge cases: empty C admits no artificial inhabitant; essential surjectivity then
forces L to have no vertices. Empty fraction and mapping spaces are permitted.
Identity denominators are retained, and their fractions have the ordinary arrow's
component. For discrete C and T = W = isomorphisms the construction retains the
ordinary discrete mapping sets. For T = W all hypotheses and conclusions remain
well formed; there is no proper-subclass restriction. Zero objects, when present,
are ordinary objects and are not excluded. At degree zero, the prism is the edge
itself, the mapping-space vertices are edges with the two fixed endpoints, and the
formula has the correct 2-simplex orientation. Degenerate and higher simplices
remain in both total and fiber categories. There is no ring, characteristic,
scheme, integer degree or external index set to restrict. The five universe
parameters are explicitly bound, and target D uses independent w,z; every nerve
and mapping space in a naturality square is lifted to their common containing
universe. No file-local notation, local instance or private copy is used.

Independent searches, using different wording from the worker:

- LeanFinder via `msearch.py`: “The classifying space of the category of cocycles
  with pullback stable denominators computes the derived mapping space of a
  relative category”: eight hits about ordinary cofibrant-object localizations,
  homotopy classes, derived natural transformations and derived-category fractions;
  none is this simplicial mapping-space theorem.
- Loogle via `msearch.py`: `"RightFraction"`: twelve successful hits. I opened
  `MorphismProperty.RightFraction` in Mathlib and confirmed it supplies the exact
  span data already reused here. `RightFractionRel` is an ordinary equivalence
  relation, not the category of all commuting apex maps.
- LeanSearch via `msearch.py`: “Classifying spaces of categories of acyclic
  fibration cocycles compute mapping spaces after localization”: eight ordinary
  localization/model-category hits, no matching theorem.
- `rg` in pinned Mathlib CategoryTheory/AlgebraicTopology, upstream
  `WeilConjectures`, and project `lean/Sheaf`, using `cocycle`, `fractioncategory`,
  `FractionHom`, `two.arrow`, `classifying.*localiz`, `localiz.*classifying`,
  `largeNerveMap` and `LocalizationNaturality`. The upstream cocycle hits are
  algebraic cochains/descent. Project fraction hits are the distinct zigzag,
  coherent-nerve and model-category interfaces; I opened the matching lines and
  they do not state this theorem or define this commuting-apex category. DAG
  searches for commuting-apex/varying-target spans and categories of fractions
  found no separate definition node for these helpers. The Mathlib ordinary
  right-fraction object is reused through a synonym so that it can carry this
  category structure. No existing declaration replaces the delivery.

Mismatches found and repaired:

1. H8: the theorem docstring's first proof step used NT and T-inverting functors,
   whereas the current node constructs its localization from NW. Corrected it to
   W, recorded composition closure from two-out-of-three, and made clear that Kan
   completion can add vertices, so essential surjectivity is proved in step 3.
   The other six steps match the node's terminal-local-comma proof; no hammock
   construction is reintroduced.
2. H9: `lem-coef-localization-homotopy-category` now has a recorded module on the
   current base, after the worker's pass. I opened its source and statement and
   added the required non-public proof import
   `Sheaf.CategoryTheory.LocalizationHomotopyCategory`. Its equal-universe nerve
   formulation is usable after the ordinary category/nerve universe enlargement;
   it does not restrict this theorem's binders. The other available proof modules
   and the Mathlib pushout-product module were already imported correctly.
3. Removed duplicated “category” in the module overview. No mathematical
   signature or node statement was changed. The node's literal multiline
   `lean.statement` remains exactly the signature before `:=` in the file, and
   its 21-name declaration inventory equals the file's declaration inventory.

There is one postponed theorem, exactly this node, with whole proof `sorry`.
Every helper definition has real data or an explicit predicate; the category and
functor laws are implementation obligations, not additional proved lemmas. All
21 declarations have source/blueprint docstrings. No line exceeds 100 characters.
The node differs from the shared base only in `lean` and the two authorized landed
statement-dependency additions recorded by the worker. The return's A–D repairs
are present and no node-field correction is needed.

Validation: I compiled the repaired delivered module with the prescribed
`scompile.py Q05 lem-coef-trivial-fibration-fraction-model` wrapper. Both sandbox
and library compilations passed (1.9 s and 2.0 s), with no errors or warnings.
The required server delivery dry run and push are performed after this reading.
