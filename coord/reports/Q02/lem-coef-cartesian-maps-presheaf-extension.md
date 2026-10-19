## Worker report

Stage 2, Q02, item lem-coef-cartesian-maps-presheaf-extension, 2026-10-17 UTC.
The module is Sheaf.CategoryTheory.CartesianMapsPresheafExtension, main declaration
SSet.Enhanced.CartesianPresheafExtension.cartesian_maps_presheaf_extension.
The theorem alone is postponed by sorry. All 22 supporting declarations have real data
or define predicates; their docstrings cite this node and GHN Lemma 9.10. The theorem
has the complete seven-step natural-language proof plan, including universes and the
mapping-space limit criterion. No statement correction or dispute is needed.

Source read: https://arxiv.org/html/1501.02161v3, Lemma 9.10(1)--(4), and its proof.
This is an infinity-category result, not the ordinary-category right Kan extension.
The two full relative functor categories retain noninvertible transformations.

Clause-by-clause correspondence:

* U-small quasicategory A: `(A : SSet.{u}) [Quasicategory A]`.
* U in V in W: the coefficient universe is `c = max (u + 1) v`; the ambient
  simplicial/functor-category universe is `c + 1`. As v varies this includes every
  coefficient universe containing U; further containing universes are degreewise lifts.
  The published presheaf category remains based on spaces of universe u, rather than
  spaces of the coefficient universe. No equality of the two universes is assumed.
* P(A) = Fun(Aop,S_U): `presheaves A` is the degreewise lift of the dependency's
  `CategoryTheory.Spaces.infinityPresheaves A`, not a second presheaf definition.
* y(a) = Map_A(-,a): `yoneda A` is the published `Spaces.infinityYoneda A`, composed
  with the explicit double-ULift reassociation `baseLift A`.
* Any coherent G:Aop -> Cat_V: G ranges over all vertices of
  `CocartesianStraightening.diagrams (base A).op`. The maps `Mcart`, `Mcocart` are
  defined on that entire coherent simplicial category, not just its vertices.
* Classifying right fibration of X: `rightRepresentative T X` uses the representative
  of the dependency's complete `TransportClassifier`. `transportPresentation` is the
  explicit change of the base's lift presentation, preserving the original space
  values. `TransportClassificationClauses T` is precisely the existing classification
  interface. T and these clauses are existentially asserted, choosing a compatible
  classification; they are not extra hypotheses on A or G. The preceding dependency
  theorem supplies the classification. `sharpOver` marks all edges of this right fibration, as required.
* Chosen unstraightening: `unstraighten S hB G` decodes the actual dependency
  equivalence's unstraightening. S is its complete `Statement`; hB is existentially
  asserted (quasicategory structure on the lifted opposite base), not an extra
  hypothesis. The existing straightening theorem supplies S. O is any opposite
  functor satisfying the existing `IsCatInfinityOpposite`; no arbitrary map replaces
  this prescribed operation.
* Fun_cocart_Aop(Yop,V_G): `mappingCategory T S hB X G` is exactly
  `Marked.Over.cartesianFunctors` on the marked opposite source and the actual marked
  cocartesian unstraightening. That dependency's definition is the full subcategory
  on marking-preserving functors, with every over-base transformation retained.
* Fun_cart_A(Y,U_G): `categoryModel true` takes the opposite of the preceding full
  functor category for the pointwise opposite coefficient diagram
  (`coefficientModel true O`). Opposite identifies this with Cartesian unstraightening
  of G over A. Taking the opposite of the entire functor category is essential;
  taking only its core would lose noninvertible transformations.
* Both constructions give the extension: `IsMappingModel ... true Mcart` and
  `IsMappingModel ... false Mcocart`. Its `objects` field fixes the values to the
  displayed full relative functor categories. The complete maps M, with their
  object and arrow normalizations, specify coherent realizations of the construction.
* Arbitrary choices of classifying fibrations/unstraightenings:
  `IsMappingModel.representatives` quantifies over all right fibrations equivalent over
  the base to the classifying representative, and all cocartesian unstraightenings
  whose classified diagram is naturally equivalent to the stipulated one. It asserts
  the resulting mapping category is equivalent to the stated value. For cart=true,
  opposite translates this quantification to arbitrary Cartesian unstraightenings.
* Carries all U-small colimit cocones to limit cones: `extensions A` is the full
  subcomplex on ALL functors preserving limits of every `IsSmall.{u}` shape K in
  P(A)op, using the existing `PreservesLimitsOfShape` on coherent cones. Opposite
  converts exactly the node's colimit cocones to these limit cones. This includes
  empty K; it is not an assumption that P(A) itself is small.
* Extends G along yop: the two `AreNaturallyEquivalent (M... ≫ restriction A) (𝟙 _)`
  clauses are coherent right-inverse equivalences, using actual restriction along
  the published opposite Yoneda map.
* Unique up to coherent natural equivalence, with all transformations:
  `IsFunctorEquivalence (restriction A)` is an equivalence of the ENTIRE full
  coherent category of limit-preserving functors with the coherent category of G's.
  It is not merely uniqueness of object equivalence classes. The final
  `AreNaturallyEquivalent Mcart Mcocart` also identifies both displayed realizations.
* X' -> X acts by precomposition: the `precomposition` field uses the actual arrow
  decoded from `T.map`, equality normalized via HEq only to accommodate the endpoint
  presentations. `IsPrecomposition` fixes the resulting map on every parameterized
  relative functor simplex, not merely on objects or edges. The Cartesian variant
  applies the actual opposite functor to this map.
* Naturality in G: `postcomposition` likewise uses the actual unstraightening arrow,
  fixing its action on every relative functor simplex by `IsPostcomposition`.
  `atPresheaf` and `atDiagram` are actual coherent evaluations, so the two M maps
  include transformations and all higher simplices in both variables.
* Containing universes/no smallness of P(A): every functor category uses c+1 and
  every relative mapping category uses c; only index shapes are required U-small.
  No IsSmall assumption on P(A), no Nonempty condition, and no truncation to a core
  occurs in the theorem.

Dependency declarations used (all source signatures and docstrings were read):

* Sheaf.CategoryTheory.EnhancedDiagramsCones: `SSet.Enhanced.coneCategory`,
  `fullSubcomplex`, `CatInfinity`, `AreNaturallyEquivalent`, `IsFunctorEquivalence`.
* Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases and its fibration imports:
  the existing left/right/Cartesian/cocartesian fibration interfaces.
* Sheaf.CategoryTheory.SpaceTransportClassification:
  `space_transport_classification`, `TransportClassifier`,
  `TransportClassificationClauses`, `transportDiagrams`, `transportFibrations`,
  `TransportFibration`, `TransportOverEquivalence`, `IsEssentiallySmallSpace`.
  The current server source unifies `smallSpaces` with `Spaces.infinityCategory`;
  transportPresentation therefore uses the existing notion without a duplicate.
* Sheaf.CategoryTheory.CocartesianStraightening:
  `CocartesianStraightening.cocartesian_straightening`, `Statement`, `diagrams`,
  `coCart`, `object`, `classify`, and its normalized relative enrichment.
* Sheaf.CategoryTheory.CatInfinityLimitsCartesianClosed:
  `catInfinity_limits_colimits_cartesianClosed` and its coherent category infrastructure.
* Sheaf.CategoryTheory.CatInfinityOppositeInvolution:
  `catInfinity_opposite_involution`, `IsCatInfinityOpposite`.
* Sheaf.CategoryTheory.InfinityPresheafYoneda:
  `CategoryTheory.Spaces.infinityPresheaves`, `infinityYoneda`.
* Sheaf.CategoryTheory.InfinityLimitsProductsPullbacks:
  `SSet.Enhanced.PreservesLimitsOfShape` (all actual cones).
* Sheaf.CategoryTheory.SmallRightAdjointDiagramCompactModel:
  `compactDiagramValue`, `compactDiagramArrow`, `compactContravariantArrow`.
* Sheaf.CategoryTheory.CoherentDiagramCoyoneda:
  `SSet.Enhanced.Coyoneda.vertexFunctor` (actual coherent simplex decoder).
* Sheaf.AlgebraicTopology.MarkedRelativeCartesianModel and its public imports:
  `SSet.Marked.Over.cartesianFunctors`, the relative marked full functor category.
* Sheaf.CategoryTheory.SpaceValuedStraightening:
  `SSet.Enhanced.SpaceStraightening.space_valued_straightening`, build prerequisite
  repaired as described below.

The newly cited existing nodes have landed Lean records, and do not change the
mathematical statement. The original five statement dependencies are retained.
Available original proof dependencies are imported: CatInfinityOppositeInvolution,
InfinityPresheafFreeCocompletion, InfinityYonedaEvaluation,
InfinityPointwiseYonedaEvaluation, InfinityYonedaPresheafLimits, and
MarkedPointCartesianModel, in addition to dependencies already public-imported.
The four proof prerequisites without a Lean record at this reading are
lem-coef-fibration-straightening-space-restriction,
lem-coef-parametric-straightening-mapping-spaces,
lem-coef-spaces-small-colimits-universe, and
lem-coef-sset-anodyne-pushout-product; they are proof inputs, not absent notions
needed to type this statement. Their mathematical roles remain in the proof docstring.

Edge cases checked before writing:

* Empty A: P(A) is terminal, its initial presheaf is also terminal, and the empty
  colimit must map to the terminal category. Empty shapes are included explicitly.
* Empty X: the relative full functor category has its unique empty-source functor
  and is terminal, again agreeing with the empty-colimit clause.
* A a point, X a point or two discrete points: the value is G or G times G.
* A a point, G the non-groupoid [1]: the formula retains its noninvertible arrow;
  the Cartesian expression needs the full opposite, not a core. For a Kan X,
  invertible X-edges impose the appropriate transport without removing arrows of G.
* Empty coefficient category and arbitrary empty/nonempty fibers remain allowed.
* Higher Kan parameters are retained by normalized mapping-simplex composition;
  neither naturality nor equivalence is reduced to homotopy classes of vertices.
* Larger coefficients than the original spaces are admitted independently; no
  U-smallness of G, P(A), or the coefficient mapping-space presheaves is imposed.

Searches (actual msearch output is in searches.jsonl):

* leanfinder: "Cartesian preserving coherent functors from right fibrations compute
  the unique colimit to limit presheaf extension". Eight ordinary-category hits,
  no quasicategorical theorem matching this node.
* loogle: `"IsCartesian", "Presheaf"`. Zero hits.
* grep Mathlib/CategoryTheory: `cartesian.*section|section.*cartesian|presheaf.*extension`.
  Three unrelated monoidal/category declarations, no match.
* leansearch: "The infinity category of cartesian functors from right fibrations
  is a limit preserving extension to presheaves". Ordinary Kan extension/fibered
  category results, no match for the coherent full-category statement.
* rg on upstream WeilConjectures and shared lean/Sheaf for Cartesian/presheaf/
  extension combinations: no existing complete statement. The existing modules
  named above supply the actual notions, which are reused.
* grep -rn of the exact node id in upstream WeilConjectures: no match.
* rg of `CartesianPresheafExtension|cartesian_maps_presheaf_extension` in
  dag/lean_names_upstream.json, Mathlib, upstream WeilConjectures and shared
  lean/Sheaf: no declaration collision or duplicate theorem found.

Compilation: prescribed scompile.py compiled BOTH delivered files individually,
including preliminary, sandbox-isolation, and library checks, without errors or
warnings. No lake build or direct compiler was run.

## Dependency modules

lem-coef-space-valued-straightening, same existing module
Sheaf.CategoryTheory.SpaceValuedStraightening. A concurrent landing unified
smallSpaces with the already existing noncomputable Spaces.infinityCategory.
The old `abbrev Diagrams` then failed compiler.ir.check because its data depends on
that noncomputable presentation. This delivery changes exactly that declaration's
modifier to `noncomputable abbrev Diagrams`. Data and mathematical statement are
unchanged. The node copy changes only lean, with the explanation in lean.note.
The repair is necessary for the KanRelativeNerveLeftFibration and
CocartesianStraightening imports. Both files were compiled together successfully.
No new definition nodes are introduced.

## Second reading by Q02

I performed a separate second pass over every hypothesis and clause. I changed the
initial universal quantifier over T to an existential classifier with its
classification clauses: arbitrary abstract classifiers satisfying the interface
need not identify the same diagram, whereas the node chooses a classifying
representative. The representatives field still covers every equivalent choice.
I checked
variance, the two occurrences of opposite in the Cartesian formula, size levels,
empty shapes, precomposition direction, and full-category uniqueness. The exact
signatures in lean.statement are extracted verbatim from the files. All variables
and universes are explicitly bound; all lines are within 100 characters.
This is a self-review: the dispatcher expressly forbids starting other agents.
The maintainer's independent review remains the next review step.
