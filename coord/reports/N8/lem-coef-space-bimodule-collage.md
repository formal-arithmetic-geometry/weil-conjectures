## Worker report

The module `Sheaf.CategoryTheory.SpaceBimoduleCollage` states
`SSet.SpaceBimoduleCollage.space_bimodule_collage`, with one `sorry` and no other
postponed theorem. Its helper structures and constructions describe this same collage
notion. There are no new DAG nodes, dependency replacements, or statement corrections.
The only added statement dependency is the already-landed
`lem-coef-infinity-adjunction-mapping-equivalence`: its generic
`AdjunctBifunctorModel` and `AdjunctTransport` specify a coherent mixed Hom functor by
its actual twisted-arrow coupling. No adjunction hypothesis from that node is assumed.

Source checked: HTT, Definition the project server and Remark the project server, printed pp. 96--97.
The PDF was read from the IAS mirror of Lurie's HTT. Definition the project server specifies a
quasicategory over the interval with identified endpoint fibers; Remark the project server
identifies correspondences with functors from the opposite first endpoint times the
second to spaces, and mentions a more precise Quillen equivalence. The complete
Segal presentation is the node's explicit agent-formulated refinement, read together
with the recorded complete-Segal/quasicategory comparison. I also read the current
blueprint ancestor `prop-coef-integral-exceptional-adjoint.proof.md`, paragraph 2.

Hypothesis and clause correspondence:

- Nested universes: `C D : SSet.{u}` and instances `Quasicategory C`,
  `Quasicategory D`; `H : uliftFunctor.{u+1,u}.obj (C.op ⊗ D) ⟶
  Spaces.infinityCategory.{u}`. Only the base is lifted to the containing universe.
  The Kan complexes which are the values of H remain small in u. No equality of
  unrelated universe levels and no resizing assumption is imposed.
- Small-space-valued coherent functor H: an actual simplicial map into the recorded
  coherent nerve of small Kan complexes. This retains both actions, their commuting
  simplices, units, and all higher simplices, rather than using a Set-valued profunctor.
- Existence of a small collage: `Nonempty (Realization H)` is the first conjunct.
  `Realization.correspondence.total : SSet.{u}` with its quasicategory witness and
  `projection : total ⟶ Δ[1]` is precisely that small infinity-category over [1].
- Full endpoint fibers C,D: `Correspondence.left_fiber` and `right_fiber` are actual
  pullback squares over the two vertices, together with `left_full` and `right_full`
  in the dependency's right-pinched mapping-space convention. Using strict framed
  fibers is a presentation of the source's identified fibers: replace the endpoints
  of a correspondence along their equivalences. It does not restrict C or D to be
  strict categories, nerves, fibrant-cofibrant enriched presentations, or Kan complexes.
- Disjoint endpoint objects: in degree zero a pullback square identifies each endpoint
  with the corresponding fiber of the label map; Δ[1] has exactly those two vertices.
  Thus the total object set is their disjoint union, with no extra objects. Whole
  endpoint simplices are retained by the same pullback conditions in every degree.
- Mixed mapping spaces: `mappingComparison c d` is a map of small simplicial sets
  from the recorded `Enhanced.mappingSpace total (left c) (right d)` to the actual
  Kan complex read from `H(c,d)`, and `mappingComparison_weak` makes it a weak homotopy
  equivalence. Its target is small in u, not a mismatched larger universe lift.
- Empty reverse mapping spaces: `reverse_empty d c n` says every degree of the
  right-to-left right-pinched mapping simplicial set is empty. This includes degree
  zero and imposes no spurious nonemptiness condition on Kan complexes.
- Exact two actions with all higher compatibilities: `mixed` is the existing
  `AdjunctBifunctorModel left right point`, with `mixed_diagram = H` and `point_unit`
  identifying the universal pointed-family source with Δ[0]. Its `classify`, `over`,
  and `classifies` identify the actual mixed twisted-arrow coupling with the pullback
  of that universal pointed-space family along H. This fixes the entire bifunctor,
  including all coherences; an unrelated pointwise equivalence of mapping spaces
  could not supply this field. The displayed mapping comparison also records the
  requested mapping-space conclusion directly.
- Complete Segal string presentation: `strings : HasStringPresentation correspondence`
  uses exactly `Classification.diagram total`, the cores of the full functor simplicial
  sets on ordinals with all restriction operators. It asserts both the existing
  `HomotopySegal.IsHomotopySegalSpace` and `SegalSpace.IsComplete` predicates. The former
  includes Kan levels and the canonical consecutive-edge comparisons into the path-model
  iterated homotopy products, not strict products over a discrete set of objects.
- Nondecreasing labels and one crossing: each ordinal diagram in this presentation
  composes with `projection` to an ordinal diagram in Δ[1]. Its labels are nondecreasing,
  so a mixed string has precisely one change. Pure strings lie in the endpoint fibers.
  Consecutive edges give endpoint arrows and the single mixed arrow. Their mapping
  fiber is H by the coupling identification. This is also the assertion about families
  of mixed arrows: the homotopy Segal equivalence gives the space of crossing labels
  together with the compatible endpoint data, with all parameter homotopies retained.
- Faces, units, and higher compatibility: the operators of `Classification.diagram`
  are actual precomposition. Interior faces therefore use composition, while degeneracies
  use units. The mixed twisted-arrow coupling specifies precisely pre- and postcomposition
  by H's actions; the same identification on the whole base supplies their higher
  compatibility. No strict associativity of an arbitrarily selected Segal inverse is assumed.
- Coherence in H: `Classifier.map` and `inverse` are actual maps between the coherent
  nerve of framed correspondences and the full bimodule functor quasicategory. `unit`
  and `counit` are natural equivalences in their entire functor objects. `models` and
  `models_diagram` normalize the classifier on every object by the actual coupling.
  `transformations` normalizes each edge: its two projection equations fix the induced
  coupling map to be the actual twisted-arrow image of `edgeMap e`, and `AdjunctTransport`
  requires a cylinder over the entire diagram transformation with the specified endpoint
  classifying maps. Thus the classifier is not an arbitrary bijection on objects or π₀.
- Coherence in endpoint functors: `restrict f g` is precomposition by the lifted
  `f.op ⊗ₘ g` on the full functor quasicategory, for arbitrary f,g. `reindex` is the
  concrete composite classifier/restriction/inverse. The final natural-equivalence
  square identifies its classified mixed bifunctor with the restricted original H.
  Composition and unit coherences transport the corresponding strict restriction
  equations through the explicit coherent inverse equivalences. There is no extra
  full-faithfulness, injectivity, or equivalence assumption on the endpoint functors.
- Additional small simplicial parameters: the parameter clause quantifies over EVERY
  `P : SSet.{u}`, including non-quasicategories and the empty simplicial set, and asserts
  that postcomposition with the inverse classifier is an equivalence of the entire
  internal functor objects. Natural transformations and higher parameter simplices are
  retained. The restriction/reindex square can itself be whiskered with any P.

Dependency declarations used, with their full source signatures and docstrings inspected:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.mappingSpace`, `IsWeakHomotopyEquivalence`, `IsFullyFaithful`,
  `AreNaturallyEquivalent`, `IsFunctorEquivalence`; Mathlib's `SSet.Quasicategory`,
  `SSet.opFunctor`, and internal-Hom structure are reused through these imports.
- `Sheaf.CategoryTheory.InfinityCategoryOfSpaces`:
  `CategoryTheory.Spaces.infinityCategory`, the coherent nerve of small Kan complexes.
- `Sheaf.CategoryTheory.CompleteSegalQuasicategoryComparison`:
  `SSet.CompleteSegalComparison.complete_segal_quasicategory_comparison` is imported
  as the recorded comparison. Its public classification-diagram and homotopy-Segal
  dependencies supply `SSet.Classification.diagram`,
  `SSet.HomotopySegal.IsHomotopySegalSpace`, and `CategoryTheory.SegalSpace.IsComplete`.
- `Sheaf.CategoryTheory.InfinityAdjunctionMappingEquivalence`:
  `SSet.Enhanced.AdjunctBifunctorModel`, `adjunctCoupling`, `adjunctProjection`,
  `AdjunctTransport`; its public twisted-arrow dependency supplies `twistedArrowMap`.
- Proof imports: `Sheaf.CategoryTheory.CoherentNerveComparison` and
  `Sheaf.CategoryTheory.TriangularCofibrantResolution`, matching the recorded proof
  dependencies. The proof-only strict-bimodule rectification node has no Lean record;
  no statement interface from it is needed to type this theorem, and it is identified
  in the proof docstring rather than replaced by a hypothesis or private definition.

Searches for existing declarations:

- `msearch.py ... leanfinder`: “Collage of a coherent space valued bimodule on C
  opposite times D with complete Segal space string presentation”: eight hits, including
  `SSet.QCat` and `CategoryTheory.SimplicialNerve`; none states the collage theorem.
- `msearch.py ... leansearch`: “Coherent space valued bimodule collage with canonical
  mixed mapping bifunctor and Segal strings”: eight monoidal `Bimod` hits, no match.
- `msearch.py ... loogle`: `CategoryTheory.Profunctor, SSet.QCat`: zero hits.
- `msearch.py ... grep`: `collage|Collage|bimodule` in `CategoryTheory`: seven monoidal
  bimodule hits. A second query `Profunctor|collage|Collage` in `CategoryTheory/Profunctor`
  returned five lines from `Profunctor/Basic.lean`. Read that file: ordinary set-valued
  profunctors do not retain the required space-valued coherent actions. Read
  `Join/Basic.lean`: its mixed hom is a singleton, so it treats only terminal H.
- `rg` in the source repository for collage, Collage, spaceBimodule, SpaceBimodule and
  the exact item id: no matching coherent space-valued collage declaration.
- `rg` in `lean/Sheaf/CategoryTheory` for collage/Collage and bimodule APIs: inspected
  `FiberColimitCollage`, `OperadicCorrespondence`, `TriangularCofibrantResolution`,
  `InfinityHomBifunctorFunctoriality`, `SpaceTransportClassification`,
  `TwistedArrowLeftFibration`, and `InfinityAdjunctionMappingEquivalence`.
  The first is an ordinary Grothendieck collage; the second is an operadic family over
  the interval; the triangular resolution takes an existing strict enriched collage.
  None already states the item. The last three supply the canonical coupling interface
  which this delivery reuses, rather than writing another Hom bifunctor.
- Exact new declaration names were searched in Mathlib, the source repository and
  `lean/Sheaf`: no existing declarations with these full names.
- The added dependency's transitive statement/proof closure was checked: it does not
  contain this item, so the added edge does not introduce a dependency cycle.

Edge cases checked mathematically before writing and on rereading the signatures:

- C empty or D empty: the collage is the other endpoint, the mixed coupling and its
  prescribed base are empty; no selected object of an empty endpoint is required.
- Both endpoints empty: the empty quasicategory over Δ[1] satisfies the fiber conditions;
  its complete Segal presentation has empty object space, not a forced terminal object.
- H empty everywhere: the disjoint union C ⊔ D has no mixed arrows. Empty Kan complexes
  are allowed by the recorded space category. Reverse homs stay empty as well.
- C=D=Δ[0], H=Δ[0]: Δ[1] has one mixed arrow, and the classifier retains its units.
- C,D arbitrary non-discrete quasicategories: their full simplicial endpoint data and
  object cores are retained; no ordinary nerve or discrete object-space hypothesis occurs.
- P empty, Δ[0], Δ[1], or a non-quasicategorical boundary: all are covered by the
  parameter clause. Identity and noninjective endpoint functors are allowed.
- All universes are declared explicitly; `autoImplicit false` is set. No local notation,
  local instance, private definition, arbitrary model chosen by a `Nonempty.some`, or
  data-valued `sorry` occurs.

Validation: the prescribed scompile wrapper compiled the module as a sandbox file and
at its library module path, without errors or warnings. The first pass detected a
small/larger-universe mismatch in the explicit mapping comparison; the target was
corrected to the actual u-small Kan value of H and the clean compile followed.
Only the named theorem is postponed. No STATEMENT-DISPUTED issue remains.

## Second reading by N8

No independent worker was started: the dispatcher's explicit instruction prohibits
sub-agents and assigns independent review to the maintainer. I reread the node and
module together as the author. This found and repaired the mapping-comparison universe
mismatch, broadened P from quasicategories to arbitrary simplicial sets, and added
normalization of the classifier on transformations by the actual induced coupling map.
The hypothesis/clause correspondence above is the resulting author check; it does not
claim to replace the maintainer's independent review.
