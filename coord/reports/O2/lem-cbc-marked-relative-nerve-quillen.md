## Worker report

The module `Sheaf.AlgebraicTopology.MarkedRelativeNerveQuillen` states
`SSet.MarkedRelativeNerve.marked_relative_nerve_quillen : Nonempty Statement.{u}`.
Its only postponed theorem is this declaration; its docstring contains all eight
steps of the node's proof, with the named inputs. The helper structures describe
this one statement. No data are extracted from an existence theorem, and no
additional theorem or independent notion is introduced.

Source checked: Lurie, [Higher Topos Theory](https://www.math.ias.edu/~lurie/papers/HTT.pdf),
section 3.2.5: Definition 2, Remarks 7 and 10, Definition 12,
Remarks 13 through 16, Proposition 18(2), Corollary 20, and Proposition 21
(printed pp. 195–204). The marked model has
cocartesian variance throughout. No change to the natural statement or proof is needed.

Clause-by-clause correspondence (names below are in `SSet.MarkedRelativeNerve`):

- Nested universes and small ordinary category: explicit `universe u`,
  `C : Cat.{u,u}`, and `Marked.{u}`; actual diagram and slice categories have
  object universe `u+1` and hom universe `u`, and their infinity localizations are
  simplicial sets in `u+1`. Any small ordinary category is covered on passing to a
  common containing universe; no equality of independent site universes is assumed.
- Strict `F:C -> M` and its underlying diagram: `F : C ⥤ Marked.{u}` and
  `F ⋙ underlying`. The `underlying` functor retains the actual simplicial sets/maps.
- An n-simplex consists of the base string and the compatible nonempty-subset
  maps: `total F` reuses `Enhanced.KanRelativeNerve.total (F ⋙ underlying)`.
  Its `Simplex.base`, `Simplex.value`, and `Simplex.compatible` are already published.
  This construction has **no Kan hypothesis**: the Kan condition appears only in
  that dependency's theorem, not in these definitions. A chain a:[m]->[n] records
  the value of t_image(a) on a. Conversely these values give each t_J, with its
  values on all simplices. Thus compatibility for all chains is exactly the
  displayed restriction/transport equation, including repeated vertices.
- Operators `t'_J=t_theta(J) Delta(theta|J)` are the existing `restrict`: compose
  each chain with theta. Projection to the base is the existing `projection`.
  `object F` equips it with the map to the maximally marked nerve, so the total
  space and projection are actual constructions, not unspecified objects.
- Mark precisely the full edge component in the last fiber: `value F` has the
  last-fiber predicate, explicitly closed under degenerate edges. The conclusion
  `Statement.marking_exact` says, for **every** F and edge, that this closure is
  equivalent to exactly the node's test. This is the same construction convention
  as the dependency's `Marked.natural`; degeneracy compatibility ensures closure
  adds nothing. No fibrancy assumption is used to obtain the exact marking.
- The right functor and its action on strict transformations:
  `AdjunctionData.N`, `objects`, and `map_values`. Objects are equal to `object F`;
  after these equality transports every chain value is postcomposed by the actual
  component of the strict transformation. Morphisms are maps in the actual slice,
  so they preserve both projection and markings.
- A left adjoint: `AdjunctionData.adjunction : A.L ⊣ N`, using the published
  normalized comma functor from the marked cone/slice comparison. Its simplices,
  actions, maps, and marking are fixed by that dependency, not redefined here.
- Projective model: `projectiveModel`, with `projective_weak` equal to
  `Marked.weak.functorCategory C` and `projective_fib` equal to the objectwise
  absolute fibration class `((Marked.cof ⊓ Marked.weak).rlp).functorCategory C`.
  Both use Mathlib's existing `MorphismProperty.functorCategory`. The model axioms
  then determine the projective cofibrations. `left_quillen` asserts preservation
  of cofibrations and trivial cofibrations into this very model.
- Quillen equivalence: `quillen_equivalence` gives the standard adjoint weak-map
  criterion for every relative X (all such X are cofibrant) and every projectively
  fibrant F. There is no projective-cofibrancy hypothesis on F.
  `Statement.derived` additionally asserts inverse **infinity** functors for every
  choice of full infinity localizations, with `DerivedComparison.unit`, `counit`,
  `left_normalization`, and `coherent_adjunction`. This does not substitute an
  equivalence of homotopy categories for the asserted homotopy theories.
- Sends projectively fibrant diagrams to fibrant objects, with exact marking:
  `IsFibrant` is natural marked fibrancy at each object;
  `AdjunctionData.nerve_fibrant` uses the recorded
  `Marked.Over.IsNaturallyFibrant true`. The marking on these same objects is
  already fixed for all F by `objects` and `marking_exact`.
- Natural comparison to cocartesian unstraightening:
  `coneRight` is right adjoint to the exact published opposite cone functor `A.T`.
  Thus it is the marked model of unstraightening allowed in the node, evaluated on
  the ordinary strict diagram, rather than an arbitrary classification with the
  same fibers. `beta` is a natural transformation; `mate` fixes it to the transpose
  of the actual cone-to-comma comparison followed by the actual relative-nerve
  counit. `beta_weak` asserts relative cocartesian weak equivalence precisely on
  projectively fibrant diagrams. `cone_fibrant` retains fibrant targets as well.
- Full derived naturality, mapping spaces and higher coherence:
  `DerivedComparison` uses the recorded full `FiniteReedy.IsLocalization`, whose
  universal property concerns full functor quasicategories. `right` and `coneRight`
  are normalized on the entire category `FibrantDiagrams C`, with every strict
  transformation. Their `beta` is an equivalence edge in the full internal hom.
  `mate_normalization` is the pasting equation identifying that edge with the
  localization of the very ordinary `AdjunctionData.beta`, via
  `FiniteReedy.transformation` and `ModelInfinity.Represents`. It is an equality
  of morphisms in the homotopy category of the **whole** functor quasicategory,
  not unrelated objectwise comparisons. Naturality in all strict transformations
  and its higher data are retained before and after localization.
- The actual fiber identification is `Statement.fiberIso`; `fiber_formula` fixes
  its inverse on every chain to restriction of the given simplex of F(c).
  `PointNormalization.nerve_formula` fixes full-chain evaluation over the terminal
  category. `augmentation_formula` uses the published point comparison (already
  identified there with the actual cone augmentation), and `point_mate` identifies
  the relative-nerve comparison with its point mate. The canonical point
  unstraightening equivalence is the inverse of this mate. Hence under these
  canonical equivalences the fiber comparison is the identity. This is the
  normalization in proof step 8. The repair additionally states
  `nerve_fiber_point`, which ties this `fiberIso` to the restriction along
  `pointFunctor c`, using the identity components of `pointDiagramIso`.
  `coneFiberToPoint` is an isomorphism from the actual cone fiber to the point
  unstraightening value; `cone_fiber_point` fixes it by its total-space
  projection through the cone base isomorphism, without referring to beta.
  `fiber_comparison` then equates the actual fiber of beta, transported by these
  two fixed identifications, with its point mate. On fibrant F that mate is a
  weak equivalence, and composing with its inverse in localization gives the
  identity on F(c), as required.
- Canonical base isomorphisms for every functor u:C'->C:
  `BaseChange.nerveIso` has source `restriction u ⋙ N_C'` and target
  `N_C ⋙ Marked.Over.pull (nerveMap u)`. No fibrancy assumption occurs here.
  `nerve_base` now fixes the image base string to `x.base ⋙ u`, and
  `nerve_values` fixes **each** chain value to `x.value m a`, after the second
  pullback projection and both `objects` transports. These formulas specify the
  canonical map independently of the adjunctions. `nerve_mate` also identifies
  this very isomorphism with the mate of the published comma Kan unit;
  `cone_mate` supplies the cone comparison. `PushPullAdjunction.projection`
  fixes the slice adjunction's second pullback projection. The earlier claim
  that the mate equations alone forced the simplex action was wrong and is removed.
- Coherent base compatibility of the comparison:
  `BaseChange.comparison_square` is an equality of actual marked maps.
  `Statement.nerve_identity`, `cone_identity`, `nerve_composite`, and
  `cone_composite` state the identity/composite equations of their total maps after
  the canonical pullback projections. The canonical mates and these equations
  supply the entire coherent base compatibility after localization; there are
  no independently chosen comparisons at separate base functors.

Recorded dependencies used, with their modules and declarations:

- `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`:
  `SSet.Marked`, its category, markings and weak equivalences;
  `SSet.Marked.marked_point_cartesian_model` supplies the absolute model in the proof.
- `Sheaf.CategoryTheory.MarkedRelativeCartesianModel`:
  `SSet.Marked.Over`, `pull`, `push`, `cof`, `weak`, `IsNaturallyFibrant`,
  and `marked_relative_cartesian_model`. The Boolean is `true` for cocartesian.
- `Sheaf.CategoryTheory.SimplicialModelCoherentDiagrams`:
  `CategoryTheory.simplicial_model_coherent_diagrams` and its normalized enriched
  diagram comparison justify the ordinary coherent-nerve interpretation.
- `Sheaf.CategoryTheory.CocartesianStraightening`:
  `SSet.Enhanced.CocartesianStraightening.cocartesian_straightening` identifies the
  marked cone model with inverse cocartesian straightening.
- `Sheaf.CategoryTheory.MarkedConeStraighteningQuillen`:
  `SSet.MarkedConeStraightening.PushPullAdjunction` and
  `marked_cone_straightening_quillen`, including point and base normalizations.
- Added **already landed** statement dependency
  `lem-coef-kan-relative-nerve-left-fibration`, module
  `Sheaf.CategoryTheory.KanRelativeNerveLeftFibration`:
  `SSet.Enhanced.KanRelativeNerve.Simplex`, `total`, `projection`, and `restrict`.
  We reuse its unconditional construction, not its Kan-valued theorem.
- Added **already landed** statement dependency
  `lem-cbc-relative-nerve-cone-left-comparison`, module
  `Sheaf.AlgebraicTopology.MarkedRelativeNerveConeComparison`:
  `SSet.MarkedRelativeNerveCone.Statement`, `Diagrams`, `TargetChange`,
  `PointNormalization`, `pointInput`, and
  `marked_relative_nerve_cone_left_comparison`. Its unmarked component supplies
  `SSet.RelativeNerveCone.Diagrams` and canonical comma/cone units. This node
  was already a proof dependency and no field of it is changed.
- Proof-only imports follow the recorded modules of
  `lem-coef-simplicial-projective-model-calculus`,
  `lem-coef-model-infinity-derived-adjunction`, `lem-coef-coherent-nerve-comparison`,
  `lem-coef-quillen-derived-counit-criterion`, and
  `lem-coef-model-localization-detects-weak-equivalences`.
  `lem-coef-infinity-monomorphism-boundary-cells` has no recorded Lean module,
  so it is cited in the proof docstring but has no invented import.

Edge cases checked mathematically before and while stating:

- C empty: no base strings, the total nerve is empty, and the unique diagram and
  empty slice assertions remain meaningful. No inhabitant of C is selected.
- C terminal: full-chain evaluation gives precisely F(*), with unchanged marking;
  the point augmentation/mate is explicitly normalized, including empty F(*).
- C=[1]: an edge is marked by its F(1) component; this verifies the required
  target-fiber variance, as opposed to marking by F(0).
- n=0 and repeated vertices: the all-chains construction handles both; there is
  no positive-dimensional or injectivity restriction on simplex operators.
- Arbitrary markings and nonfibrant diagrams: construction, marking_exact,
  adjunctions and base isomorphisms have no fibrancy hypothesis. Fibrancy is
  imposed only where the source imposes it. No cofibrancy of diagrams is imposed.
- Identity and composable base functors: recorded as equations of total maps and
  the canonical mate square, including their point restrictions.

Searches made (2026-10-17):

- `msearch.py`, LeanFinder: "The marked relative nerve of a diagram of marked
  simplicial sets is a right Quillen equivalence over the nerve of an ordinary
  category". Eight hits, all ordinary nerve/2-truncation or reflective adjunctions;
  none is a marked relative nerve or its Quillen theorem.
- `msearch.py`, Loogle: `"RelativeNerve"`. Zero hits.
- `msearch.py`, Mathlib grep: `relativeNerve|relative_nerve|marked.*[Qq]uillen`.
  Zero hits.
- `msearch.py`, LeanSearch: "marked relative nerve Quillen equivalence projective
  diagrams cocartesian model". Eight hits on ordinary nerve adjunctions, Cech
  nerves and the ordinary simplicial-set cofibration structure; none matches.
- `rg` of Mathlib, upstream `WeilConjectures`, and `dag/lean_names_upstream.json`:
  `MarkedRelativeNerve|marked_relative_nerve_quillen|relative[Nn]erve|relative_nerve`.
  No hits in those sources. The prescribed upstream node-id grep also has no hit.
- `rg` of published `lean/Sheaf` found the genuine reusable chain construction and
  the marked/unmarked left comparisons, which this module imports. No published
  declaration states this node's right adjunction plus Quillen and normalized
  derived/base/fiber comparison. Mathlib's `CategoryTheory.nerveAdjunction`,
  `nerveFunctor.fullyfaithful`, and `Nerve.quasicategory` were read: they concern
  ordinary nerves, so are not matches.

Validation of returned head: the immutable reviewer reproduced a clean compile.
On this repair's first required dry run, the current dependency overlay instead
reported `SpaceValuedStraightening.Diagrams` as depending on noncomputable
`smallSpaces`. The dependency repair below addresses this concrete diagnostic.
The repaired item and dependency both passed `scompile.py` in sandbox and
named-module modes with no errors or warnings (item 15.6 s, dependency 2.9 s
in named-module mode), retaining the 60-second limit. The delivery dry run
rechecks every delivered module. Every universe is explicitly bound, `autoImplicit` is
false, and every Lean line is at most 100 characters. Only `lean` and additional
published `stmt_deps` change on the item. No new node, natural-language statement
correction, or statement dispute is needed.


## Dependency modules

`lem-coef-space-valued-straightening`, module
`Sheaf.CategoryTheory.SpaceValuedStraightening`: the first saved-packet dry run
failed at `Diagrams`, because `smallSpaces` is now noncomputable. The dependency
module is copied with its full mathematical statement and proof docstring, and
only `Diagrams` gains `noncomputable`. Its declarations and signatures stay the
same; the node changes only in `lean`, whose note records the diagnostic. The
item adds this already published node to `stmt_deps`. It is already a prerequisite
through the Kan relative nerve, so this adds no mathematical assumption or cycle.
No data are chosen from the theorem, and no new definition of spaces is made.

## Second reading by N2

Repair second pass, using the independent immutable review of head
`36e33e8342d4c1681f7774a90a3eaca1b64dcb8c` as the independent reading, and
rereading the node and repaired file together. The original review found H3 and
H11; this section records the concrete recheck. This follow-up is the repairing
worker's own check; no additional agent was started, as the repair brief forbids
it. The maintainer will independently review the new delivery.

| Node hypothesis or clause | Lean inspected on this pass | Finding and repair |
| --- | --- | --- |
| Nested universes, small ordinary C, marked model M | `universe u`, `C : Cat.{u,u}`, `Marked.{u}`, localizations in `u+1` | Arbitrary small C and values fit a common containing universe; no inhabitance or diagram cofibrancy hypothesis. |
| Strict F and underlying U | `F : C ⥤ Marked.{u}`, `underlying`, imported `KanRelativeNerve.total` | Uses the same underlying simplicial sets and maps. The construction itself has no Kan premise. |
| Strings, all nonempty subsets and their compatibility | imported `Simplex.base/value/compatible` | Chains into a subset give its whole simplicial map, with transport to its maximum; includes degenerate and repeated chains. |
| Every simplex operator theta | imported `restrict` | Composition of chains is precisely image-subset restriction. No injectivity hypothesis or degree-zero exception. |
| Edge marked exactly by last fiber component | `value`, `Statement.marking_exact` | Explicit degenerate closure is asserted equal to the exact last-value test, for all F. Terminal and [1] examples have the required variance. |
| N is a functor with a left adjoint | `AdjunctionData.N/objects/map_values/adjunction` | Objects and transformations fixed on chains. The theorem asserts the adjunction; the repaired canonical base maps are now independently normalized, rather than inferred from a choice of this adjunction. |
| Projective structure, weak equivalences and fibrations objectwise | `projectiveModel/projective_weak/projective_fib` | Uses existing absolute classes and `MorphismProperty.functorCategory`; projective cofibrations come from that model. |
| Quillen equivalence and inverse derived functors | `left_quillen`, `quillen_equivalence`, `derived` | Every relative X is covered, only F is fibrant in the weak-map criterion; no additional cofibrancy assumption on F. Full infinity-localizations, unit/counit and coherent adjunction retained. |
| Fibrant diagrams sent to fibrant marked cocartesian objects | `IsFibrant`, `nerve_fibrant`, exact object/marking fields | Uses Boolean `true`, not the cartesian variance. Exact marking still holds without this hypothesis. |
| Natural weak comparison with cocartesian unstraightening | `coneAdjunction`, `beta`, `mate`, `beta_weak`, `cone_fibrant` | Source is the existing normalized opposite cone functor; beta remains its specified right mate and is weak on fibrant diagrams. |
| Comparison retains mapping spaces and higher coherence, natural in strict transformations | `DerivedComparison` and `mate_normalization` | Full functor-quasicategory edge, its equivalence and localized-mate pasting equation are unchanged. Fibrant subcategory retains every strict transformation. |
| Canonical base isomorphism for every u | `BaseChange.nerveIso/nerve_base/nerve_values` | H3 repaired: after both object transports and second pullback projection, the base becomes `x.base ⋙ u` and every `x.value m a` stays unchanged. This is a formula for all degrees and all chains, with no fibrancy premise. |
| Coherent comparison for identities/composites | `nerve_mate`, `cone_mate`, `comparison_square`, four identity/composite fields | All previous mate/coherence clauses retained on the very chain-normalized nerve isomorphism. |
| Canonical actual fiber and identity derived fiber comparison | `fiber_formula`, `point.nerve_formula/augmentation_formula/point_mate`, new `nerve_fiber_point/cone_fiber_point/fiber_comparison` | H3 repaired: the actual fiberIso is identified with point restriction. The cone fiber-to-point iso is fixed by projection through the cone base map. Fiber beta becomes the specified point mate; its inverse gives the identity on F(c) after localization. |

Adversarial recheck of the review's example: for C = B(Z/2) acting on a discrete
two-point value by a swap, twisting the relative-nerve adjunction and its base
mates changes the chain values of the point base map. Such a twisted family now
fails `nerve_values`, already in degree zero. Independently, twisting a fiber
comparison away from the normalized point mate violates `fiber_comparison`.
Thus identity/composite cancellation alone no longer admits the reported swap.

The fiber-to-point identification does not define itself using beta: its projection
equation involves only the cone base isomorphism, the identity-component diagram
isomorphism and the actual pullback projection. The comparison equation is then
an additional conclusion about beta. Consequently it is not a circular assertion
of a freely chosen identity. Empty categories make the point/fiber quantifiers
vacuous, empty values cause no selected vertex, and the terminal case gives the
full-chain isomorphism. Arbitrary markings and nonfibrant F remain allowed in
all construction, canonical-base and ordinary fiber-map equations. The derived
inverse of the point mate is used only when F is fibrant, as in the node.

The independent review's dependency and duplicate audit was reread; this pass
also opened the exact marked/unmarked comma and cone units, `PushPullAdjunction`,
`KanRelativeNerve.Simplex/restrict/total`, and the dependency model and comparison
signatures. `SpaceValuedStraightening` has only the computation annotation repair
above; its final theorem and ten-step proof docstring are unchanged. There is
one postponed item theorem and the preserved dependency theorem; no extra
postponed lemma or hollow data definition. H11's former placeholder is replaced
by this explicit reading, and the source-place paragraph uses section-and-item
notation so the delivery tool does not mistake HTT numbering for IP addresses.


Returned-head/current-base comparison: the immutable module was read from its
archived `packet.md` and compared with the sandbox. The repair adds the two
base-action equations, identity-component point helpers, and four fiber/point
fields; moves the unchanged `totalMap` earlier so those equations can use it;
and expands proof steps 7–8 to explain these normalizations. It retains the
full derived and coherence fields. The current read-only base has no item
module yet, and the dependency diff is exactly the one `noncomputable` keyword.
The wrapper rebases the delivery onto current `newtargets-dag`; no direct Git
operation or write in the shared repository was used.
