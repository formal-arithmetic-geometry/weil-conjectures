## Worker report

The delivery states `SSet.Enhanced.localization_cartesian_pullback` in
`Sheaf.CategoryTheory.LocalizationCartesianPullback`. The only new declaration is this
named theorem, whose proof is `sorry`; there are no definitions or proof-bearing helper
lemmas. Its docstring contains the node's complete four-step proof plan and names each
proof dependency.

Source checked directly: [Gepner--Haugseng, arXiv:1312.3178v4](https://arxiv.org/html/1312.3178v4),
Definition 5.3.12, Remark 5.3.13, Lemma 5.3.15 and Proposition 5.3.16. In particular the
proposition's final edge class imposes BOTH the W-projection condition and the
E-equivalence condition. The source statement agrees with the DAG; no correction or
STATEMENT-DISPUTED flag is needed.

Clause-by-clause correspondence:

- Infinity categories C, D, E: `{C D E : SSet.{u}}` and their three `Quasicategory`
  instances. The existing enhanced convention represents infinity functors by simplicial
  maps and their full functor categories by the simplicial internal Hom. Universe `u`
  can be any common universe containing all three categories; no equation with the
  larger test universe is imposed. Enlarging to a common universe includes a small C
  and independently larger D and E as in the node's two-universe convention.
- The subcategory W of C: `(W : C.Subcomplex) (_hW : InnerFibration W.ι)`.
  This is precisely the definition of a subcategory in
  [Kerodon Definition the project server](https://kerodon.net/tag/01B8). It includes closure under
  ambient compositions and homotopies, rather than merely requiring the subset itself
  to be a quasicategory. Since C is a quasicategory, W is then a quasicategory too;
  no redundant quasicategory assumption is added. It allows a proper subcategory on
  all objects, including the core of C.
- W contains every equivalence: `_hEquivalences` quantifies over every edge of C and
  uses the existing `IsEquivalenceEdge C`. Degenerate identity edges are equivalences;
  closure under faces therefore includes every object in W. No nonempty condition is
  added for C or W.
- The given functor q: `(q : C ⟶ D)`.
- q is a localization at W: `_hq : IsLocalizationAtEdges.{u, v} q (W.obj (op ⦋1⦌))`.
  This EXISTING definition quantifies over every quasicategory `T : SSet.{max u v}`;
  its factorization `r ≫ inclusion = pre(ulift q)` specifies the actual restriction
  simplicial map in every degree. `IsFunctorEquivalence r` supplies a coherent
  quasi-inverse on the FULL edge-inverting subcategory. It consequently includes all
  mapping spaces and noninvertible natural transformations. The source and target are
  lifted canonically into the containing target universe, with arbitrary `v`.
- The functor p and Cartesian-fibration condition: `(p : E ⟶ D)` and
  `_hp : cartesianFibration p`. The definition has exactly `InnerFibration p` followed
  by lifts of every base arrow with prescribed target. `IsCartesianEdge` uses the
  final-horn characterization; the existing theorem
  `SSet.Enhanced.infinity_cartesian_mapping_criterion` identifies this with the node's
  homotopy-pullback mapping-space test (HTT the project server). Thus this is the specified
  Cartesian-fibration notion, rather than a discrete or ordinary fibered category.
- E' and its two projections: Mathlib's `pullback q p`, `pullback.fst q p` to C and
  `pullback.snd q p` to E. Because p is Cartesian, this degreewise pullback is a
  presentation of the pullback in infinity categories (HTT the project server). There is no
  hypothesis that an arbitrary square is homotopy Cartesian and no additional
  fibration hypothesis on q.
- T is EXACTLY the set in the conclusion:
  `{e | (pullback.fst q p).app _ e ∈ W.obj (op ⦋1⦌) ∧
  IsEquivalenceEdge E ((pullback.snd q p).app _ e)}`.
  The first conjunct tests precisely W, not every edge inverted by q; the second
  tests equivalence in E, not just equivalence after further projection to D.
- The conclusion is the SAME `IsLocalizationAtEdges.{u, v}` predicate applied to the
  actual second projection and this exact T. It asserts the full functor-category
  universal property for all containing-universe targets, without passing to cores
  or homotopy categories.

Dependency declarations read and reused:

- `Sheaf.CategoryTheory.CompleteAlgebroid`, the recorded module of
  `def-coef-complete-algebroid`, is publicly imported. Its `completeCategory` signature
  and docstring were read, as were its imports establishing the enhanced universe and
  quasicategory conventions. No algebroid object is needed in this general theorem.
- Its underlying `Sheaf.CategoryTheory.EnhancedDiagramsCones` supplies
  `SSet.Enhanced.IsEquivalenceEdge`, `IsFunctorEquivalence`, and the full simplicial
  functor and mapping-space conventions. The complete signatures and docstrings of
  those definitions were read.
- `Sheaf.CategoryTheory.InfinityFibrations` supplies `cartesianFibration` and
  `IsCartesianEdge`; their complete signatures were read. The currently recorded
  extension `InfinityFibrationsOverSimplicialBases` publicly reexports these original
  declarations and was also read; no repair to that dependency is required.
- The landed `def-coef-universally-localizing-simplicial-map` is added to `stmt_deps`
  under brief-stage2 section 5. Its recorded module
  `Sheaf.CategoryTheory.UniversallyLocalizingSimplicialMap` is publicly imported and
  its helper `SSet.Enhanced.IsLocalizationAtEdges` is used directly, including its
  universe-lifted `edgeInvertingDiagrams`. Both complete definitions were read, along
  with the underlying `EnrichedMarkedRealization.invertingDiagrams` definition.
- The stated proof dependency `lem-coef-infinity-functor-pushout` is imported privately
  via `Sheaf.CategoryTheory.InfinityFunctorPushout`; its
  `SSet.Enhanced.infinity_functor_pushout` and coherent cocone/restriction definitions
  were read. The two other proof dependencies, the Kan-completion localization and
  Cartesian pullback pushout lemmas, currently have no Lean record, so their imports
  are omitted. They are proof dependencies only; none of their conclusions is used
  as an extra hypothesis in this statement.

Edge cases checked before writing and during the final rereading:

- Empty E: the pullback is empty; target-prescribed lifts have no target to test,
  and localization is the equivalence of the two terminal functor categories.
- Empty C: containing all equivalences does not force nonemptiness; W is empty too.
  The assumption that q localizes still applies unchanged.
- q or p an identity: the displayed projection and exact two-part marking give the
  expected identity specialization. For q the identity and W the core, T consists
  exactly of equivalence edges in E.
- W the core or all of C: `_hW` allows both and does not force W to contain every
  ambient edge. No fullness-on-vertices hypothesis was accidentally substituted.
  Inner-horn lifting for the monomorphic inclusion forces all ambient composition
  triangles on a composable pair of W edges and all ambient homotopies of W edges
  to stay in W, as required of an infinity subcategory.
- A non-groupoidal fiber such as [1]: its noninvertible edge fails the E-equivalence
  condition and is not erroneously inverted merely because its base edge is in W.
- Identity edges and their faces retain every vertex by `_hEquivalences`; no separate
  nonempty assumption occurs. Inner-horn lifting in `_hW` retains the required higher
  coherent composition simplices as well as their long edges.
- `v` is arbitrary and targets lie in `max u v`, so no independent smaller target
  universe or site-object/morphism-universe identification is imposed.

Searches made for an existing declaration:

- `msearch.py ... leanfinder`: "Pullback of a Cartesian fibration along an infinity
  category localization is a localization at edges over W mapping to equivalences".
  Eight hits were ordinary-category localization tools (`Localization.lift`, `fac`,
  `liftingLift`, the localizer-morphism tools) and `HasFibers.pullbackMap.isCartesian`.
  None is an infinity-category Cartesian-localization theorem. Mathlib's
  `CategoryTheory/Localization/Predicate.lean` was opened: its `Functor.IsLocalization`
  and universal-property signatures concern ordinary categories.
- `msearch.py ... loogle`: `IsLocalization, CartesianFibration`: zero hits; Loogle
  reports the unknown identifier `CartesianFibration`.
- `msearch.py ... grep`: `CartesianFibration|cartesian.*localization|localization.*cartesian`
  in `CategoryTheory`: zero hits.
- `rg` of the read-only upstream `WeilConjectures` for this node ID and the same
  Cartesian/localization pattern found no statement for this node. The upstream
  name inventory has no `localization_cartesian_pullback` or matching module.
- `rg` of `lean/Sheaf/CategoryTheory` found the already landed full localization
  predicate above, which is reused. It also found Cartesian mapping and pullback
  tools, not this statement. Searches for existing subcategory definitions found
  full vertex subcategories and enriched wide simplicial subcategories; neither
  replaces a general quasicategory's subcategory. The latter is spelled out using
  Mathlib's existing `Subcomplex` and `InnerFibration` in the binders, without a
  duplicate definition or auxiliary node.

Validation: the prescribed `scompile.py ND lem-coef-localization-cartesian-pullback`
compiled the delivered file both as a sandbox module and at its final library module
path, with exit code 0 and no errors or warnings (12.1 s and 2.7 s respectively for the repaired file).
All lines are at most 100 characters; `autoImplicit` is explicitly disabled. Only the
item's `lean` record and the addition of the landed localization definition to its
`stmt_deps` change; the natural statement, proof and other node fields are preserved.

Final author check: replaced the initial edge-determined/quasicategory-subset encoding
by `InnerFibration W.ι`, after checking Kerodon Definition the project server directly. The initial
encoding did not explicitly force ambient composition and homotopy closure. This is a
repair of the Lean rendering of the same natural statement, not a DAG statement change.
The delivery wrapper is rerun for the repaired module and signature.

## Second reading by ND

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
