## Worker report

The module `Sheaf.AlgebraicGeometry.TopBaseChangePresheaf` states
`AlgebraicGeometry.top_base_change_presheaf`, with its proof postponed, and constructs
four real helper maps. It does not change the mathematical statement.

Hypotheses and clauses, matched individually:

- Schemes and arbitrary maps `f : X ⟶ S`, `g : T ⟶ S`: the corresponding binders, with
  `X S T : Scheme.{u}`. The chosen fibre product is `pullback g f`, canonically the
  same cartesian square, with `v = pullback.snd g f`, `f_T = pullback.fst g f` and
  commutativity `pullback.condition.symm`. Reversing the order matches the existing
  restricted-resolution interface and does not change the square.
- An O_X-module F: `F : X.Modules`, the existing sheaf-of-modules carrier. The general
  ringed-site carrier recorded by the dependency is transparently SheafOfModules;
  its module is imported. No quasi-coherence or local-freeness hypothesis occurs.
- A nonnegative q: `q : ℕ`, cast to ℤ only for derived cohomology.
- `R^i f_*F = 0` for i > q: `hC : C.IsLE (q : ℤ)`, where C is the explicitly
  written `schemeDerivedDirectImage f` applied to `DerivedCategory.singleFunctor ... 0`
  at F. By the definition of `IsLE`, this is exactly vanishing of H^i(C) above q,
  the recorded derived higher direct images. The total/classical comparison identifies
  them with the classical right derived functors in nonnegative degrees.
- C = Rf_*(F[0]): the term defining hC and the local C in `topBaseChangeAdjoint`.
- The particular canonical module map δ: `topBaseChangeDelta`, the existing
  `schemeDerivedBaseChangeMap` for the fibre square followed by direct image of
  `pinnedModulePullbackComparisonAt v 0 F`. This is the fixed counit/ordinary-unit
  normalization, not a hypothesis quantifying over maps satisfying the older
  existential comparison predicate. Both the mate and single comparison use the
  same existing selected left-derived counits.
- The specified κ: `derivedPullbackTopCohomology g q C hC` from the recorded dependency.
  `derivedPullback_topCohomology` supplies its IsIso proof, explicitly installed inside
  the helper definition. Its data is the recorded top truncation and pinned comparison.
- `b = H^q(δ) κ⁻¹`: the composite `inv (derivedPullbackTopCohomology ...) ≫
  (DerivedCategory.homologyFunctor ... q).map (topBaseChangeDelta f g F)`.
- Ordinary adjoint a: `tensorPullbackSectionAdjunction g |>.homEquiv _ _` applied
  to b. `topBaseChangeAdjoint` conjugates this map by the canonical total/classical
  isomorphisms `Functor.homologyRightDerivedFunctorObjSingleFunctorIso`. Its domain
  and target therefore use the classical right derived functors, exactly those used
  by the existing cocycle-sheafification interface. This conjugation is an
  identification, not an alternative choice of a.
- V, U, W, U': `V : S.Opens`, `f ⁻¹ᵁ V`, `g ⁻¹ᵁ V`, and
  `(pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)`. The equality with `f_T ⁻¹ᵁ W` is precisely
  `flatBaseChangeOpenEquality f g V`, which has no flatness hypothesis despite its name.
- Restricted v_V: `(pullback.snd g f).resLE (f ⁻¹ᵁ V) (...) le_rfl`.
- The actual restricted ordinary unit: `topBaseChangeRestrictedUnit v F U`. It
  composes the section-normalized ordinary pullback unit with restriction's unit,
  identifies the composite direct images, then transposes under the open restriction
  adjunction. Thus its component on a subopen Z of U is F(Z) → (v*F)(v⁻¹Z).
  Its coefficient is literally `(restrictFunctor U'.ι).obj ((tensorPullback v).obj F)`.
  It consequently implements the node's ordinary pullback followed by the canonical
  composition/restriction coefficient identification, without choosing an arbitrary
  map or requiring a separate coefficient-isomorphism hypothesis.
- θ_V: `topBaseChangeClass f F I V (f ⁻¹ᵁ V) rfl R q`. The helper uses existing
  `resolutionSectionClass`, which evaluates `sectionCohomologyTheta` after the
  resolution and exact-evaluation isomorphisms, then applies the inverse resolution
  comparison into the classical higher direct image. This is the canonical cocycle
  map in the recorded higher-direct-image-presheaf node.
- θ'_W: the same helper with f_T, the ordinary pulled-back coefficient, J, W and R'.
  Only the open equality above is used to identify the inverse-image section complex.
- `v_V^*`: `moduleCohomologyFMap v_V (topBaseChangeRestrictedUnit v F U) q`, the
  exact recorded resolution-based h-map. It has source and target the global
  cohomology of the restricted modules on the open subschemes U and U'.
- The conclusion is the equality of these two composites in AddCommGrpCat:
  `topBaseChangeClass ... ≫ Hom.app (topBaseChangeAdjoint ...) V =
  moduleCohomologyFMap ... ≫ topBaseChangeClass ...`. Consequently it is an equality
  on every local cohomology class, with precisely the intended section values.
- The theorem ranges over every injective resolution I,J and every
  `RestrictedResolutionSections` R,R'. These are presentation parameters for the
  specified canonical θ, not assumptions on F, f, g or V. Existence of these restricted
  resolutions for arbitrary schemes and opens is already proved by
  `restrictedResolutionSections_exists` (no flatness hypothesis); their augmentation
  and section component fields prevent any twisting of the displayed maps.
- The universe `u` is arbitrary, and the localization Hom universe `w` is arbitrary
  with the standard shared HasDerivedCategory interface. No new universe equality,
  affineness, flatness, quasi-compactness, properness, quasi-coherence, or invertibility
  of δ or θ is assumed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: Scheme and Scheme.Hom.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: chosen pullbacks and
  projections, via the public dependency imports.
- `Sheaf.CategoryTheory.RingedSiteModules`: ringedSiteModules, transparently the same
  SheafOfModules carrier as X.Modules.
- `WeilConjectures.AlgebraicGeometry.PQFCohomology`: moduleCohomology and the relation
  of classical higher direct images to total derived cohomology.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`: schemeDerivedCategory.
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`: schemeDerivedDirectImage.
- `WeilConjectures.AlgebraicGeometry.DerivedPullback`: derivedPullback.
- `WeilConjectures.AlgebraicGeometry.DerivedModuleBaseChangeMap`: the normalized
  single-comparison/module-map notion; `schemeDerivedBaseChangeMap` from its public
  dependency gives the actual mate, followed by the selected pinned comparison.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: tensorPullback,
  tensorPullbackSectionAdjunction; its public TensorPullback dependency also supplies
  the identity and composition comparison declarations of the recorded dependency.
- `WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction`:
  exists_tensorPullbackAdjunction, underlying the section-normalized adjunction.
- `Sheaf.AlgebraicGeometry.DerivedPullbackTopCohomology`:
  pinnedModulePullbackComparisonAt, derivedPullbackTopCohomology,
  derivedPullback_topCohomology.
- `Sheaf.Paper.HigherDirectImagePresheaf`: higherDirectImagePresheaf and its
  specified sectionCohomologyTheta construction.
- `WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap`: moduleCohomologyFMap.
- The already landed definition node `def-weil-pbc-flat-base-change-open-choices`
  is added to stmt_deps: its module
  `WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices` supplies
  RestrictedResolutionSections, resolutionSectionClass and flatBaseChangeOpenEquality.
  This node states no flatness hypothesis and is usable here unchanged. No new node
  or dependency repair is required.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`:
  Functor.homologyRightDerivedFunctorObjSingleFunctorIso, the actual canonical
  total/classical comparison already used to establish pqf-def-cohomology.

All recorded proof-dependency modules that exist are imported, directly or through
public imports. The proof-only node `lem-weil-pbc-derived-adjunction-top-edge` has no
recorded Lean or Mathlib declaration, so its future module import is omitted and must
be added when that proof dependency is stated. It is not required to type this theorem;
its mathematical argument remains explicitly named in the proof docstring.

Edge cases checked before writing: q = 0 recovers the ordinary unit on sections;
V empty, empty schemes and F = 0 give the unique zero class maps; V = top is included
without choosing a smaller affine open; identity g uses the same normalized unit and
κ; arbitrary nonflat g can have lower Tor contributions, but only the upper bound
on C is used by κ. A noninvertible δ is allowed: the construction inverts κ only.
Resolutions are not required to be unique, split, finite or globally acyclic beyond
being injective resolutions. θ need not be injective, surjective or invertible on V.

Searches for an existing statement:

- msearch LeanFinder: "The top derived module base change map agrees with the pullback
  map on local cohomology followed by the cocycle to higher direct image sheafification
  map". Eight hits, including SheafOfModules.sheafificationCompPullback and
  PresheafOfModules.toPresheaf_map_sheafificationHomEquiv. These are underived
  sheafification/pullback identities, not the top derived cohomology equality.
- msearch Loogle: `"rightDerived", "baseChange"`: no hits.
- msearch grep: `baseChange.*([Cc]ohomology|[Pp]resheaf)|[Cc]ohomology.*baseChange`
  under Mathlib/AlgebraicGeometry: no hits.
- msearch LeanSearch: "Derived base change on highest cohomology is the cocycle
  sheafification of pullback on local module cohomology": eight hits including
  SheafOfModules.sheafificationCompPullback, sheafifyMap, pullbackObjFreeIso;
  no total-derived top-degree normalized comparison.
- rg in WeilConjectures and Sheaf for the item id and base-change/cohomology/presheaf
  names: existing affine/flat comparison constructions and the downstream
  CoherentAffineBaseChangeEdge proof cite this missing lemma. None states this
  arbitrary-open, arbitrary-base-map top-degree equality.
- rg in both source roots for the five proposed declaration names: no declarations.

Source read: local Stacks cohomology.tex, lemma-describe-higher-direct-images (01E4),
remark-explain-arrow (01FB), remark-base-change (08HY), and the exact declarations
and docstrings of the recorded statement dependencies. No disputed statement or
statement correction was needed. Definitions contain real composites; the only
postponed proof is the named theorem matching this DAG node.

Validation: server single-file compile and delivery preflight results are recorded below.

`scompile.py` compiled the delivered module in both its sandbox and library contexts
without errors or warnings. `deliver2.py --no-push` returned OK: the delivery passes
server preflight and per-file compilation. The only sorry is
`AlgebraicGeometry.top_base_change_presheaf`, intentionally left for stage 3.

## Second reading by NV

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
