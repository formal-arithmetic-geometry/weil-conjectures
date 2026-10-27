## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceProperSupportUniversalPurity` states
`AlgebraicGeometry.AlgebraicSpace.universallyPureRelativeToScheme_of_properSupport`.
Its only proof is `sorry`; it introduces no definitions. The node's statement,
dependencies, proof and all other fields are unchanged. The theorem docstring carries
all six steps of the recorded proof and their supporting node ids.

Source read: `literature/stacks-project/spaces-flat.tex`, Tag 0CVI,
`lemma-proper-pure`, clause (1) and its proof, and
`literature/stacks-project/spaces-perfect.tex`, Tag 0CZI,
`lemma-module-support-proper-over-base`, especially clause (3) and the proof of its
equivalence with proper support. The node is a supporting lemma, not the blueprint
unit's statement. The source's proper-support hypothesis is expressed by exactly the
carrier already specified in this node.

Clause-by-clause correspondence:

- Work over Spec Z: `X : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))`.
  The lift embeds Z in the same arbitrary scheme universe `u`; it does not impose a
  characteristic restriction. All binders and the universe are explicit, with
  `autoImplicit false`.
- Y is a scheme: `Y : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))`.
  Its associated algebraic space is the existing `schemeSpace Y`; this retains its
  scheme object and structural map, rather than replacing Y by an arbitrary space.
- The morphism is `f : X ⟶ schemeSpace Y`; `hf : MapIsFiniteType f` says finite
  type, including quasi-compactness and the locally finite type chart test.
- Quasi-separatedness is exactly
  `hqs : MapIsQuasiCompact (pullback.diagonal f.hom.hom)`; separatedness of f is
  not required.
- M is a quasi-coherent module on the small etale ringed site: `M : X.QCoh`.
  Its finite type condition is `hM : SheafOfModules.IsFiniteType M.obj`, whose
  local finite generating families are the node's etale locally finitely generated
  condition. No finite presentation or flatness is required.
- The complete proper-support assumption is `hsupport`: there exist an algebraic
  space Z over the same Spec Z and a morphism `i : Z ⟶ X`.
- The carrier is a representable closed immersion:
  `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom`.
  This uses the existing scheme-test representability predicate and Mathlib's
  scheme closed immersion; it tests every scheme base change.
- Its given map to Y is proper: `MapIsProper (i ≫ f)`.
  The map is the structural composite, not an unrelated chosen proper morphism.
- The carrier module is `N : Z.QCoh`, with
  `SheafOfModules.IsFiniteType N.obj`; the required isomorphism is
  `Nonempty ((moduleDirectImage i).obj N.obj ≅ M.obj)`.
  Here `moduleDirectImage` is the existing canonical, chart-limit-normalized
  direct image. Nonempty expresses existence of the specified module isomorphism,
  not a choice of direct-image functor. This is the same carrier convention as
  `ProperQuotient.properSupport`, with QCoh bundled instead of a separate predicate.
- The conclusion is exactly
  `IsUniversallyPureRelativeToScheme Y f hf hqs M hM`. Reading its full definition
  verifies quantification over every scheme B to Y, the canonical sheaf fibre
  product and tensor pullback, every specialization and relative associated point,
  and existence of a point in its closure above the specialization. No extra
  conclusion or weaker support-only surrogate is used.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, the small etale site, structure sheaf and
  `Modules` (full signatures and docstrings read).
- `def-weil-size-convention` has an explicit metatheoretic convention record,
  with no declaration to import; `universe u` and the existing site/module universe
  parameters implement it. No independent equality of universes is assumed.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme` (the sheaf pullback and scheme-chart framework).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`, using
  Mathlib's `SheafOfModules.IsQuasicoherent` unchanged. Its localized sheafification
  instances supply the required section universe.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleDirectImage`,
  `ModuleDirectImageModel`, `moduleTensorPullback` and `moduleTensorAdjunction`.
  The complete chart-limit characterization was read, not just the functor name.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsFiniteType`,
  `MapIsProper` and their chart/topological constituents. The existing
  `MapIsQuasiCompact` supplies the diagonal condition.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`
  (line 45: closed embedding with surjective stalk maps).
- `Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor`: `ProperQuotient.properSupport`,
  the explicit existing closed-carrier convention. Its other quotient conditions
  are not imposed on this theorem.
- `Sheaf.AlgebraicGeometry.SpaceUniversalRelativePurity`:
  `IsUniversallyPureRelativeToScheme`, with `relativeAssassin` and
  `IsImpurityOverScheme`; the exact recorded declaration is used as the conclusion.

The stated proof dependencies are imported nonpublicly:
`AlgebraicSpaceClosedPushforwardStalks.closed_pushforward_geometric_stalks`,
`ReducedClosedSubspaceSupport.exists_unique_reduced_closed_subspace`,
`RelativeAssassin.Scheme.Modules.relativeAssassin`, and
`AlgebraicSpaceEtaleChartSupport.etale_chart_moduleSupport` (module suffix followed
by declaration suffix here; actual namespaces are AlgebraicGeometry.AlgebraicSpace,
except the scheme relative assassin). The four remaining proof-only nodes
`lem-sfb-space-finite-type-support-pullback`,
`lem-sfb-space-closed-subspace-proper`,
`lem-sfb-space-proper-support-closed-operations`, and
`lem-sfb-space-proper-base-change` currently have neither Lean records nor Mathlib
matches nor upstream closed audits, so there are no modules for them to import.
They are retained in the DAG proof dependencies and explicitly named in the docstring.
They are not needed to elaborate this stage-2 statement.

Edge cases checked before writing:

- Empty X, empty Y, empty Z, and the zero module are allowed by every binder.
  The zero module has empty relative assassin after every base change, so the
  universal-purity conclusion is vacuous as required; no nonempty hypothesis occurs.
- Identity base change is included in the recorded purity definition, as are
  nonflat base changes and an empty test scheme.
- A reflexive specialization is allowed: the associated point itself supplies
  the specialization lift. There is no requirement of a strict specialization.
- N need not have full support on Z: the proof explicitly passes from the carrier
  to the actual closed support; neither faithfulness nor reducedness of Z is assumed.
- The base and carrier can be non-Noetherian and nonreduced; no noetherianity,
  excellence, characteristic, flatness, finite-presentation or separatedness
  hypotheses were added.
- Arbitrary scheme universe u is retained, including the lifted integer base.
  The conclusion reuses precisely the dependency's site and module universes.

Searches actually run using msearch.py with group Q46 and this item:

- LeanFinder: `A finite type quasi coherent module on an algebraic space with
  support proper over the base is universally pure`: eight hits including
  `SheafOfModules.IsFiniteType`, quasi-coherent finite-presentation interfaces
  and scheme local quasi-finiteness; no proper-support universal-purity theorem.
- LeanSearch: `Proper support implies universal relative purity for a finite
  type quasi coherent module on an algebraic space`: eight hits including
  `AlgebraicGeometry.isProper_eq`, `Module.mem_support_mono`,
  `Module.isClosed_support`, `Module.support` and `Module.mem_support_iff_of_finite`;
  no theorem for algebraic-space module relative purity.
- Loogle: `"AlgebraicGeometry", "IsProper"`: twelve scheme properness hits,
  including `Scheme.Hom.isProperMap`, `IsProper`, and base-change/composition
  instances; none states this module theorem.
- Mathlib grep: `UniversallyPure|proper.*pure|ProperSupport`: three unrelated hits
  in traversable functors, universally closed topological maps, and purely
  inseparable ring homomorphisms; no matching declaration.
- rg in `lean/WeilConjectures` and `lean/Sheaf`:
  `UniversallyPure|proper.*pure|proper_support|properSupport`. Upstream universal
  purity hits concern Weil weights; project hits include the actual purity
  definition, proper Quot carriers, and etale sheaf proper-support operations,
  but no theorem matching this item. The relevant existing module interfaces
  were opened and reused.
- `grep -rn` for the item id in `lean/WeilConjectures` and rg for the item id in
  `dag/lean_names_upstream.json`: no match.

Validation: the prescribed scompile.py compiled the file in its sandbox form and
its library module form (1.8 and 1.7 seconds respectively), with no errors and no
warnings. The final node lean.statement is extracted verbatim from the delivered
signature. There are no new nodes, dependency repairs, statement corrections or
statement disputes.

## Second reading by Q46

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
