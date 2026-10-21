## Worker report

The module `Sheaf.Paper.SectionDerivedPushpullNormalization` states
`AlgebraicGeometry.ProEtale.ModuleRingedComparison.sectionDerivedPushpullNormalization`.
Its sole proof is `sorry`. It introduces one transparent interface definition naming the existing internal derived adjunction
with its functor types fixed, and changes no source statement.
All objects and comparisons are the existing constructions, rather than arbitrary functors
or isomorphisms quantified as assumptions.

Hypothesis and clause correspondence:

- A commutative condensed ring is the section variable
  `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}` with `[MonObj Λ]` and
  `[IsCommMonObj Λ]`. This is the underlying-object presentation of
  `Profinite.CondensedRing`, admitting arbitrary condensed rings and the zero ring.
- The morphism is `{X Y : Scheme.{u}} (f : X ⟶ Y)`, with no geometric restriction.
  `Scheme.ProEt.topology X` is used by the imported `internalModules` and `modules`.
  The site object universe is `u+1`, Hom universe `u`, and section universe `u+1`.
  There is no equality imposed between object and Hom universes.
- The pulled-back coefficient is `condensedRingObj Λ T`, the existing
  `p_T^* Λ`; `ring Λ T` reconstructs the section-ring sheaf, and
  `equivalence Λ T` is the fixed `sectionModuleEquivalence`. These are the
  transparent aliases in `SectionModuleOperationsData`, not alternate carriers.
- The ordinary operations are exactly `pullback`, `pushforward`, `adjunction`,
  `pullComparison`, and `pushComparison` in that module. Their coefficient map,
  identity-on-sections direct-image map, and uniquely mate-normalized inverse-image
  map are retained through the imported constructions.
- The only size binder beyond these data is
  `[∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]`.
  This specifies the derived localization in the selected larger universe;
  it is the same size convention as the existing section realization. It does not
  impose a mathematical boundedness, resolution, or exactness assumption.
- The first two conjuncts assert `IsEquivalence` of the actual localized forward
  functors at X and Y. Their definition is `E.functor.mapDerivedCategory`; the
  already constructed `derivedEquivalence` has precisely that forward functor.
- The third conjunct quantifies over T and every internal cochain complex P and
  asserts `CochainComplex.IsKInjective (C(E_T).obj P) ↔ P.IsKInjective`.
  The fourth states the corresponding equivalence of K-injective resolutions,
  namely `QuasiIso (C(E_X).map i) ∧ IsKInjective (C(E_X).obj I)` iff
  `QuasiIso i ∧ I.IsKInjective`. Termwise functoriality retains comparison maps
  and homotopies; no selected resolution is substituted for the canonical one.
- The two natural comparison isomorphisms are the fixed `derivedPullComparison`
  and `derivedPushComparison`. Their types already give the two required
  isomorphisms between the independently constructed derived functors.
  The next two conjuncts state their left and right universal comparison equations
  at every complex P. They include `sectionLocalizationComparison`, the actual
  `leftDerivedFunctorCounit` and `rightDerivedFunctorUnit`, and localization of
  the ordinary `pullComparison` and `pushComparison`. The left equation uses the
  section pullback's exact-localization factor map, exactly as its definition
  identifies the canonical total derived pullback with degreewise localization.
  In particular this includes all K-flat and all K-injective representatives.
- The next conjunct identifies the specified derived Hom equivalences, using
  `(derivedAdjunction Λ f).homEquiv` on the section side and
  `(normalizationInternalAdjunction Λ f).homEquiv` internally.
  The latter is definitionally the existing CondensedRing derived adjunction; its
  explicit functor type avoids repeating large inferred monoidal arguments.
  The following two conjuncts explicitly identify their units and counits.
  The section adjunction is independently derived from its ordinary adjunction;
  it is not defined by transporting the internal adjunction.
- The penultimate conjunct quantifies over every `{Z}` and `g : Y ⟶ Z` and
  asserts the composition square on every internal derived M. Its compositors
  are the actual `CondensedRing.leftDerivedUpperStarComp` and
  `derivedPullbackComposition`, localized from the specified ordinary geometric
  compositors. The final conjunct is the right-hand composition square obtained
  by `conjugateEquiv` using these exact independently derived adjunctions. Thus
  both the left composition isomorphism and its specified adjunction mate are
  compared, not an unspecified composition structure.

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt` and
  `Scheme.ProEt.topology`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `condensedRingObj`.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence`, including
  its section-ring reconstruction and unchanged underlying sheaf functor.
- `Sheaf.Paper.SectionModuleOperationsData`: `ring`, `modules`, `internalModules`,
  `equivalence`, `pullback`, `pushforward`, `adjunction`, `pullComparison`,
  `pushComparison`, `pullbackComposition` in `ModuleRingedComparison`.
- `Sheaf.Paper.CondensedModuleDerivedPushpull` and its public upstream import:
  `moduleObjectDerivedPullback`, `moduleObjectDerivedPushforward`,
  `CondensedRing.derivedUpperStarLowerStarAdjunction`, `leftDerivedUpperStarComp`.
- `Sheaf.Paper.RingedTopoiDerivedPullback`: `SheafOfModules.ringedTopoiDerivedPullback`;
  `Sheaf.Paper.ProjectionMateExact`: `SheafOfModules.ringedProjectionMateExact`.
  These supply the source's ringed derived constructions, specialized by the
  already landed section realization. The source theorem for general ringed sites
  has a more specialized universe interface; no attempt is made to force this
  site's Hom universe to match its object universe. The existing exact-localization
  section construction gives its universal derived functor with the actual universes.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`; `Mathlib.CategoryTheory.Adjunction.Mates`:
  `CategoryTheory.conjugateEquiv`.
- Already landed `Sheaf.Paper.SectionDerivedTensorData`: `derivedFunctor`,
  `derivedEquivalence`, `internalDerivedPullback`, `internalDerivedPushforward`,
  `derivedPullback`, `derivedPushforward`, `sectionLocalizationComparison`.
- Already landed `Sheaf.Paper.SectionDerivedRealization`: `derivedPullComparison`,
  `derivedPushComparison`, `derivedAdjunction`, `derivedPullbackComposition`.
  Their owning nodes are added to `stmt_deps` as authorized citations of landed
  definitions. Nothing about their statements or Lean records changes.

All recorded proof-dependency modules are imported without `public` and the eight
proof steps are written out in the theorem docstring. No proof is supplied here. The interface definition has the actual adjunction as
its data; it makes no choice and uses no new postponed theorem.
The source passages read are `derived.tex` lemma-derived-adjoint-functors,
lemma-adjoint-preserve-K-injectives, definition-K-injective and lemma-K-injective,
and `sites-cohomology.tex` lemma-adjoint and lemma-adjoints-push-pull-compatibility.

Edge cases checked: Λ=0 makes both module categories trivial and all comparison
identities remain meaningful; f=id and composable identities are included because
no properness, open-immersion or nonidentity assumption occurs; empty X and Y
are permitted schemes; complexes are genuinely unbounded, including zero complexes
and every shift; g is arbitrary; there is no characteristic or nonzero-ring
assumption. Distinct site object/morphism universes are retained throughout.
No statement dispute or source correction was needed.

Searches for an existing whole-item declaration:

- msearch LeanFinder: “Exact equivalence of internal and section module sheaves
  identifies derived adjunction units counits composition and K-injective resolutions”.
  Eight hits on generic derived-adjunction units, counits and factorization;
  no statement specializing the fixed section equivalence with all clauses.
- msearch Loogle: `CategoryTheory.Adjunction.derived, CategoryTheory.Equivalence`:
  zero hits.
- msearch LeanSearch: “Exact equivalence preserves reflects K-injective complexes
  and identifies derived adjunctions”: eight generic hits, including
  `CochainComplex.IsKInjective`, preservation of injective objects, and
  `HomotopyEquiv.isKInjective`; none states this node.
- msearch grep: `IsKInjective|mapDerivedCategorySquareIso` in
  `CategoryTheory/Functor`: zero hits.
- Direct rg of Mathlib, `lean/WeilConjectures`, and `lean/Sheaf` for the item ID,
  `section_derived_pushpull_normalization`, and
  `SectionDerivedPushpullNormalization`: no existing whole-item declaration.
  Broader searches located the existing section-derived constructions and the
  parent's separate `derived_homEquiv` and `composition_comparison` clauses;
  neither includes this item's resolution and K-injective normalization clauses.
  They were read to check orientation; the parent theorem module is not imported.

Validation: every compile uses scompile.py. Early elaboration exposed the namespace
of `IsKInjective` on a mapped HomologicalComplex; it is now fully qualified.
The final warning-only formatting defect in the generated docstring was removed.
Final scompile.py passes both sandbox and final-module checks with no warnings
(29.4 seconds and 30.7 seconds, respectively). Delivery preflight is run next.

## Second reading by N9

No independent second worker was launched, as instructed by the dispatcher brief.
The maintainer performs the independent mathematical review. A final in-thread
reread matched each conjunct against the node and its eight proof steps, checked
all functor directions in the representative squares and the unit/counit formulas,
and retained the actual geometric compositor and its conjugate right mate.
