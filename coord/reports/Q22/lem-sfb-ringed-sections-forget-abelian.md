## Worker report

The module `Sheaf.CategoryTheory.Sites.RingedSectionsForgetAbelian` states
`CategoryTheory.RingedSectionsForgetAbelian.ringedSectionsForgetAbelian`, with its
proof entirely `sorry`. The four helper abbreviations/definitions contain real
functor and natural-transformation data. They expose evaluation and the actual
presheaf restriction maps for the comparison in this node; they introduce no
independent mathematical notion. No new node, dependency repair, or statement
correction is needed.

Clause-by-clause correspondence:

- A site small in the coefficient universe is `{C : Type u} [SmallCategory C]`
  with `J : GrothendieckTopology C`. Coefficient rings, module sections and abelian
  groups all have universe `u`. The explicit independent derived Hom universes
  `w`, `z`, `t` implement def-weil-size-convention. Sheafification and abelianness
  are inferred from the small-site APIs, not additional mathematical hypotheses.
- The commutative ring sheaf is `B : Sheaf J CommRingCat.{u}`. `rings B` is precisely
  its image under `sheafCompose J (forget₂ CommRingCat RingCat)`, without changing
  its section rings or topology. Modules are the recorded `ringedSiteModules`.
- The three `HasDerivedCategory` binders select ordinary localizations for module
  sheaves, abelian sheaves, and abelian groups. The formulas use integer-indexed
  `CochainComplex` and the K-injective `rightDerivedFunctor`, with no boundedness.
- `K_ab` is `(SheafOfModules.toSheaf (rings B)).mapDerivedCategory.obj K`.
  This is exact termwise forgetting, not its possibly different right derived
  functor. The localization factor `mapDerivedCategoryFactors` fixes the
  identification on every complex.
- For every object `U`, `e U` is a natural isomorphism from the recorded
  `UnboundedSectionsLocalization.derivedEvaluation (rings B) U` to exact derived
  forgetting followed by `(abelianEvaluation J U).rightDerivedFunctor`. Thus its
  component gives the claimed isomorphism in `D(Ab)` for every derived `K`.
  Being a natural isomorphism states naturality for all derived morphisms in K.
- Sections mean derived evaluation, using the node's expressly permitted first
  interpretation. The public dependency
  `UnboundedSectionsLocalization.unboundedSectionsLocalization` already identifies
  this very functor with localized evaluation at `Over.mk (𝟙 U)`, with the literal
  section-complex identity. Its `derivedEvaluation` is reused here, so no second
  localization comparison is introduced or assumed.
- The first conjunct quantifies over every module K-injective `I`, every abelian
  K-injective `A`, and every quasi-isomorphism `a : I_ab ⟶ A`. Its equation says:
  comparison, then the canonical exact-forgetting factor, then `RΓ(U,Q(a))`,
  then the K-injective computation on A, equals the module K-injective computation
  on I followed by `Q.map (Γ(U,a))`. This is precisely the representative formula
  with the canonical resolution identifications included. There is no assumption
  that `I_ab` is K-injective, nor that its terms are injective.
- The second conjunct is the actual derived restriction square for every
  `f : V ⟶ U` and derived K. `abelianRestriction J f` is obtained from the
  evaluation functor's map of `f.op`, hence is exactly each sheaf's restriction
  along f. `moduleRestriction B f` is its whiskering with the existing forgetful
  functor; it has the same literal restrictions. `rightDerivedFunctorNatTrans`
  derives those transformations, so these are actual restriction maps, not
  arbitrary maps chosen to make a square commute.
- The existential natural isomorphism is tied to the canonical comparison by its
  formula for every K-injective and every replacement. Every derived object has
  a K-injective representative, so this normalization leaves no arbitrary
  comparison on other objects. Definitions make no choice from a mere existence.

Dependency declarations read and used:

- def-weil-size-convention is the recorded metatheoretic convention, rendered by
  explicit universes; it has no module or mathematical definiendum.
- `Sheaf.CategoryTheory.SiteCoveringAxioms` supplies
  `CategoryTheory.Precoverage.IsSiteForCoverings`; as its record specifies,
  the other components use Mathlib `GrothendieckTopology` and `Sheaf`.
  This statement is at the topology/sheaf level and imposes no new precoverage.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`,
  transparently uses the Mathlib sheaf-of-modules category.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, gives the ordinary unbounded category.
- `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses`,
  `CategoryTheory.ringedSiteZerothHypercohomologyOfUniverses`, uses the same
  K-injective total right derived sections, composed with H⁰. This node needs
  total derived evaluation rather than only H⁰, so reuses the existing
  `UnboundedSectionsLocalization.derivedEvaluation` interface.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`,
  `SheafOfModules.overFunctor`, `over`, `Hom.over`, `overMap`, `overFunctorMap`,
  and Mathlib `GrothendieckTopology.over`, `Sheaf.over`, are the existing
  sectionwise slice constructions used in the imported localization theorem.
- Proof imports follow all recorded proof dependencies: Mathlib `constantSheaf`
  and `SheafOfModules.restrictScalars`;
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`
  in `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`;
  `CategoryTheory.isKInjective_restrict_localized` in
  `WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized`;
  `CategoryTheory.CoefficientDerivedSections.derivedSectionsScalarCoherence` in
  `Sheaf.CategoryTheory.DerivedSectionsScalarCoherence`; and the localization
  theorem above. Their source signatures and docstrings were read. No import
  cycle was found or omitted.
- Supporting existing APIs are Mathlib `SheafOfModules.toSheaf`, its additive and
  finite-limit instances; the upstream finite-colimit instance in
  `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`;
  Mathlib `mapDerivedCategory` and `mapDerivedCategoryFactors`; upstream
  `Functor.rightDerivedFunctorObjQIso` and `rightDerivedFunctorNatTrans`.

Source verification: read `literature/stacks-project/sites-cohomology.tex`,
lemma-modules-abelian-unbounded, lines 4453–4547 (Tag 0D6J). Part (2) and the
explicit Gamma(U,a) proof formula are exactly the item. Part (1) supplies the
scalar-sections argument on the slice. The theorem docstring carries all four
DAG proof steps, including integer coefficients, exact slice restriction,
K-injective resolutions, scalar coherence, sectionwise localization, and
restriction naturality.

Edge cases checked: zero complex; zero coefficient ring (only zero modules);
integer coefficients (forgetting is the canonical integer-module identification);
empty site (the object-indexed claims are vacuous); objects with empty covering
families (no nonemptiness assumption); identity arrows and arbitrary restriction
arrows (literally the presheaf maps); complexes unbounded in both directions;
independent localization Hom universes. No flatness, terminal site object,
nonzero ring, enough-points, boundedness or injective-preservation hypothesis is
introduced. No disputed statement or node fault was found.

Searches performed:

- `msearch.py ... leanfinder`: “For a small ringed site unbounded derived sections
  of modules agree naturally with derived sections of the underlying abelian
  sheaf complex”. Eight hits: sections/evaluation APIs, `SheafOfModules.instAbelian`,
  `Sheaf.H`, `unitHomEquiv`; no unbounded comparison theorem.
- `msearch.py ... loogle`: `"SheafOfModules", "rightDerivedFunctor"`: zero hits.
- `msearch.py ... grep`:
  `forget.*(derived|hypercohomology)|(derived|hypercohomology).*forget`: zero hits.
- `rg` in `lean/WeilConjectures` for the item id, proposed declaration names,
  and forgetting/derived/sections patterns: no exact statement. Hits concerning
  Weil structures, constant coefficients and pro-étale complexes specialize to
  different coefficient categories or restricted sites.
- `rg` in `lean/Sheaf` found `LeftModuleDerivedEvaluationForget`, which is the
  bounded-below constant-coefficient result and cannot serve this unbounded,
  arbitrary ring-sheaf statement. `UnboundedSectionsLocalization` gives the
  required shared derived evaluation, not the forgetting comparison. The general
  scalar-sections coherence theorem is a proof dependency, not the same statement.
- Proposed namespace/declaration names were also searched in
  `dag/lean_names_upstream.json`; no collision.

Validation: the first compile exposed two unqualified `whiskerLeft` references
and one invalid line break after field-notation punctuation; these were repaired.
The next compile exposed one long-line warning, which was repaired. All compiles
use the prescribed scompile.py wrapper and module-mode header. Final compile and
preflight results are recorded by the delivery wrapper.

## Second reading by Q22

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
