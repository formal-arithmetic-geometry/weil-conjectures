## Worker report

This is an `existing: true` convention bundle. No module, definition, theorem or proof is
added. The primary binding is
`AlgebraicGeometry.ProEtale.IsClassicalModuleComplex` in
`Sheaf.SixFunctors.ClassicalDefinition`; its signature is copied verbatim into `lean.statement`.
The other existing declarations in `lean.declarations` record publicly visible interfaces of
that module. The unchanged statement-dependency records cover the remaining conventions;
their modules are listed below and were checked together in the compiler probe.
The node's statement, dependencies, proof fields and all other fields are unchanged.

I read the complete node, all fifteen direct statement-dependency statements and their
recorded interfaces, the declarations and docstrings in their owning sources, and the current
blueprint `main-20261015/blueprint/sec-proper-base-change/sk-def-pbc-conventions/_section.md`.
I also read Stacks `sites-cohomology.tex`, lemma-cohomology-modules-abelian-agree, Tag 03FD
(tag verified in `literature/stacks-project/tags/tags`).

Clause correspondence:

1. Arbitrary schemes are `AlgebraicGeometry.Scheme.{u}`, with no Noetherian, separated,
   quasi-compact or characteristic hypothesis. The ring is an arbitrary
   `Λ : Type (u + 1)` with `[CommRing Λ]`; no topology on Λ is supplied, so these are
   discrete constant coefficients. Given any scheme and coefficient sizes, a common larger
   universe permits these declarations; this introduces no mathematical ring restriction.
2. The small pro-étale site is `AlgebraicGeometry.Scheme.ProEt T` with
   `AlgebraicGeometry.Scheme.ProEt.topology T`, the recorded Mathlib leaf `sk-def-pe-site`.
   The ring sheaf is
   `(constantSheaf (Scheme.ProEt.topology T) RingCat.{u + 1}).obj (RingCat.of Λ)`.
   Its modules are `CategoryTheory.ringedSiteModules.{u + 1}` of this ring, definitionally
   `SheafOfModules.{u + 1}`. This uses the actual recorded general-ringed-site dependency.
3. On that module category, `DerivedCategory` is the recorded localization and
   `DerivedCategory.Plus` is its bounded below full subcategory. The classical condition on
   `K : DerivedCategory.Plus ...` is exactly
   `AlgebraicGeometry.ProEtale.IsClassicalModuleComplex (DerivedCategory.Plus.ι.obj K)`.
   The primary declaration unfolds to `∀ q : ℤ, IsClassicalModuleSheaf (H^q K)`.
   `IsClassicalModuleSheaf` uses the canonical affine-presentation continuity maps through
   its underlying sheaf of sets, as recorded by `sk-def-pe-classical-definition`. For module
   maps bijectivity of the underlying map is precisely invertibility. No continuity map,
   category, or classicality predicate is defined again. The existing predicate is general
   in R; its specialization here is to exactly the constant ring above. Its
   `HasDerivedCategory` parameter is a choice of localization, supplied by the concrete
   `HasDerivedCategory.standard`, rather than an added mathematical hypothesis.
4. The intermediate site is `T.smallEtaleTopology`; abelian sheaves are
   `Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}`. Constant-coefficient module sheaves
   use the recorded étale encoding `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`.
   This is the encoding in `def-weil-pbc-derived-categories` and in the comparison theorem;
   `moduleSheaf_constantRing_equivalence` identifies it with modules over the constant
   ring sheaf, and the existing module-cohomology module expressly uses that equivalence.
   `AlgebraicGeometry.Etale.DerivedCategoryModule Λ T` names their derived category;
   `DerivedCategory.Plus` gives exactly D+. The phrase about where curve and Chow
   calculations are made is an ambient-category convention, with no additional assertion.
5. For `f : S ⟶ T`, `Scheme.etaleSetPullback f` goes from sheaves on T to sheaves on S.
   `AlgebraicGeometry.etaleSetInverseImage_exact f` gives the adjunction, finite-limit and
   finite-colimit preservation on sets. On abelian and ModuleCat sheaves the corresponding
   functor is `AlgebraicGeometry.Etale.upperStar A f`, with A respectively AddCommGrpCat
   and ModuleCat Λ. On D+ it is `(Etale.upperStar A f).mapDerivedCategoryPlus`.
   This is the recorded `def-weil-pbc-derived-inverse-image` declaration, induced termwise
   by an exact functor, with no resolution. Source and target were checked by the compiler.
6. Exactness and agreement with module pullback over constant rings are exactly
   `AlgebraicGeometry.etaleInverseImageModulesExact S T f (CommRingCat.of Λ)`:
   its c is the adjoint constant-ring comparison, LM is additive and preserves finite
   limits and finite colimits, e identifies its underlying abelian inverse image, and d
   is the canonical natural extension-of-scalars comparison with the specified tensor
   formula. Its adjunction, unit and counit clauses supply the stated module functor.
   Thus this binding uses the recorded dependency, not an arbitrary isomorphic functor.
7. Direct image is `AlgebraicGeometry.Etale.lowerStar A f`, given by sections on fibre
   products. Ru_* is `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus A f`, with the
   displayed source D+(S) and target D+(T). The former is in the recorded
   `UpperLowerStar.Defs`; the latter's actual owning module is
   `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`, which was also read
   and used in the module-mode compile probe. No dependency record is replaced.
8. Torsion of an abelian sheaf is `CategoryTheory.Sheaf.IsTorsion`, locally finite order
   on a covering sieve. For module derived objects,
   `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology` applies that predicate after
   forgetting scalars to every cohomology sheaf. This is exactly underlying abelian
   torsion, without a uniform annihilator.
9. Properness is `AlgebraicGeometry.IsProper f`, extending `IsSeparated f`,
   `UniversallyClosed f` and `LocallyOfFiniteType f`. This is the only clause of
   `sk-def-conv` used here. There is no invertibility, characteristic exclusion, finite
   ring condition or selected prime among the binders of these conventions. In
   particular a torsion prime may equal the residue characteristic. The return of the
   introductory ell-adic convention describes the later theory, not an extra hypothesis
   on this section or an extra proposition in this definition node.
10. The final paragraph is exactly the already recorded
    `AlgebraicGeometry.Etale.module_cohomology_conventions Λ T`: conjunct one is acyclicity
    of every injective module sheaf after forgetting, on every U, for q > 0; conjunct two
    is invertibility of `moduleEvaluationForgetComparison Λ T U q`, the right-derived
    identity on sections. Conjunct three is invertibility of the canonical higher
    direct-image comparison for all f, F, q. Conjunct four gives the canonical derived
    direct-image comparison at every K in D+, so it includes the full derived assertion,
    not just its cohomology. No preservation of injectives by forgetting is assumed.
    The theorem's docstring follows the acyclicity argument of 03FD and the canonical
    derived comparison. These are existing theorem statements, not new stage-2 proofs.

Dependency declarations and owning modules (all read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`: `DerivedCategory.Plus`, `Plus.ι`.
- `Sheaf.SixFunctors.ClassicalDefinition`: `ProEtale.IsClassicalModuleSheaf` and
  `ProEtale.IsClassicalModuleComplex` (under `AlgebraicGeometry`).
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: `Scheme.etaleSetPullback` and the
  publicly imported `CategoryTheory.Sheaf.IsTorsion`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: `Etale.DerivedCategoryModule`,
  `Etale.DerivedCategory.torsionCohomology` (under `AlgebraicGeometry`).
- `WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageExact`:
  `AlgebraicGeometry.etaleSetInverseImage_exact`.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategoryPlus`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `AlgebraicGeometry.etaleInverseImageModulesExact`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.upperStar`, `AlgebraicGeometry.Etale.lowerStar`.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`:
  `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Sheaf.AlgebraicGeometry.ModuleCohomologyConventions`:
  `AlgebraicGeometry.Etale.moduleEvaluationForgetComparison` and
  `AlgebraicGeometry.Etale.module_cohomology_conventions`.

Edge cases checked before binding: zero ring and zero complexes; the empty scheme; identity
and arbitrary scheme maps; non-quasi-compact schemes; Λ = Z, Q, Z/n and F_p in residue
characteristic p. None is excluded by the selected signatures. On a countable disjoint union,
Q/Z is torsion without sections having a common annihilator; the selected local torsion
predicate allows it. An injective F_p-module need not be injective as an abelian group;
the comparison theorem uses only acyclicity. Cohomology classicality quantifies over all
integer degrees, and bounded below is supplied separately by Plus, with no upper bound.

Searches, all through the prescribed msearch wrapper or read-only source searches:

- LeanFinder: "Classical bounded below derived category of pro etale sheaves with discrete
  commutative coefficients and etale inverse image and cohomology conventions": eight
  results, including `Sheaf.H`, small étale topology and unrelated condensed definitions;
  no new all-in-one convention object.
- Loogle: `DerivedCategory.Plus, SheafOfModules`: zero results.
- Mathlib grep: `ClassicalPlus|IsClassicalModuleComplex|module_cohomology_conventions`:
  zero results. These project notions are not Mathlib definitions.
- LeanSearch: "Classical complexes of pro etale module sheaves and exact inverse image with
  constant coefficients": eight results, including `constantSheaf` and IsConstant
  interfaces. These supply the constant-sheaf convention but not a new convention object.
- `rg` in lean/Sheaf for classical Plus and convention names found the existing
  ClassicalDefinition, ClassicalDerivedDefinitions and ModuleCohomologyConventions modules.
  ClassicalDerivedDefinitions uses the alternative ModuleCat encoding; the primary binding
  deliberately retains the actual recorded `SheafOfModules` classicality declaration.
- `rg` in lean/WeilConjectures for these notions and direct inspection found the recorded
  ÉtaleSheaves, DerivedCategories, inverse-image and direct-image APIs.
  `grep -rn sk-def-pbc-conventions lean/WeilConjectures` returned no item-labelled declaration.
  The absence of an item label does not justify copying its already existing components.

No missing notion, disputed statement, statement correction or dependency repair is needed.

## Second reading by Q09

I made a separate second pass over the unchanged node, its blueprint paragraph and the
existing declaration sources. This is a second reading by this worker; the maintainer's
independent review is still required. I checked the correspondence numbered above against
every sentence, not only the primary signature. The primary declaration alone is not
claimed to assert the whole bundle: the unchanged dependency records
cover the other clauses, just as the existing sk-def-conv convention bundle does.

Two interface details were caught and addressed during reading. The recorded direct-image
module gives lowerStar but the bounded-below derived declaration lives in
Derived.UpperLowerStarCoherence, so the report and probe use its actual owning module.
Second, the generic pro-étale SheafOfModules category does not automatically infer a chosen
HasDerivedCategory. The probe explicitly selects Mathlib's standard localization. No
hypothesis or universe equality is added to the node; its recorded classicality declaration
already accepts any chosen localization. The probe checks the precise constant-ring
specialization followed by the Plus inclusion, alongside the ModuleCat étale functors and
cohomology theorem. There is no finite coefficient specialization, and no assumption that
the forgetful functor preserves injectives.

Validation: the module-mode `scompile.py` probe passed (12.0 s, no warning or error),
including the exact constant-ring D+ classicality expression. The first delivery dry run
found that declarations from other owning modules cannot be listed as exports of the
primary module. I restricted lean.declarations to interfaces actually exported there;
all other clauses retain their existing dependency records and report mappings. No
module or mathematical statement was changed to resolve this packaging issue.
