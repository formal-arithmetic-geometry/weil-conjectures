## Worker report

Delivered module: `Sheaf.AlgebraicGeometry.EtaleModuleStalkCohomologyTest`.
All seven public theorems have `sorry` as their entire proofs. No definition,
instance, axiom, or alternative stalk construction is introduced. The node's
statement and proof are unchanged. Its `stmt_deps` retains exactly the nine live definition dependencies. The
upstream `CategoryTheory.GrothendieckTopology.Point.sheafFiber_additive` lemma
is enabled as a local instance, without a theorem statement dependency.

The seven declarations, all in namespace `AlgebraicGeometry.Etale`, jointly state
the node's clauses. The primary record is the final zero-detection equivalence;
`lean.declarations` lists every clause.

Hypothesis and clause correspondence:

- Arbitrary commutative coefficient ring: `(A : Type (u + 1)) [CommRing A]`.
  There is no nonzero-ring, finite-ring, local, Noetherian or characteristic
  assumption. This is the established six-functor coefficient universe.
- Arbitrary scheme and its small étale site: `(T : Scheme.{u})` and
  `T.smallEtaleTopology`. There is no scheme-theoretic finiteness assumption.
- Modules over the constant ring sheaf A_T: the project's recorded
  constant-coefficient encoding is `Sheaf T.smallEtaleTopology
  (ModuleCat.{u + 1} A)`. This is exactly the encoding prescribed in
  `def-weil-pbc-derived-categories`, `WeilConjectures.AlgebraicGeometry.DerivedCategories`,
  and brief-stage2's “Λ-module étale sheaves” convention, as used by the parent
  `lem-sf-etale-stalk-tor-test`. ModuleCat-valued sections have their A-action
  and A-linear restriction maps; the action of the sheafified constant ring is
  its local extension. No new category of coefficient sheaves is defined.
- Geometric point: `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]`
  and `(t : Spec (.of Ω) ⟶ T)`. In the final equivalence Ω and its structures
  are universally quantified, rather than fixed. No point is assumed to exist.
- The stalk with induced A-action is `(pointSmallEtale t).sheafFiber
  (A := ModuleCat.{u + 1} A)`. Its definition is the same colimit diagram as
  `pointedEtaleStalk` in the recorded stalk dependency. Taking that colimit in
  ModuleCat makes both the germ maps and the induced maps A-linear, with the
  action induced from the section actions. No arbitrary map or chosen module
  structure replaces it.
- Stalk exactness is `etaleModuleStalk_exact`: `.Additive`,
  `PreservesFiniteLimits` and `PreservesFiniteColimits`. Between abelian
  categories this is precisely exactness, including short exact sequences.
- Forgetting sheaf-module structures is the actual `sheafCompose` functor for
  `forget₂ (ModuleCat A) AddCommGrpCat`. `etaleModuleForget_preserves_cohomology`
  explicitly gives finite limit preservation (in particular kernels), finite
  colimit preservation (in particular cokernels, hence quotients), image
  isomorphisms for every sheaf morphism, and an isomorphism of cochain-complex
  cohomology functors for every integer degree. The latter is natural in
  complex maps. Exactness also gives the canonical kernel/cokernel and image
  comparisons with their universal-property compatibility; this is not just
  an assertion about underlying groups of objects.
- `moduleForget_preserves_cohomology` gives exactly the corresponding four
  assertions for ordinary modules and `forget₂ (ModuleCat A) AddCommGrpCat`.
  Thus the “forgetting module structures” assertion is covered on both sides
  of the stalk functor.
- Termwise application is the existing `.mapHomologicalComplex (ComplexShape.up ℤ)`.
  `etaleModuleStalk_preserves_quasiIso` states `QuasiIso f → QuasiIso` of its
  image for every map of arbitrary integer-indexed cochain complexes. Its
  `hf : QuasiIso f` is the premise of the preservation assertion.
- The induced functor on full unbounded categories is the existing
  `.mapDerivedCategory`, from `DerivedCategoryModule A T` to
  `DerivedCategory (ModuleCat A)`. `etaleModuleStalk_derived_factors` provides
  the natural representative identification `Q ⋙ D(s) ≅ C(s) ⋙ Q`. In
  particular the functor is induced by the specified termwise stalk, rather
  than an arbitrary functor with isomorphic cohomology objects.
- The displayed cohomology comparison is `etaleModuleStalk_cohomology_iso`:
  `Nonempty (H^i ⋙ s ≅ D(s) ⋙ H^i)`. This is one natural isomorphism of
  functors on the whole derived category, for each point and degree. Its
  component at E is `(H^i E)_t ≅ H^i(E_t)`. Its codomain is ModuleCat A,
  so its morphisms are A-linear, including the inverse.
- The final displayed equivalence is `etaleModuleStalk_cohomology_test`:
  `IsZero (H^i E) ↔ ∀ Ω [Field Ω] [IsAlgClosed Ω] t, IsZero (H^i (D(s_t) E))`.
  `IsZero` is categorical vanishing of these module/sheaf objects. E ranges
  over all of `DerivedCategoryModule A T`, and `i : ℤ` is arbitrary.
- No boundedness, constructibility, finite-generation, or Noetherian binder
  appears. The domain of every complex functor is the full cochain category.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`, `Scheme.Etale`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`;
  the existing sheafification-of-constant-presheaf definition supplies the
  meaning of the constant coefficient ring and sections in the proof plan.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`
  is the generic `SheafOfModules` encoding. Read its full declaration and
  docstring. For this node use the constant-coefficient specialization above,
  as the recorded derived-category interface requires, rather than introduce
  another generic ringed-site category or an incompatible derived category.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; a geometric point is
  the inline morphism specified in `def-weil-geometric-point`.
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`: `pointedEtaleStalkDiagram`,
  `pointedEtaleStalk`, `pointedEtaleGerm`. These are the same pointed-neighbourhood
  colimits underlying `Point.sheafFiber`, whose signature and definition were read.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and its public coefficient
  import: `AlgebraicGeometry.Etale.DerivedCategoryModule`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; no bounded subcategory is used.
- The `mathlib_match` of `def-weil-derived-cohomology-sheaves` is used:
  `DerivedCategory.homologyFunctor`, `DerivedCategory.homologyFunctorFactors`
  in `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`. Its recorded
  specialized `sfModelCohomology` declaration concerns another coefficient
  category; the supplied general Mathlib match already gives this notion.
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`:
  `CategoryTheory.moduleSheaves_colimits_forgetful`, proof dependency (1).
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`:
  `Functor.preservesHomologyOfExact`, `Functor.homologyFunctorIso`;
  `Functor.mapHomologicalComplexHomologyIso` gives the unbounded complex version.
- `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images`:
  `CategoryTheory.PreservesImage.iso`, with its two compatibility equations.
- `Mathlib.CategoryTheory.Sites.Point.Basic` and `.Skyscraper`: existing finite
  limit/finite colimit preservation of `Point.sheafFiber`, as recorded for
  `prop-weil-pbc-geometric-stalks-exact`.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategory`, `Functor.mapDerivedCategoryFactors`.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategoryHomologyFunctorIso`, including its representative
  formula `mapDerivedCategoryHomologyFunctorIso_hom_app_Q`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`:
  `Scheme.isIso_of_isIso_sheafFiber_map`, the existing conservative geometric
  point family. Its lifted fibres are canonically isomorphic to the ordinary
  `pointSmallEtale` fibres, so this does not restrict the final quantifier.
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper`:
  `CategoryTheory.GrothendieckTopology.Point.sheafFiber_additive`, enabled with
  `attribute [local instance]` before the namespace. This upstream lemma supplies
  the additive Prop instance needed by the unbounded derived functor. No tensor
  theorem is imported or added to `stmt_deps`.
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering`:
  `CategoryTheory.sheafCompose_additive`, needed to state the forgetful
  complex-cohomology natural isomorphism without an extra assumption.

Edge cases checked before writing:

- Empty T: there are no geometric-point morphisms, so the right-hand condition
  is vacuous. Every sheaf of modules on the empty étale topos is zero; this is
  compatible with the same conservative-family argument, without Nonempty T.
- Zero ring: all unital A-modules are zero. None of the statements require
  Nontrivial A, and all comparisons and the vanishing test remain meaningful.
- E = 0 and a sheaf placed in any single degree: the comparison specializes to
  zero, respectively the ordinary stalk; no shift or indexing case is lost.
- Arbitrarily unbounded complexes, including zero differentials in every
  degree: degree-i homology uses only the adjacent differentials, so exactness
  suffices without convergence or a bounded resolution.
- A non-flat module, e.g. over Z/4 with multiplication by 2: stalks are exact
  because they are filtered colimits, rather than because coefficients are flat.
- The coefficient category has its established u+1 size, with scheme and
  geometric field in u. No site object/morphism universe equality is imposed.

Searches for an existing statement:

- msearch LeanFinder: “Geometric stalk of an etale sheaf of modules is exact
  commutes with unbounded derived cohomology and detects vanishing”: 8 hits,
  including `DerivedCategory.isGE_Q_obj_iff`, formal étaleness and cohomological
  support results, none stating this node.
- msearch Loogle: `CategoryTheory.GrothendieckTopology.Point.sheafFiber,
  DerivedCategory.homologyFunctor`: 0 hits.
- msearch grep: `sheafFiber.*homology|homology.*sheafFiber|mapDerivedCategory.*homology`:
  0 Mathlib hits.
- msearch LeanSearch: “Geometric stalks of etale module sheaves commute with
  unbounded derived cohomology and jointly detect zero cohomology”: 8 hits,
  mostly `ModuleCat.Tilde` and Zariski module-stalk results, none matching.
- Direct rg in both `lean/WeilConjectures` and `lean/Sheaf` for module/stalk and
  stalk/cohomology combinations found the existing generic exact-functor
  comparison, the additive instance, and nearby specialized results. The
  exact proposed declaration names are absent in both roots and Mathlib.
- Direct rg for this node id in `lean/WeilConjectures` and
  `dag/lean_names_upstream.json` found no existing declaration.
- `GeometricStalkCohomology.lean` concerns abelian coefficients and geometric
  pullback. `EtaleStalkTorTest.lean` proves a Tor-amplitude test; its proof uses
  cohomology comparisons internally but its exported statement is different.
  Neither states all the module exactness, forgetful, derived, and vanishing
  clauses of this node. The overlap with the still-unstated
  `lem-sfb-etale-stalk-constant-complex-exactness` is documented in the item's
  existing maintainer review; this delivery introduces no duplicate definition.

Sources read: local Stacks etale-cohomology.tex at lemma-stalk-exact and
 theorem-exactness-stalks, sites-modules.tex at lemma-abelian and
 lemma-stalk-exact-modules (including the preceding scalar-action construction),
and sites-cohomology.tex at lemma-tor-amplitude-stalk. All seven proof docstrings
name the item, the source and the relevant steps of its six-step proof.

No statement correction, disputed statement, new node, or dependency module.

## Second reading by Q44

A separate pass through the final module and node checked the ring, scheme,
site, geometric-point and integer binders; the module-valued source category;
both forgetful functors; exactness; quasi-isomorphism preservation; the
representative factorization; naturality and A-linearity; and both directions
of zero detection. The component of the natural isomorphism is in the node's
stalk-of-cohomology to cohomology-of-stalk direction. All seven declarations
are listed in the node record. No file-local notation, implicit universe,
choice of canonical data, extra finiteness hypothesis or data-valued sorry
occurs. One 103-character line was wrapped after the first compiler run.
This is a self-check; the maintainer supplies the independent delivery review
specified by the dispatcher, which forbids starting another worker.

## Validation

Every compile uses the prescribed `scompile.py` wrapper, compiling this module
separately against the live published library. The first complete statement
compile succeeded but reported one long-line warning; the line was repaired.
The final compile and the required delivery dry run are recorded below.

Final `scompile.py`: clean sandbox check (17.5 s) and clean real-module check
(13.5 s), both within the 60-second limit. No errors or warnings.
`deliver2.py --no-push`: OK; server preflight and per-file compilation passed.

## Returned delivery repair

The independent review of immutable head `fa81cbfe6594` returned H2: the added
`lem-sfb-etale-derived-tensor-stalk` statement dependency was used only for its
exported additive Prop instance, not for its theorem conclusion. Removed that
dependency, restoring exactly the nine live definition statement dependencies.
Replaced the public import of `Sheaf.AlgebraicGeometry.EtaleDerivedTensorStalk`
with `WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper` and enabled
`CategoryTheory.GrothendieckTopology.Point.sheafFiber_additive` as a local
instance before the namespace, exactly as requested. Updated `lean.note` and
this report. No statement, proof plan, declaration signature or docstring changed.

Compared the retained packet against the current read clone: before repair, only
`lean` and the extra `stmt_deps` entry differed; after repair, only `lean` differs.
The initial saved-packet dry run passed as commit `9e60aac8b4c`. This did not
resolve the mathematical review return; the import and dependency repairs above
are the concrete changes for the new delivery.

The review's advisory about pinning comparison isomorphisms is recorded for
the proving stage. The requested repair preserves the seven independently
accepted theorem statements and their natural A-linear comparisons.

Repair self-check: the node differs from the current live node only in `lean`;
all nine definition `stmt_deps` match exactly, and the primary signature still
matches `lean.statement` verbatim. The seven theorem bodies remain `sorry`
only, `autoImplicit false` remains enabled, and every Lean line is within
100 characters. The local instance attribute is the specific repair required
by the independent reviewer; it uses the upstream additive proof.

Repaired `scompile.py`: clean sandbox check (12.1 s) and clean real-module check
(8.9 s), with no errors or warnings.

Repaired `deliver2.py --no-push`: OK, commit `0279c7eda3f`; server preflight
and per-file compilation passed.
