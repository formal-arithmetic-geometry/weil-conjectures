## Worker report

The item is stated by
`AlgebraicGeometry.ProEtale.CondensedRing.profinite_constant_model_relation_mem_hull`
in `Sheaf.Paper.ProfiniteConstantModelRelationHull`. Its only theorem has proof `sorry`.
The two definitions in that module give exactly the admissible classes and their
intersection in the item. `Sheaf.Paper.ProfiniteFiniteConstantLocalModel` supplies the
profinite-slice companion of the constructibility dependency. Both modules contain
real definitions, no proof-bearing choices or hollow data. No natural-language
statement, proof plan, dependency list or inherited statement_change was changed.

Hypothesis and clause correspondence:

- The fixed prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The fixed algebraic closure and finite
  subextensions are the existing `PadicAlgCl` / `PadicAlgCl.FiniteIntermediateField`.
  `hΛ` has exactly the five alternatives: finite discrete rings killed by ℓ^n,
  `continuousMapRingObj ℤ_[ℓ]`, `padicIntegersRingObj ℓ E`,
  `continuousMapRingObj ℚ_[ℓ]`, and `continuousMapRingObj E`. Ring-object
  isomorphisms allow any presentation of the same coefficient ring. The topology
  and all-continuous-functions construction are the existing coefficient objects;
  there is no algebraic-closure coefficient alternative. Finite scalar rings may
  be represented in Type 0 without losing any isomorphism class, as in the already
  recorded supported-image consumer and localizing coefficient convention.
- The abelian coefficient sheaf is `Λ`, with `[MonObj Λ] [IsCommMonObj Λ]`.
  These express the stated commutative condensed ring, not extra finiteness or
  regularity assumptions. Scheme-site pushpull and sections are contextual
  conventions, not objects in the conclusion: their recorded modules are publicly
  imported and no extra scheme variable or sections hypothesis is added.
- `(P : Profinite.{u}) [ExtremallyDisconnected P]` gives compact Hausdorff totally
  disconnected P with open closures of opens. No nonemptiness hypothesis occurs.
  The site is exactly `(coherentTopology Profinite.{u}).over P` on `Over P`,
  namely finite jointly surjective covers. `profiniteCoefficient Λ P` is the
  published abbreviation for the actual `overPullback` of Λ. Its published
  multiplication/unit instances are the images under that monoidal functor.
- The ordinary module category is `Mod (Sheaf ... Ab.{u+1}) (profiniteCoefficient Λ P)`;
  the derived category is `DerivedCategory` of that category. Nothing is completed.
  Site object universe is u+1, morphism universe u, coefficient universe u+1;
  product indices and filtered categories range over `Type (u+1)` in the fixed
  indexing convention, as in `supportedImageGenerationHull`.
- The scalar modules B,C are encoded by internal condensed-point modules with
  `Mod.IsFinitelyPresented Λ B` and `Mod.IsFinitelyPresented Λ C`. This is the
  existing scalar-presentation interface used by `HasFiniteConstantLocalModel`,
  not sheafwise finite presentation after pullback to P. `Mod.finiteFree Λ n`
  is a finite biproduct of regular modules. A map between such modules is a
  matrix of endomorphisms of the regular module, hence a matrix over Λ(*)
  (the terminal one-point profinite space). Taking its cokernel is exactly
  extension from the cokernel scalar module. Conversely, every finite scalar
  presentation supplies this cokernel. Thus these B,C range over precisely the
  scalar models, up to the isomorphisms already allowed by repleteness. This
  also avoids introducing a second constant-module or scalar-extension functor.
- The source and target of `v` are exactly `overPullback ... P |>.mapMod Λ`
  applied to B,C, i.e. their canonical scalar-extension models on Prof/P.
  `v` is any morphism in the module-sheaf category, with no scalar-origin,
  constant-rank, elementary-divisor or field-valuedness constraint.
- `HasFiniteConstantProfiniteLocalModel` requires a covering sieve on the final
  object `Over.mk (𝟙 P)` and permits a different finitely presented point model
  B for every member. Its displayed isomorphisms use the actual monoidal
  restriction `overPullback` on internal module objects. A covering sieve and
  a covering family give the same local-model condition by localizing the
  isomorphisms; these finite jointly surjective sites have finite covering
  refinements. Empty coverings and zero models are allowed.
- `IsProfiniteModelGenerationClass` includes `H.IsTriangulated`, which is
  Mathlib's contains-zero, all-integer-shifts, distinguished-triangle-extension
  predicate, and `H.IsClosedUnderIsomorphisms`. Object properties give full
  subcategories. Retracts are exactly `i ≫ p = 𝟙 K` with H L implying H K.
  Products quantify over every small family K and every limiting fan c;
  `IsLimit c` is the product universal property in the ordinary derived category.
- The generator clause is exactly H of `DerivedCategory.singleFunctor _ 0`
  applied to each `HasFiniteConstantProfiniteLocalModel` F.
- The final clause quantifies over a strict functor D into actual cochain
  complexes, `[SmallCategory I] [IsFiltered I]`, an integer a and every colimiting
  cocone c. `(D.obj i).IsStrictlyGE a` is the common termwise lower bound.
  `DerivedCategory.Q.obj c.pt` is the localization of the colimit complex;
  complex colimits are computed termwise in module sheaves. No filtered
  diagram in the derived category replaces the strict diagram.
- `profiniteModelGenerationHull` is the literal universal intersection over all
  these classes. The conclusion is membership of `(singleFunctor _ 0).obj
  (kernel v)`, with the abelian module-sheaf kernel taken before degree zero.

Dependency interfaces read and used:

- `Sheaf.Paper.LocalizingAdmissibleCoefficients`:
  `IsLocalizingAdmissibleCoefficient` and its five continuous coefficient
  constructors (the additional finite-subextension-valued Qbar case is excluded
  explicitly by the five-way hypothesis).
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `CondensedRing.moduleObjectDerivedPushforward`,
  `CondensedRing.moduleObjectDerivedPullback`, and their imported adjunctions;
  ordinary derived-functor convention retained.
- `Sheaf.Paper.CondensedQcqsPushforwardContinuity`: `condensedModuleSections`,
  the actual module-forgetful evaluation functor; its contextual convention
  does not replace the kernel by a global-section kernel.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`;
  `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
  `def-weil-size-convention` is metatheoretic and is realized by explicit u.
- `Sheaf.Paper.SectionwiseFiniteConstantLocalModel` and its public imports:
  `HasFiniteScalarConstantLocalModel`, `HasFiniteConstantLocalModel` and
  `HasFiniteConstantRingedLocalModel`; the companion below is required for
  their change of site, universe and module-object presentation.
- `Mathlib.CategoryTheory.Triangulated.Subcategory`: `ObjectProperty.IsTriangulated`;
  products: `Fan`, `IsLimit` (the universal version of piObj/Pi.π/Pi.lift);
  `Mathlib.CategoryTheory.Limits.HasLimits`: `Cocone`, `IsColimit`, `colimit`;
  `Mathlib.CategoryTheory.Filtered.Basic`: `IsFiltered`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`;
  `Mathlib.Algebra.Homology.Embedding.CochainComplex`: `singleFunctor`;
  `Mathlib.CategoryTheory.Monoidal.Mod`: `Mod`, its actual module morphisms.
- `Sheaf.Paper.ComponentRelativeProfiniteSite`: `component_relative_profinite_site`,
  the recorded relative site and slice projection; `profiniteCoefficient` and
  its monoidal instances from `Sheaf.AlgebraicGeometry.CondensedLisseEvaluationModel`.
- `WeilConjectures.CategoryTheory.ModuleObjects.Free`:
  `Mod.finiteFree`, `Mod.IsFinitelyPresented`, exactly the finite scalar
  matrix convention already used by the constructibility definition.
- The stated proof dependency
  `Sheaf.CategoryTheory.RingedSiteFreeMatrixScalarExtension` is imported privately;
  its recorded `ringedSiteFreeMatrixScalarExtension` gives actual free-module
  coordinates and scalar-extension normalization. The other four proof nodes
  currently have no Lean record and are not imported or assumed as hypotheses.

Edge cases checked in the statement and definitions: P empty; B or C zero;
zero coefficient rings among finite A; zero and identity maps; finite presentations
of rank zero; arbitrary continuous matrix entries; empty product index (its
product is zero); filtered I remains nonempty by IsFiltered; every integer lower
bound and every integer shift; no common upper bound or completeness imposed.
No counterexample to the specified statement is asserted. The inherited node
review explicitly records the rank-one field annihilator input as an open core;
this stage-2 statement retains that obligation with sorry and copies the actual
accepted five-step proof plan, rather than relying on the obsolete maintenance
note's non-clopen recollement argument. The resolved stage-1 repair note has no
released stage-2 interface defect to repair.

Searches (2026-10-25):

- msearch leanfinder, query: "For an extremally disconnected profinite space the
  kernel of a morphism between finitely presented constant scalar module sheaves
  belongs to the derived hull closed under products and bounded below filtered
  colimits". Eight hits: Condensed AB4/AB4Star/AB5, LightCondensed Grothendieck,
  instAbelianCondensedMod, IsSolid, ofSheafProfinite, ofSheafStonean. None states
  this generation theorem or its hull.
- msearch loogle, query `"Condensed", "kernel"`: zero hits.
- msearch grep, query
  `(profinite|condensed).*(kernel|hull)|(kernel|hull).*(profinite|condensed)`:
  zero hits.
- rg of the item id in lean/WeilConjectures and lean/Sheaf: only the consumer
  SupportedImageBoundedDerivedGeneration's proof docstring, no declaration.
- rg `relationHull|relation_hull|finiteModel|FiniteScalar|scalarModel|profinite.*[Hh]ull|Profinite.*[Hh]ull`
  over lean/Sheaf/Paper and lean/WeilConjectures: nearby finite scalar model
  constructions and supported-image hull, no profinite relation theorem.
  Opened CondensedConstantConstructibility, SectionwiseFiniteConstantLocalModel,
  FiniteConstantRingedLocalModel, FiniteConstantModelResolution,
  CondensedLisseEvaluationModel and SupportedImageBoundedDerivedGeneration.
  Their existing scalar construction and presentation predicate are reused.

Validation: both modules compiled independently in dependency order through
scompile.py, in both sandbox and library modes. The main theorem is the only
new sorry. No local build or repository mutation was performed.

## Dependency modules

`sk-def-sfb-constructible`: its existing general sectionwise interface requires a
small category with the same universe as coefficients, and its internal-module
interface is scheme-specific. Neither can accept the actual profinite slice and
its internal modules. `Sheaf.Paper.ProfiniteFiniteConstantLocalModel` therefore
adds only `HasFiniteConstantProfiniteLocalModel`, the same covering and finite
scalar-presentation condition on Prof/P. It publicly imports the previous
SectionwiseFiniteConstantLocalModel module unchanged, retaining its whole API.
The dependency copy changes only lean, with this explanation in lean.note.
No new DAG definition node is needed: this is a companion presentation of the
existing constructibility notion under §1(B), not a new mathematical notion.

## Second reading by NI

In-thread rereading (the dispatcher explicitly prohibits starting another agent;
no independent-reader claim is made here; the maintainer supplies independent review).
Reopened the item and both module texts after compilation. Checked the five-way
coefficient hypothesis against the corrected list, the ordinary category and
kernel against the internal-module paragraph, and all six closure/generator
clauses against the hull paragraph. The source and target are point presentations
pulled to P while the map v remains arbitrary. The companion predicate has a
covering sieve at the final object, separate point presentations on its members,
and actual module restrictions. Checked the order i ≫ p, the product universe,
strictness and termwise lower bound of the colimit diagram, and localization
only after the colimit. No mismatch or correction found; no inherited natural
language field changed. The open rank-one generation input remains a theorem
obligation, not an assumption or finite-model assertion about the kernel.
