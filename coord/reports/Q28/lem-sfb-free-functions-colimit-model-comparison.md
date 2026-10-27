## Worker report

The module `Sheaf.CategoryTheory.FreeFunctionsColimitModelComparison` states the assigned node.
Its primary theorem is `CategoryTheory.FreeFunctionsColimitModelComparison.comparison_quasiIso`.
All six theorem bodies are `sorry`; helper data are explicit composites of existing constructions.
No node statement, statement dependency, proof, or proof dependency changed. No new node or dependency
module is needed. Existing dependency declarations supply every mathematical notion.

Hypothesis-by-hypothesis and clause-by-clause rendering:

- The small site is `{C : Type u} [SmallCategory C] (J : GrothendieckTopology C)`;
  `[HasFiniteProducts C]` and `[J.Subcanonical]` give exactly the two stated site assumptions.
  This uses the Grothendieck topology encoding of the recorded site convention, not a different
  covering structure. All values and indices are in the common chosen sheaf universe `u`.
- `R : Sheaf J CommRingCat.{u}` is the given commutative ring sheaf. `modules J R`, `ring J R`,
  `hom J R P`, `free J R` and `precomp P` are imported directly from the dependency's recorded
  FreeRepresentableDerivedFunctions module. `modules` transparently uses `ringedSiteModules`.
  These are ordinary R-module sheaves and the specified sheaf Hom out of the free representable.
- `underlying J R` is exactly `SheafOfModules.toSheaf (ring J R)`. The helper is a def with that
  actual value, to avoid expensive repeated unfolding during elaboration; it is no new notion.
  `raw` applies its composite with `sheafToPresheaf J AddCommGrpCat` termwise. `transform J P`
  is exactly `precomp P ⋙ presheafToSheaf J AddCommGrpCat`, namely a t_P, with the recorded a.
- `I : Type u`, `[SmallCategory I]`, `[IsFiltered I]` give the small filtered category. This includes
  its nonemptiness, so no extra nonemptiness hypothesis is added. `M : I ⥤ modules J R` is the
  original diagram; `colimit M` with `colimit.ι M i` is its chosen colimit and coprojections.
- `K` is the supplied diagram of Z-cochain complexes. `s` is the natural transformation from
  M[0], so its naturality is exactly augmentation compatibility along diagram transitions.
  `hs` says every augmentation is a quasi-isomorphism; `hI` says every term is injective;
  `hneg` says it is nonnegative. These are the node's nonnegative injective resolutions without
  replacing them by arbitrarily chosen canonical ones.
- `c : Cocone K` has vertex K∞ and legs k_i. `sLimit` augments the original coefficient colimit
  placed in degree zero. `hsLimit`, `hILimit`, `hnegLimit` give its quasi-isomorphism, injectivity
  and nonnegativity. `hcompat` is precisely s_i ≫ k_i = M[0](colimit.ι_i) ≫ sLimit.
- `comparison J R P c` is the chain map colimit.desc of the H_P-image of the actual cocone.
  No arbitrary arrow or assumed complex lift is supplied. `onComplexes` applies H_P termwise.
- `presheafComparison J R c` is the analogous colimit.desc for ιU applied termwise.
  On the supplied module-injective resolutions this computes the stated derived δ:
  Stacks 03FD makes UI^n ι-acyclic; the normalized acyclic-resolution comparison identifies
  Q(ιUI) with Rι(UM[0]), naturally in every augmentation-compatible chain map. Thus the
  cocone legs are exactly Rι of the original underlying module coprojections. Both the source
  and target of δ are represented by these explicit compatible complexes; the node expressly
  defines derived filtered colimits as localization of such termwise colimits. The hypothesis
  `hδ : IsIso (DerivedCategory.Q.map (presheafComparison J R c))` is therefore δ invertible,
  not an additional acyclicity, finite-cover or continuity assumption.
- `[HasDerivedCategory.{wA} ...]`, `[HasDerivedCategory.{wM} ...]` and
  `[HasDerivedCategory.{wP} ...]` supply the chosen localizations in the size convention, with
  independent explicit morphism universes. There is no extra equality of universes imposed.
- The two conclusion clauses are `QuasiIso (comparison ...)` and `IsIso (DerivedCategory.Q.map
  (comparison ...))`, in the ordinary unbounded derived category of module sheaves.
- `comparison_homology` is the requested precise normalization: H^q(Uc) followed by the target
  isomorphism equals the source isomorphism followed by `transform.map (cohomologyComparison ...)`.
  The latter map is the colimit-desc arrow on cohomology of the presheaf resolution cocone,
  hence the required colim h^q(UM_i) → h^q(UM∞). `presheafComparison_homology` separately fixes
  its identification with H^q(δ) using the canonical exact-colimit isomorphism.
- `evaluation` takes the θ supplied by `free_representable_derived_functions_model` and its
  prescribed generator formula, then uses that module's `sheafEvaluationIso` (counit of a ⊣ ι).
  `evaluationComplex` applies this UNDERIVED natural isomorphism termwise. It does not choose a
  lift of an isomorphism in D. On an injective resolution, compose it with any compatible map
  UI → T to an abelian injective resolution. By the dependency's actual `comparisonMap`
  definition this composite is exactly the given canonical derived-model isomorphism.
  Applying cohomology and the exact functor a t_P thus gives the stated `targetHomologyIso`.
  The source uses only canonical colimit transport followed by cohomology and exact-colimit
  transport. It consequently uses the same derived-model cohomology identifications, not merely
  an existential isomorphism between the right objects. No abelian-resolution DIAGRAM is assumed.
- `cohomologyComparison_negative` asserts that both source and target of the presheaf cohomology
  comparison are zero for q < 0 on the supplied nonnegative diagrams. The displayed isomorphisms
  give the same vanishing for H_P. The theorem includes every negative integer and q=0 remains
  in the normalization and criterion, as required.
- All resolution and cocone arguments are universally quantified, giving every compatible
  choice. `comparison_naturality` records the exact coefficient square for EVERY compatible
  chain lift; taking coefficient identity and changed resolutions includes choice independence.
  `comparison_parameterNaturality` records contravariance along every P′ → P, with
  `parameterMap` the actual precomposition by `(free J R).map f`. Generator evaluation of the
  recorded model identifies it with precomposition of presheaves along 1 × f. The canonical
  isomorphisms used above are natural functor maps, so the same squares normalize cohomology.
- No finite-cover, projectivity, discrete-ring, cohomological-dimension or unconditional
  Rι-filtered-colimit assertion occurs.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.FreeRepresentableDerivedFunctions`: `ring`, `modules`, `free`,
  `hom`, `homAdditive`, `precomp`, `sections`, `homAbelian`, `sheafEvaluationIso`,
  `comparisonMap`, `free_representable_derived_functions_model`, and the coefficient/parameter
  maps and normalization of that theorem. Its full source and docstrings were read.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, through
  the recorded `modules`; `Sheaf.CategoryTheory.SiteCoveringAxioms` supplies the recorded
  site convention, encoded here by the associated Grothendieck topology.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`: `SheafOfModules.homObj`
  and `homFunctor`, used through the recorded H_P, including its genuine free-module map.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`, `sheafToPresheaf`,
  `sheafificationAdjunction`, through the recorded model and the actual `transform`.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `colimit`, `colimit.desc`, `colimit.ι`,
  `Cocone`, `HasColimit.isoOfNatIso`; `Limits.Preserves.Limits.preservesColimitIso` fixes
  the coprojection normalization of all colimit identifications.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`: `Injective`;
  `...Injective.Resolution`: `InjectiveResolution`; `...Abelian.Injective.Extend` supplies
  the recorded integer-cochain interface used by the model. The consumer accepts arbitrary
  nonnegative resolutions directly rather than replacing them by one chosen resolution.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`, `HasDerivedCategory`;
  `HomologicalComplex.homologyFunctor`, `homologyMap`, `QuasiIso` are the recorded cohomology
  and quasi-isomorphism notions, with ordinary integer cochain complexes.
- `WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso`:
  `Functor.mapHomologicalComplexHomologyIso`, the exact-functor cohomology comparison.
- `WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits`: the recorded
  `HomologicalComplex` instance preserving exact colimits under homology, used in
  `sourceCohomologyIso` and the presheaf normalization equation.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `SheafOfModules.preservesColimitsOfShape_toSheaf`, whose actual instance data are reused.
  `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful` is a proof dependency;
  its full exactness/colimit statement was read. All other recorded Mathlib proof leaves
  are imported with proof-only imports as required; the genuine unstated proof dependency
  lem-sfb-module-resolution-derived-presheaf-comparison has no module to import.

Edge cases checked before writing: the zero ring and zero coefficient diagrams impose no
nonzero assumption; terminal filtered index and identity coefficient maps are allowed. An
empty index category is correctly excluded by IsFiltered itself. Empty site is excluded
by finite products (a terminal object), already a source hypothesis. Every P, including a
terminal parameter, is allowed. Arbitrary negative q and q=0 are covered. Different module
and abelian injective resolutions are allowed; UI is not assumed abelian-injective. Sites
whose Rι does not preserve filtered colimits are allowed: hδ is an explicit conditional
hypothesis. No inappropriate presheaf/sheaf colimit equality is used.

Searches for an existing statement:

- `msearch.py leanfinder`: “Filtered colimit of internal Hom injective resolutions for free
  representable module sheaves compared with derived inclusion into presheaves”. It returned
  free-sheaf and sheafification adjunction helpers, no normalized derived-colimit criterion.
- `msearch.py loogle`: `"homologyFunctor", "colim"`. Result:
  `instPreservesHomologyFunctorAddCommGrpCatColim`, an ingredient only.
- `msearch.py grep`: `(colimit|[Cc]olim).*(homology|[Qq]uasi[Ii]so)` in Algebra/Homology.
  Results were local cohomology, short-complex exactness and preservation of homology,
  not the node's free-representable model comparison.
- `msearch.py leansearch`: “Filtered colimit canonical comparison for sheaf internal Hom of
  free representable module and derived presheaf inclusion”. Results include sheaf colimit
  existence, free Hom equivalences, and `Sheaf.hasFilteredColimitsOfSize`; no exact match.
- `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for free-representable/derived-functions
  and colimit comparison patterns found the recorded model and the downstream profinite
  specialization, which needs this general-site criterion. Neither is this statement.
  Searching the item id in upstream Lean found no match. The new namespace and declaration
  names have no existing occurrence. The source places read are sites-cohomology.tex
  section-internal-hom (08J7) and sites.tex lemma-sheafification-exact (00WJ).

No STATEMENT-DISPUTED flag or node correction is needed.

## Validation

Compilation uses scompile.py only, including module-mode probes. Explicit `autoImplicit false`
ensures every variable and universe is bound. All definitions contain real data; no theorem
has a proof beyond sorry. Final compile and delivery preflight results are recorded below.

## Second reading by Q28

(Written by the maintainer's second reader NT-cc review, replacing the dispatcher-wording
placeholder; the Lean and node records are unchanged.)

Node clauses and their Lean rendering:

1. Small subcanonical site with finite products, common universe: `C : Type u`,
   `[SmallCategory C]`, `J`, `[HasFiniteProducts C]`, `[J.Subcanonical]`; same encoding as
   the recorded model `FreeRepresentableDerivedFunctions`. Correct, nothing stronger.
2. R a commutative ring sheaf, ordinary module sheaves: `R : Sheaf J CommRingCat.{u}`,
   `modules J R` (= `ringedSiteModules`, def-weil-sheaf-of-modules-category). Correct.
3. U, ι, a, t_P: `underlying` = `SheafOfModules.toSheaf (ring J R)`, `sheafToPresheaf`,
   `presheafToSheaf`, `precomp P` (whiskering by (−×P)ᵒᵖ). `transform P` = a ∘ t_P. Correct.
4. H_P = Hom_R(R[P], −): recorded `hom J R P` (SheafOfModules.homFunctor on `free J R P`);
   `parameterMap` precomposes with `(free J R).map f`. Correct.
5. Small filtered I, M : I ⥤ Mod(R), colimit M∞ with coprojections: `I : Type u`,
   `[SmallCategory I] [IsFiltered I]`, `colimit M`, `colimit.ι M i`. Correct.
6. Compatible diagram of nonnegative injective resolutions M_i[0] → K_i, resolution of M∞,
   cocone k_i with augmentation compatibility: `K`, natural `s` (transition compatibility),
   `hs`, `hI`, `hneg`, `c : Cocone K`, `sLimit`, `hsLimit`, `hILimit`, `hnegLimit`, `hcompat`
   (s_i ≫ k_i = M[0](ι_i) ≫ sLimit). Arbitrary choices, universally quantified. Correct.
7. c : colim H_P(K_i) → H_P(K∞): `comparison` = `colimit.desc` of the H_P-image of the cocone. Correct.
8. δ and hypothesis "δ iso in D(PAb)": `hδ : IsIso (Q.map (presheafComparison J R c))`, where
   `presheafComparison` is colimit.desc of ιU applied to the cocone. The node fixes derived
   filtered colimits as localizations of compatible termwise colimits; by Stacks 03FD the terms
   UK_i^n are ι-acyclic, and the normalized comparison c_r of
   lem-sfb-module-resolution-derived-presheaf-comparison (natural for augmentation-compatible
   lifts, a proof dependency without Lean record) identifies the diagram Q(ιUK_i) with
   Rι(UM_i[0]) and the legs Q(ιUk_i) with Rι(Um_i[0]) (via hcompat). So hδ is exactly δ
   invertible, neither weaker nor stronger. Same representative style as the recorded model,
   which also has no Rι functor. Accepted.
9. Conclusions: `QuasiIso (comparison …) ∧ IsIso (DerivedCategory.Q.map (comparison …))` in
   D(Mod(R)). Correct; both clauses, nothing weaker.
10. Normalization H^q(Uc) ≅ a t_P(colim h^q(UM_i) → h^q(UM∞)), arrow = H^q(δ), induced by
   the coprojections: `comparison_homology` (with `sourceCohomologyIso`, `targetHomologyIso`,
   `cohomologyComparison`) and `presheafComparison_homology`. I checked both equations after
   each coprojection: naturality of the termwise evaluation, `preservesColimitIso` legs, and
   naturality of `mapHomologicalComplexHomologyIso`; both are true. The target identification
   is H^q of the termwise generator evaluation (from `sheafEvaluationIso` of the model's θ,
   which the model pins by the generator formula, so the `.choose` is canonical). Composed with
   H^q(a t_P ι b) for a compatible b : UK → T it is H^q of the model's E, because
   `comparisonMap` is defined as that composite. So these are the model's derived isomorphisms
   on cohomology, not an assumed complex lift. Correct.
11. Negative degrees zero: `cohomologyComparison_negative`. Correct.
12. Naturality in compatible coefficient maps and choice independence, contravariance in P:
   `comparison_naturality` (every compatible chain lift, including the identity coefficient
   map) and `comparison_parameterNaturality`. The canonical identifications are natural
   transformations, so the cohomology normalization inherits these squares. Correct.
13. No finite-cover, cohomological-dimension or unconditional Rι-colimit assumption. Correct.

Edge cases: one-object I; R = 0; terminal P; q < 0 and q = 0; UK_i not abelian-injective
(allowed); sites where Rι does not commute with filtered colimits (hδ is a real hypothesis).
Universes: everything is in u as the size convention requires, and the derived-category Hom
universes wA, wM, wP are free.

Advisory (no change): the section instances `[HasDerivedCategory.{wA} (Sheaf J Ab)]` and
`[J.Subcanonical]` are auto-included in later declarations that do not use them. Any citer
can supply them, and the node assumes subcanonicity.

Searches: none duplicates this statement. rg of lean/Sheaf and lean/WeilConjectures for
free-representable colimit / quasi-iso comparison patterns found only the recorded model and
the downstream profinite node. In Mathlib, `instPreservesHomologyFunctorAddCommGrpCatColim`
is an ingredient only. Records: the node differs from side-live only by `lean`, and
`lean.statement` matches the file verbatim. stmt_deps cover every notion used. Definitions
are canonical composites with real data, theorem bodies are `sorry`, and docstrings carry the
source place, `(blueprint: …)` and the proof steps.

Mismatches found: none. The only change is this section.
