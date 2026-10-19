## Worker report

The module `lean/Sheaf/AlgebraicGeometry/ClosedSupportHom.lean` states
`AlgebraicGeometry.Etale.closedSupportHom`, with `sorry` as its whole proof.
It states the node's natural isomorphism in the ordinary derived category of A-modules.
There are no definitions, added nodes, dependency modules or statement corrections.

Hypothesis and clause correspondence:

- Coefficients: `(A : Type (u + 1)) [CommRing A]`, using the commutative-ring convention
  expressly recalled in the node's first proof step. No torsion, finiteness or field
  assumption is imposed.
- Schemes: `{D V T : Scheme.{u}}`, with arbitrary explicit universe `u`.
- Closed immersion: `(i : D ⟶ T) [IsClosedImmersion i]`.
- Complementary open immersion: `(v : V ⟶ T) [IsOpenImmersion v]` and
  `hcomp : Set.range v.base = (Set.range i.base)ᶜ`. This allows arbitrary scheme structures
  on D, including nonreduced closed subschemes. It expresses equality of underlying images,
  not a chosen equality of schemes. No quasi-compact or finite-type condition is imposed on v.
- Complex K: `∀ K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ`.
  These are all unbounded étale A-module complexes in the dependency's six-functor encoding.
- A_D: `(constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)`.
  This is the constant rank-one A-module sheaf. It uses the recorded constantSheaf,
  not a new coefficient object.
- i_*: `(lowerStar (ModuleCat.{u + 1} A) i).obj` on that sheaf, exactly the dependency's
  direct-image functor. There is no accidental derived pushforward in the first argument.
- Ordinary global RHom_T(i_* A_D,K): apply `.rightDerivedFunctor` to the A-linear Hom
  functor `(linearCoyoneda A (Sheaf ...)).obj (op (i_* A_D))`, then evaluate at
  `DerivedCategory.Q.obj K`. This is ordinary global derived Hom into D(ModuleCat A),
  rather than internal sheaf Hom or a bare Hom set / cohomology group.
- The displayed restriction arrow is specified by the existential natural transformation q:
  its degree-n component on every complex is required to equal the existing
  `globalSectionsUpperStarMap (ModuleCat A) v (K.X n)`. This component condition uniquely
  determines q. It is construction data for the arrow in the node, not a new hypothesis or
  an arbitrary map with the same endpoints. The q codomain uses the recorded `upperStar`.
- RΓ(T,K) and RΓ(V,v^*K): use Γ(T,I(K)) and Γ(V,v^*I(K)), where I is the existing
  `CochainComplex.kInjectiveResolutionFunctor`. For the open immersion, v^* is right adjoint
  to exact v_!, so v^*I(K) is K-injective and v^*K → v^*I(K) is a quasi-isomorphism.
  Consequently `q.app (I.obj K)` is the restriction morphism between these actual
  representative complexes for derived global sections. The proof docstring spells out
  these identifications on the unbounded categories.
- Cone and shift: `CochainComplex.mappingCone (q.app (I.obj K))`, localized with
  `DerivedCategory.Q`, then shifted by `⟦(-1 : ℤ)⟧` in `DerivedCategory (ModuleCat A)`.
- Isomorphism: `∃ e : ∀ K, ... ≅ ...`. Thus all K receive isomorphisms in the ordinary
  derived category of A-modules.
- Naturality: the final `∀ K L (f : K ⟶ L), ...` equates derived Hom applied to Q(f)
  followed by e(L) with e(K) followed by the shifted localized `mappingCone.map`.
  The two cone maps are induced by I(f) on Γ(T,I) and Γ(V,v^*I); q.naturality supplies
  the commuting square. This is a simultaneous natural family, not independently chosen
  objectwise isomorphisms. The functorial resolution sends quasi-isomorphisms to homotopy
  equivalences, and Γ and the compatible cone construction preserve these. Hence the RHS
  inverts quasi-isomorphisms and the equation gives naturality on D(T_et,A) as well.

The existential q and its component equation avoid adding a duplicate definition of
restriction: the statement uses the existing section-pullback construction directly.
The formula is not an added mathematical conclusion; it fixes the meaning of the arrow
already present in the node. No separate descent or extra comparison hypothesis is assumed.

Dependency declarations read and used:

- `def-weil-pbc-derived-categories`: `Sheaf.AlgebraicGeometry.DerivedCategories`, in
  particular its recorded existing `AlgebraicGeometry.Etale.DerivedCategoryModule` from
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`. The fully written derived
  category here is its underlying `DerivedCategory (Sheaf ... (ModuleCat A))`.
- `def-weil-pbc-etale-sheaves`: the existing `CategoryTheory.Sheaf` with
  `T.smallEtaleTopology` and ModuleCat values; the record explicitly authorizes this
  encoding for the six-functor chapter. Its locally constant, lisse, constructible and
  torsion predicates are not used by this node. Their source docstrings were read in
  the available `lean/Sheaf/AlgebraicGeometry/EtaleSheaves.lean` mirror; they add no
  hypothesis here.
- `def-weil-scheme-morphism-properties`: a convention-only record. The actual properties
  used are Mathlib `AlgebraicGeometry.IsClosedImmersion` and `IsOpenImmersion`, not a
  replacement predicate.
- `def-weil-pbc-constant-sheaf`: `CategoryTheory.constantSheaf` in
  `Mathlib.CategoryTheory.Sites.ConstantSheaf`.
- `def-weil-pbc-direct-image` and `def-weil-pbc-inverse-image`:
  `AlgebraicGeometry.Etale.lowerStar` and `upperStar` in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
- `def-weil-abstract-derived-category`: `DerivedCategory` and `DerivedCategory.Q` in
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`; the usual shift and cone construction
  are imported through `Mathlib.Algebra.Homology.HomotopyCategory.Triangulated`.
- `def-weil-pbc-kinjective-resolutions`: `CochainComplex.IsKInjectiveResolution` and its
  underlying `IsKInjective` and `QuasiIso`, in
  `Sheaf.AlgebraicGeometry.KInjectiveResolutions`. No new K-injectivity predicate is used.
- `def-weil-pbc-global-sections-functor`: `CategoryTheory.Sheaf.Γ` in
  `Mathlib.CategoryTheory.Sites.GlobalSections`. The existing
  `AlgebraicGeometry.Etale.globalSectionsUpperStarMap` in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections` fixes restriction.
- The resolution is the published `CochainComplex.kInjectiveResolutionFunctor` in
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`,
  as recorded in `lem-pur-kinjective-degreewise-existence`.
- Ordinary Hom uses existing `CategoryTheory.linearCoyoneda` from
  `Mathlib.CategoryTheory.Linear.Yoneda` and existing `Functor.rightDerivedFunctor`
  from `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`.

All recorded proof-dependency modules are included, directly or transitively. The
private proof-plan imports include the open-closed exact sequence, inverse-image exactness,
Grothendieck abelian module sheaves, extension-by-zero adjunction/exactness, and
`Sheaf.CategoryTheory.KInjectiveTotalDerived`. The theorem docstring carries all five
proof steps, including the signed cone and homotopy calculations and localization.

Edge cases checked before writing:

- D empty, V = T: i_* A_D is zero, restriction is an isomorphism, and its shifted cone is zero.
- V empty, D has all of T as its underlying image: closed étale direct image of the
  coefficient sheaf is A_T (including nilpotent closed thickenings), so the RHS is RΓ(T,K).
- T empty: all sheaf complexes involved have zero derived sections and Hom.
- A the zero ring and K the zero complex are allowed; both sides vanish.
- Arbitrarily unbounded K and non-quasi-compact open V are retained.
- Neither n = 0 nor any other degree is excluded: the component and naturality clauses
  quantify over all integers and all maps of complexes.
- Universe u is explicit; coefficients and étale module values have the recorded u+1
  universe. There are no auto-bound variables or auxiliary test-universe assumptions.

Searches (all msearch invocations used group NO and this item):

- LeanFinder: `Derived Hom closed immersion constant sheaf equals shifted cone of derived
  global sections restriction`: 8 hits (closed-immersion/ideal equivalence and Zariski
  Scheme.Modules restriction adjunctions), no match.
- Loogle: `CategoryTheory.Sheaf.Γ, CategoryTheory.constantSheaf`: 6 hits, including
  constantSheafΓAdj and Type-valued Γ/coyoneda comparisons, no closed-support derived theorem.
- LeanSearch: `restriction of global sections to open subscheme natural transformation
  etale sheaves`: service unavailable, Internal Server Error; recorded as unavailable.
- LeanFinder: `restriction of global sections natural transformation inverse image of
  sheaves`: 8 hits, including ΓRes_map and Zariski restrictFunctorΓ, no requested theorem.
- msearch grep: `relativeSectionRestriction|closedSupportHom|mappingConeFunctor`: no hits.
- rg of Mathlib, upstream WeilConjectures and lean/Sheaf: searched `closedSupport`,
  `closed.support`, `relativeSections`, `relativeSection`, `derivedGlobalSections`, `RHom`,
  `linearCoyoneda`, `mappingConeFunctor`, and `globalSectionsUpperStarMap`. Found existing
  internal derivedHom, global derived sections, linearCoyoneda, and section-pullback map;
  none states this ordinary global derived Hom/cone identification.
- Searched the node id in upstream WeilConjectures: no hits. Searched the proposed full
  declaration name by its short name in Mathlib/upstream/project: no pre-existing declaration.
- Searched DAG records for restriction and derived Hom notions while considering a helper;
  no helper was added, since the existing operations suffice directly.

Validation: server-only scompile.py compiled the statement cleanly (3.4 seconds for the
main module; nice 19, two threads, 60-second per-file limit). No local Lean command or
lake build was run. The only delivered proof is `sorry`. No mathematical statement fault
or STATEMENT-DISPUTED issue was found. The independent second reader has not yet read it.

## Second reading by NO

I independently read the node and its blueprint source
`sec-smooth-purity/sk-prop-sf-cbc/lem-amb-closed-support-hom.md`, the recorded statement
and definition dependencies, and the actual Lean signatures. The source states this for
an arbitrary complex and has no Noetherian, finite-type, torsion, invertibility or
boundedness assumption. The commutative coefficient-ring convention is supplied by
`def-weil-pbc-derived-categories` and the node's first proof step. I also read the relevant
Stacks source passages: extension by zero and its adjunction in `sites-modules.tex`
(lemma-extension-by-zero), its etale interpretation in `etale-cohomology.tex`
(proposition-describe-jshriek and the preceding discussion), and `derived.tex`
(lemma-adjoint-preserve-K-injectives, lemma-enough-K-injectives-implies), together with
`injectives.tex` (theorem-K-injective-embedding-grothendieck). None adds a restriction
missing from the Lean.

Object, hypothesis and conclusion checklist:

- A is a commutative coefficient ring: `(A : Type (u + 1)) [CommRing A]`.
  Matches the dependency convention; arbitrary characteristic and the zero ring remain.
- D, V and T are schemes: `{D V T : Scheme.{u}}`. Matches, with arbitrary `u`.
- i is a closed immersion: `(i : D ⟶ T) [IsClosedImmersion i]`. Matches Mathlib's
  scheme-theoretic notion; no reducedness assumption.
- v is the complementary open immersion: `(v : V ⟶ T) [IsOpenImmersion v]` and
  `Set.range v.base = (Set.range i.base)ᶜ`. Matches the complementary underlying open,
  allowing any isomorphic presentation of that open subscheme.
- K is an arbitrary etale A-module complex: `∀ K : CochainComplex
  (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ`. Matches the recorded six-functor
  encoding of `DerivedCategoryModule`, read in the actual Coefficients module. There is
  no accidental bounded or constructible subcategory.
- A_D is the rank-one constant sheaf: `constantSheaf ... |>.obj (ModuleCat.of A A)`.
  The actual Mathlib definition sheafifies the constant presheaf. Matches.
- i_* A_D is `(lowerStar (ModuleCat.{u + 1} A) i).obj ...`. The recorded declaration
  really is evaluation on etale base change, not a different pushforward. Matches.
- Ordinary global RHom is `linearCoyoneda A ...` at `op (i_* A_D)`, followed by
  `.rightDerivedFunctor`, evaluated at `DerivedCategory.Q.obj K`. I read both
  definitions: the former has value `ModuleCat.of A (i_* A_D ⟶ F)`, and the latter is
  total right derivation on the unbounded derived categories. Thus this is exactly the
  ordinary A-module-valued derived Hom claimed, not internal sheaf Hom. Matches.
- The arrow is restriction: the first existential binds a natural transformation `q`
  whose degree-n component is required to equal `globalSectionsUpperStarMap ... v (K.X n)`
  for every K and every integer n. I read that map's unit-and-terminal-section formula.
  This uniquely fixes the arrow already in the node and adds no hypothesis. Matches.
- RΓ(T,K) and RΓ(V,v^*K) are represented by the two mapped complexes on
  `kInjectiveResolutionFunctor.obj K`. I read the functor and its natural
  quasi-isomorphism and K-injectivity instance. Restriction `upperStar` is the recorded
  inverse image; for an open immersion it is right adjoint to exact extension by zero,
  hence its image of this resolution is K-injective. These are actual representatives
  of the stated derived global sections and derived restriction. Matches.
- Cone and [-1] are `DerivedCategory.Q.obj (CochainComplex.mappingCone (q.app ...))`
  followed by `⟦(-1 : ℤ)⟧`. Matches the ordinary derived A-module cone and shift.
- The isomorphism is a simultaneous family `∃ e : ∀ K, ... ≅ ...`, with the final
  equation imposing naturality for every `f : K ⟶ L`. The cone map uses the same
  resolution functor on f on both sides and `q.naturality` for its commuting square.
  This covers derived morphisms: resolutions send quasi-isomorphisms to homotopy
  equivalences, and postcomposition Hom, sections and the compatible cone maps preserve
  these equivalences. Localization then gives naturality also for inverse
  quasi-isomorphisms. Matches the full naturality clause, rather than merely separate
  objectwise isomorphisms.

Edge cases: D empty gives zero on the left and the cone of an isomorphism on the right.
V empty gives the full global-section complex, also for nilpotent closed thickenings
of T. Empty T, zero K and the zero coefficient ring are permitted and give zero objects.
No index family or positive integer parameter is introduced; degree n ranges over all
integers, including zero and negative degrees. Non-quasi-compact opens and arbitrarily
unbounded K are retained. The explicit `u` and the recorded `u+1` coefficient/sheaf
universes are consistent throughout; all variables are bound and no test-object universe
makes a hypothesis vacuous.

Independent searches, with different wording from the worker:

- LeanFinder: `etale cohomology supported on closed subscheme homotopy fiber restriction
  global sections` returned eight Zariski section/restriction results, none this theorem.
- Loogle: `"mappingCone", "Sheaf"` returned zero hits.
- LeanSearch: `The derived global sections with support in a closed subscheme are the
  homotopy fibre of restriction to the open complement` was unavailable (Internal Server
  Error); no negative mathematical search verdict is inferred from the failure.
- rg in Mathlib, upstream WeilConjectures and this project's lean/Sheaf used
  `supported.*(cohomology|sections)`, `sections.*support`, `relative.*cohomology`,
  `closedSupport`, `relativeSection`, `localCohomology`, and `sectionsWithSupport`.
  I opened the closest candidates: upstream `ProEtale.sectionsWithSupport` is a kernel
  functor on pro-etale sheaves, not this etale global derived isomorphism; Mathlib
  `localCohomology` is ideal-supported cohomology of ring modules. Neither is a match.
  The proposed theorem name has no pre-existing declaration in these trees or the
  upstream name inventory. Existing constant sheaf, Hom, derived functor, sections,
  pullback, resolution and cone constructions suffice without any new notion.

No mismatch was found. I changed neither the Lean nor the node. There are no new
nodes, dependency modules, private definitions, hollow data or statement corrections to
review. The sole theorem has a sorry-only proof. Its docstring contains the source,
blueprint id and all five proof steps, including the signed cone calculation and descent
of naturality. The node's `lean.statement` was checked verbatim against the signature.
Server-only scompile compiled ClosedSupportHom cleanly in 3.3 seconds (nice 19, two
threads, 60-second limit), with no errors or unexpected warnings. The compiler also
checked the private-overlay dependency KInjectiveTotalDerived in 1.1 seconds.
