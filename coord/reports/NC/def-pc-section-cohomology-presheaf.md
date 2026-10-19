## Worker report

Existing declaration: `AlgebraicGeometry.Scheme.Modules.sectionCohomologyPresheaf`
in `Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices`, lines 32–39. No new module,
new node, dependency repair, or statement correction is needed. The existing module
is already on newtargets-dag; its declaration docstring identifies Stacks Tag 01E4.

Clause-by-clause correspondence:

- Scheme T: implicit `{Y : Scheme.{uOpen}}`, with explicitly declared universe `uOpen`.
- Cochain complex of O_T-modules indexed by N: `(K : CochainComplex Y.Modules ℕ)`.
  Mathlib `Scheme.Modules` is `SheafOfModules.{uOpen} Y.ringCatSheaf`;
  Mathlib `CochainComplex` uses `ComplexShape.up`, hence consecutive differentials
  square to zero. The generic dependency declaration supports N as well as Z;
  its specialization to N here is precisely the item's explicit index choice.
- Natural cohomological degree q: `(p : ℕ)`.
- Presheaf on the Zariski opens: result
  `_root_.PresheafOfModules.{uOpen} Y.ringCatSheaf.obj`, whose underlying presheaf
  is a functor from `Y.Opensᵒᵖ` to additive commutative groups. Keeping the
  canonical sectionwise O_T-action is the native module-presheaf encoding.
- Value H^q(Gamma(V,K)): `SheafOfModules.forget Y.ringCatSheaf` forgets only
  the sheaf condition, `mapHomologicalComplex (ComplexShape.up ℕ)` applies this
  functor degreewise to K and its differentials, and `.homology p` takes its
  cycles modulo boundaries in the abelian category of presheaves of modules.
  Presheaf kernels and cokernels are computed objectwise, giving exactly the
  cohomology of the section complex on each V.
- Restriction for V contained in W: the underlying complex already has the
  degreewise section restrictions. Presheaf homology induces its restriction
  maps from these, so this construction fixes the maps as well as the values.
- No flatness, base change, injectivity, or resolution hypothesis: none appears
  in the signature or construction. The surrounding file concerns resolutions,
  but this definition takes an arbitrary K.

Dependency declarations read and used: `AlgebraicGeometry.Scheme` in
`Mathlib.AlgebraicGeometry.Scheme`, including its local-affine definition;
`CochainComplex` in `Mathlib.Algebra.Homology.HomologicalComplex`, including
its `ComplexShape.up` definition. These are exactly the two stmt_deps records.
Additional construction APIs read: `SheafOfModules.forget` and evaluation in
`Mathlib.Algebra.Category.ModuleCat.Sheaf`; the objectwise abelian structure in
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian`. The existing module imports
these APIs and the necessary scheme-module framework.

Source checked: local Stacks `cohomology.tex`, lemma-cohomology-of-open (01E1),
where sections of a resolution compute open cohomology, and
lemma-describe-higher-direct-images (01E4), whose proof describes precisely the
presheaf of kernels modulo images and its restriction mappings. The definition
uses that raw construction for arbitrary complexes without asserting the
resolution comparison for arbitrary K.

Edge cases checked: p=0 uses the cochain complex's zero incoming differential;
zero complexes give zero homology; the empty open and empty scheme are allowed;
no boundedness beyond the stated N indexing or nonemptiness condition is imposed.
The universe matches the project's `Scheme.Modules` convention at arbitrary uOpen.

Searches performed:

- msearch.py leanfinder: "presheaf assigning to an open subset the cohomology of
  the complex of sections of a complex of sheaves of modules". Eight results,
  including `CategoryTheory.Sheaf.cohomologyPresheaf` (Ext cohomology of a sheaf,
  not the raw homology of an arbitrary section complex) and module-section APIs.
- msearch.py loogle: `HomologicalComplex.homologyFunctor, SheafOfModules.sectionsFunctor`.
  No results.
- msearch.py leansearch: "presheaf cohomology of a complex of sections of sheaves
  of modules". Service unavailable, Internal Server Error.
- msearch.py grep in Algebra/Category/ModuleCat:
  `sectionCohomologyPresheaf|homologyFunctor|mapHomologicalComplex|toPresheaf`.
  Found forgetful/evaluation APIs, no matching named raw section-cohomology definition.
- rg in upstream WeilConjectures for sectionCohomologyPresheaf, sectionsFunctor,
  and section-complex patterns; no matching definition. Blueprint-id search in
  upstream WeilConjectures also found no result.
- rg in project lean/Sheaf for `sectionCohomologyPresheaf` found the exact
  definition in FlatBaseChangeOpenChoices and numerous existing citers.

No statement disputes or node faults found. Validation: deliver2.py --no-push
checks the existing declaration by a server-side #check through scompile and
runs the delivery preflight; its result is recorded by the worker's READY answer.

## Second reading by NC

Independently opened the item node, its sandbox copy, both dependency nodes and
recorded Mathlib declarations, the existing FlatBaseChangeOpenChoices module,
and Stacks cohomology.tex at lemma-cohomology-of-open (01E1), the restriction
mapping immediately following it, and lemma-describe-higher-direct-images (01E4).
The source first assumes ringed spaces and uses injective resolutions for the
comparison with derived cohomology. The present node isolates the raw section
complex construction on schemes; it does not assert that comparison for arbitrary
complexes. No injectivity, morphism of schemes, or flatness assumption is needed.

Object/hypothesis/conclusion checklist, with verdicts:

1. Arbitrary scheme T: `{Y : Scheme.{uOpen}}`. Read `Scheme` in
   Mathlib.AlgebraicGeometry.Scheme: a locally ringed space locally isomorphic
   to affine spectra. This is the recorded def-pc-scheme notion. PASS.
2. N-indexed cochain complex of O_T-modules: `(K : CochainComplex Y.Modules ℕ)`.
   Read `Scheme.Modules` in Mathlib.AlgebraicGeometry.Modules.Sheaf: it is
   `SheafOfModules.{u} X.ringCatSheaf`. Read `CochainComplex` in
   Mathlib.Algebra.Homology.HomologicalComplex: it is `HomologicalComplex`
   with `ComplexShape.up`, including square-zero differentials and chain maps.
   The dependency describes the integer-indexed specialization, but its recorded
   generic declaration explicitly supports the N indexing required here. PASS.
3. Arbitrary natural degree q: `(p : ℕ)` after K. No additional degree bound. PASS.
4. Presheaf on Zariski opens: result
   `_root_.PresheafOfModules.{uOpen} Y.ringCatSheaf.obj`. Its additive presheaf
   has domain `Y.Opensᵒᵖ`; the module structure is the canonical sectionwise
   O_T(V)-action, adding no requirement on K. PASS.
5. Value H^q(Gamma(V,K)): the body applies `SheafOfModules.forget` degreewise
   using `mapHomologicalComplex (ComplexShape.up ℕ)`, then takes `.homology p`.
   Read `forget` in Mathlib.Algebra.Category.ModuleCat.Sheaf: its objects and
   maps are exactly the underlying presheaves and their morphisms. Read the
   Presheaf.Limits, Presheaf.Colimits, and Presheaf.Abelian constructions:
   evaluation computes kernels and cokernels objectwise. Therefore homology
   evaluates to cycles modulo boundaries of the section complex. PASS.
6. Restriction P(W) to P(V) for V contained in W: the same presheaf-complex
   homology construction induces the maps from the degreewise restrictions.
   This is the source's restriction construction, not an unspecified family of
   objects or a sheafification of their homology. PASS.
7. No flatness or base-change hypothesis: no such binder or instance occurs.
   The surrounding local enough-injectives instance is not a parameter or
   ingredient of this definition's body. PASS.

Edge cases: p=0 has zero incoming boundary by ComplexShape.up on N; the zero
complex has zero homology; all opens including the empty open and the empty
scheme are admitted. There is no auxiliary index set, characteristic condition,
field assumption, or finiteness assumption. `uOpen` is explicitly declared and
arbitrary, matching Scheme.Modules' universe convention; every variable is
bound. The result retains its natural module action for every coefficient ring.

Independent searches (2026-10-15):

- msearch.py leanfinder, query "homology presheaf underlying complex evaluated
  on opens with induced restriction maps": eight hits, including generic
  HomologicalComplex.homologyFunctor and TopCat presheaves, no exact replacement.
- msearch.py loogle, query
  `PresheafOfModules.evaluation, HomologicalComplex.homology`: zero hits.
- rg for homologyPresheaf/cohomologyPresheaf/sectionCohomologyPresheaf in
  Mathlib's module-presheaf and Sites directories, upstream WeilConjectures,
  and this project's lean/Sheaf: the exact definition is the project's
  FlatBaseChangeOpenChoices declaration. Opened Mathlib's
  Sheaf.cohomologyPresheafFunctor and cohomologyPresheaf: they use Ext of one
  abelian sheaf, not raw homology of arbitrary module section complexes.
- rg for the item's blueprint id and sectionCohomologyPresheaf in upstream
  WeilConjectures and for sectionCohomologyPresheaf in dag/lean_names_upstream.json:
  no match. Existing project citers use the same definition.

No mismatch found; no Lean or node change needed. The signature recorded in
lean.statement agrees verbatim with the existing declaration before `:=`.
The definition's body is an actual construction without sorry, and its existing
source docstring names Tag 01E4. Its historical blueprint tag belongs to the
original bundled node; this delivery correctly reuses that existing declaration
and adds no module or duplicate definition merely to retag it. H6/H8 theorem
proof requirements are inapplicable to this definition-only existing attachment.
There are no new nodes, dependency modules, or statement corrections to audit.
Only this independent review was appended; the worker report is preserved.
Validation: deliver2.py's dry run and delivery each check the existing declaration
on the server through scompile.py and run the stage-2 preflight.
