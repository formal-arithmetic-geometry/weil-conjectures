## Worker report

Repaired `lean/Sheaf/AlgebraicGeometry/DerivedRHomAlgebraModule.lean` for return
R-dra (head 10ddbf434). The main declaration remains
`AlgebraicGeometry.derivedRHomAlgebraModule`. The node statement and dependencies
are unchanged. No new node or dependency module is needed.

Each hypothesis and clause is rendered as follows:

- Scheme: `(Y : Scheme.{u})`, the recorded Mathlib scheme, with no additional
  separation, Noetherian, nonempty or characteristic hypothesis.
- Commutative O_Y-algebra: `(B : Y.CommAlgebraSheaf)` is `Under Y.sheaf`, with
  commutative ring sheaf `B.right` and structure map `B.hom`.
- Quasi-coherence: `(hB : B.toModule.IsQuasicoherent)` is retained on the main
  derived functor, and its target is exactly `sheafAlgebraDerivedCategory Y B hB`.
- Arbitrary O_Y-module F: the category is `SheafOfModules.{u}` over
  `((sheafCompose (Opens.grothendieckTopology Y)
  (forget₂ CommRingCat RingCat)).obj Y.sheaf)` throughout. No condition is
  imposed on F. This is the category used by the landed `derivedInternalHom`.
- Ordinary sheaf Hom: `sheafAlgebraHomSections Y B F U` is precisely
  `(PresheafOfModules.homObj B.toModule.val F.val).obj U`, the section carrier
  of the dependency's `SheafOfModules.homObj B.toModule F`. It is the type of
  O-linear morphisms over the localized site, not merely maps on sections of U.
- Natural B-module action: `sheafAlgebraMulApp` has the explicit function
  `x ↦ B.right.obj.map W.unop.hom.op b * x`. `sheafAlgebraMul` packages these
  components into the multiplication morphism of B restricted to U.
  `sheafAlgebraHomSMul` defines `b • φ` to be `sheafAlgebraMul ... b ≫ φ`.
  Thus `(b • φ).app W x = φ.app W (b|_W * x)`; `sheafAlgebraHom_smul`
  records this formula. `sheafAlgebraHomModule` supplies the Module structure
  with this very smul field. Only its axioms are postponed as propositions.
- Restriction maps: `sheafAlgebraHomObj` uses `PresheafOfModules.ofPresheaf`
  on the existing Hom's abelian presheaf, with its existing restriction
  functions; `sheafAlgebraHom_restrict_smul` supplies only semilinearity.
  The existing internal Hom's sheaf proof supplies `isSheaf` directly.
- Functor maps: `sheafAlgebraHomMap` uses the underlying abelian-presheaf map
  of `PresheafOfModules.homObjMap (𝟙 B.toModule.val) g.val`, hence exactly
  postcomposition on each localized Hom. A named proposition supplies its
  B-linearity. `sheafAlgebraHom` packages these objects and maps as a functor.
- Additivity: `sheafAlgebraHom_additive`, registered as an instance, states
  that this explicit functor is additive. Its proof is postcomposition's
  distributivity over sums.
- Underlying ordinary Hom: `sheafAlgebraHom_underlying_linear` states that
  the O-action induced by `B.hom` agrees with the shared Hom's O-action.
  `sheafAlgebraHomUnderlying_eq` equates two already constructed functors:
  restriction of this explicit B-valued Hom and the existing ordinary Hom.
  Their carriers, addition, restrictions and postcomposition functions are
  identical; linearity of φ identifies the two scalar actions.
  `sheafAlgebraHomUnderlyingIso` is `eqToIso` of that equality, the transported
  identity comparison. It chooses no unknown functor, object, map or iso.
- Functorial K-injective resolution: `sheafAlgebraHomResolution` is the proved
  `CochainComplex.kInjectiveResolutionFunctor.{u}` with the instance
  `SheafOfModules.isGrothendieckAbelian _`; `toSheafAlgebraHomResolution`
  is exactly `CochainComplex.toKInjectiveResolution.{u}` with the same instance.
  These are the same resolution and instance as `derivedInternalHom`, with
  no choice from a sorried existence theorem. The proved
  `monoQuasiIso_toKInjectiveResolution_app` supplies the quasi-isomorphism,
  `isKInjective_kInjectiveResolutionFunctor_obj` supplies K-injectivity, and
  imported `injective_kInjectiveResolutionFunctor_obj_X` supplies injectivity
  at every integer degree. The old `sheafAlgebraHomResolution_spec` is removed.
- Computation for a representative M: the defining composite is
  `sheafAlgebraHomResolution Y ⋙ (sheafAlgebraHom Y B).mapHomologicalComplex
  (ComplexShape.up ℤ) ⋙ DerivedCategory.Q`. This gives the complex with terms
  Hom(B,I(M)^n) and postcomposition differentials.
  `derivedRHomAlgebraModule_comparison` states its natural comparison with Q
  followed by the localized derived functor.
- Quasi-isomorphisms: `sheafAlgebraHomResolution_inverts` gives precisely the
  inversion proposition required by `Localization.lift`. Its proof uses
  naturality and two-out-of-three, then the recorded Hom-complex lemma with
  both first arguments B[0]. Quasi-isomorphisms are detected on the underlying
  abelian sheaves, as required in the node.
- Descent D(O_Y) → D(B): `derivedRHomAlgebraModule` is `Localization.lift` of
  the explicit composite, using that inversion proposition. The two
  `HasDerivedCategory` instance binders fix the shared localizations and their
  hom universes `w`, `wB`; no derived category instance is chosen privately.
- Forgetting the algebra action: `derivedRHomAlgebraModule_underlying` ties
  the comparison directly to `(SheafOfModules.restrictScalars ...).mapDerivedCategory`,
  rather than quantifying over an unspecified U. Named propositions assert
  preservation of finite limits and finite colimits, registered as instances.
  The comparison's other side is exactly `derivedInternalHom` specialized to
  Q(B[0]) and the identity in its second argument, using the same resolution.

Dependency declarations read (full signatures and docstrings):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.DerivedCategoryQCoherentAlgebra`:
  `AlgebraicGeometry.sheafAlgebraDerivedCategory`, importing the recorded
  `Scheme.CommAlgebraSheaf` and `Scheme.CommAlgebraSheaf.toModule`.
- `Sheaf.Algebra.Homology.DerivedInternalHom`:
  `CategoryTheory.derivedInternalHom`, `derivedInternalHom_comparison`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`:
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutions`.
  The statement supplies the small-site context; its sorried existential data
  is not used to define any resolution.
- `Sheaf.Algebra.Homology.QuasiIsoHomComplexMap`:
  `CategoryTheory.quasiIso_homComplex_map`, in the inversion proof docstring.
- Ordinary Hom is the shared `PresheafOfModules.homObj`/`homObjMap` and
  `SheafOfModules.homObj`/`homFunctor`, from upstream InternalHom modules.
- Proved resolution data comes from
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`;
  degreewise injectivity comes from its sibling `KInjectiveResolutionInjective`.

The Stacks source was read in the sandbox's retained `duality-source.tex`,
Section `section-duality-finite`, including the ordinary Hom functor, its derived
extension to algebra-module sheaves, and the underlying derived restriction.

Edge cases checked: empty schemes and opens; zero algebra and zero module;
B = O_Y; every integer degree including zero and negative degrees; unbounded
complexes. No nontriviality, flatness, finite presentation, boundedness, finite
morphism or characteristic assumption is introduced. Sheaf carriers use u,
the small site is Opens Y, and both localization universes are explicit.

Searches (including the inherited searches and the repair's repetitions):

- LeanFinder, `sheaf Hom from an algebra with action by precomposition multiplication`:
  eight hits, ordinary sheaf/module morphisms and section maps; no algebra-valued
  sheaf Hom functor.
- Loogle, `SheafOfModules.restrictScalars, Functor.mapDerivedCategory`:
  zero hits, unknown identifier `Functor.mapDerivedCategory`. The actual exact
  derived functor was then located and read by rg in pinned Mathlib.
- msearch grep, `restrictScalars|coextendScalars` in Mathlib's
  `Algebra/Category/ModuleCat/Sheaf`: ten hits, restriction and continuous
  pushforward ingredients, no algebra-valued derived Hom.
- rg over Mathlib, upstream WeilConjectures and project lean/Sheaf for sheaf Hom,
  coextension, the item id and derived Hom: existing ordinary internal Hom,
  fixed-ring coextension and shared derived internal Hom; no D(B)-valued RHom.
- rg for exactness of varying-sheaf restriction: Mathlib's changing-sheaf-rings
  restriction has Additive, but no preservation-of-finite-limits/colimits
  instances were found. The module therefore states these Prop obligations
  and uses the tied mapDerivedCategory.
- Inherited LeanSearch query `derived internal Hom functor to modules over an algebra`:
  service unavailable (Internal Server Error), not treated as evidence of absence.
- Inherited Loogle `ModuleCat.coextendScalars` and Mathlib grep for coextension:
  fixed-ring module coextension does not supply this varying sheaf-algebra functor.

No statement dispute or correction. All remaining sorried declarations are
named Prop obligations with source and natural-language proof docstrings; they
are listed in the node's lean.declarations. The definitions contain no sorry
and no Classical.choose from an existence theorem.

## Repair of R-dra

1. Removed `exists_sheafAlgebraHom` and all choices from it. Hom sections, the
   multiplication components, smul, Module data, restrictions, postcomposition,
   and functor data are now explicit. The underlying iso is transported identity
   along equality of two specified constructions, not a chosen witness.
2. Replaced both chosen resolution data by proved kInjectiveResolutionFunctor
   and toKInjectiveResolution with the proved Grothendieck instance. Imported
   the proved degreewise-injectivity instance and removed the redundant spec.
3. Wrote every O_Y-module category with sheafCompose on Y.sheaf, matching the
   recorded derivedInternalHom exactly; there is no Y.ringCatSheaf in this file.
4. Tied the underlying derived comparison to restrictScalars.mapDerivedCategory.
   Exactness obligations are named propositions about the existing functor.

The stale second-reading section of the returned version was removed. The
second reader must read the repaired definition and write a fresh review.

## Second reading by F1

I independently read the node, all five statement-dependency nodes and their
recorded declarations, the complete 443-line module, the shared algebra-sheaf
and ordinary internal-Hom definitions, and the resolution implementation.
The source was the retained `duality-source.tex`, lines 2458–2544: the opening
paragraphs of section-duality-finite and the compute-sheafhom-affine,
sheafhom-affine-adjoint and sheafhom-affine-ext lemmas (0BUZ, 0BV0, 0BV1).
The source uses an affine morphism to obtain the quasi-coherent algebra
f_*O; the node abstracts that algebra as B. Its Hom action and construction
need only the stated commutative algebra, with quasi-coherence retained at
the derived-category interface. The source imposes no Noetherian, separated,
finite, nonzero or boundedness assumption on this construction. The subsequent
finite-pseudo-coherent lemma is not part of this definition.

Objects, hypotheses and clauses, matched in node order:

1. Y is any scheme: `Y : Scheme.{u}`. I read Mathlib's `Scheme`, extending
   `LocallyRingedSpace` with local affineness. Verdict: exactly the dependency,
   with no added geometric assumptions.
2. B is a commutative quasi-coherent O_Y-algebra:
   `B : Y.CommAlgebraSheaf` and `hB : B.toModule.IsQuasicoherent`.
   I read `CommAlgebraSheaf = Under Y.sheaf`, and `toModule`, which restricts
   the unit B-module along B.hom. Verdict: correct ring sheaf, algebra map
   and underlying O-module, not a constant-ring special case.
3. F is an arbitrary O_Y-module: the explicit `SheafOfModules.{u}` carrier
   over `sheafCompose ... Y.sheaf`. Verdict: identical to the carrier in
   `derivedInternalHom`; no quasi-coherence or other restriction on F.
4. Hom(B,F) is the ordinary internal sheaf Hom:
   `sheafAlgebraHomSections` uses `PresheafOfModules.homObj B.toModule.val F.val`.
   I read the upstream definition: its sections are morphisms after
   `restrictOver`, not Hom of the section modules alone. `sheafAlgebraHomObj`
   keeps these carriers, abelian groups, restrictions and the existing sheaf
   proof. Verdict: exactly the required internal Hom sheaf.
5. The natural B-action acts on the first argument:
   `sheafAlgebraMulApp` sends x to b restricted to W times x;
   `sheafAlgebraMul` packages these components; `sheafAlgebraHomSMul`
   precomposes with that multiplication morphism. `sheafAlgebraHom_smul`
   records the component formula. `sheafAlgebraHomModule` retains that smul
   and takes only its laws from `sheafAlgebraHom_module_axioms`.
   Verdict: concrete correct action, including zero and unit laws.
6. This gives an additive functor Mod(O_Y) to Mod(B):
   `sheafAlgebraHomMap` is the shared homObjMap with identity on B and
   postcomposition by g; `sheafAlgebraHom` supplies those objects and maps;
   `sheafAlgebraHom_additive` states additivity. The named restriction and
   map semilinearity obligations refer to precisely these functions.
   Verdict: the specified functor, not an unspecified witness.
7. For every representative complex M, use a functorial K-injective
   resolution injective in every degree: `sheafAlgebraHomResolution` and
   `toSheafAlgebraHomResolution` are the proved upstream
   `kInjectiveResolutionFunctor` and `toKInjectiveResolution` under
   `SheafOfModules.isGrothendieckAbelian`. I read their signatures and
   definitions, `monoQuasiIso_toKInjectiveResolution_app`,
   `isKInjective_kInjectiveResolutionFunctor_obj`, and the imported proved
   `injective_kInjectiveResolutionFunctor_obj_X`. Verdict: all three
   properties hold for this exact resolution; the small Opens Y site needs
   no extra binder. This is the same Grothendieck instance and resolution
   used in the recorded derived internal Hom.
8. The derived value is the complex with terms Hom(B,I(M)^n):
   the composite `sheafAlgebraHomResolution Y` followed by
   `(sheafAlgebraHom Y B).mapHomologicalComplex (ComplexShape.up ℤ)` and Q
   specifies its objects, differentials and maps. The natural computation
   clause is `derivedRHomAlgebraModule_comparison`. Verdict: all integer
   degrees and all representative complexes, without a boundedness cutoff.
9. Quasi-isomorphisms descend: `sheafAlgebraHomResolution_inverts`
   asserts exactly IsInvertedBy for that explicit composite. Its proof
   docstring uses resolution naturality and two-out-of-three, then
   `quasiIso_homComplex_map` with both first arguments B[0], and detection
   on underlying abelian sheaves. I read that dependency's full signature:
   both targets are K-injective and both maps are quasi-isomorphisms.
   Verdict: applicable without a flatness or finiteness hypothesis on B.
10. Obtain D(O_Y) to D(B): `derivedRHomAlgebraModule` is `Localization.lift`
    of that composite, using precisely the preceding inversion proposition.
    Its target is the dependency's `sheafAlgebraDerivedCategory Y B hB`:
    all derived B-module sheaves, not the quasi-coherent bounded subcategory.
    Verdict: correct descent and target.
11. Forgetting the B-action gives RHom(B[0],K):
    `sheafAlgebraHom_underlying_linear` identifies the O-action,
    `sheafAlgebraHomUnderlying_eq` compares the two explicit ordinary
    functors, and `sheafAlgebraHomUnderlyingIso` transports their identity.
    `derivedRHomAlgebraModule_underlying` compares the exact derived
    restriction along B.hom with `derivedInternalHom` at Q(B[0]) and the
    identity in K. I read `restrictScalars` and its Additive instance;
    the finite-limits/colimits obligations refer to this same functor.
    Verdict: a natural comparison with the recorded RHom and fixed
    resolution, with no arbitrary forgetting functor.

Edge cases: empty Y and empty opens are admitted; there is no Nonempty or
Nontrivial binder. The zero algebra, zero module, and B = O_Y are admitted,
with multiplication and precomposition still defining the stated action.
No index set is quantified; the complexes use every n in Z, including zero
and negative degrees, and may be unbounded. There is no characteristic,
field, flatness, coherence-of-F or finite-presentation restriction.
`u` is arbitrary and shared by the small site, ring sheaves and module
carriers, as in the dependency declarations; a larger carrier can be
placed in a larger ambient universe. `w` and `wB` separately specify the
localizations' Hom universes via the shared HasDerivedCategory binders.
No variable or universe is unbound.

Independent searches, with different wording from the worker:

- LeanFinder: `restriction of scalars sheaf algebra right adjoint derived functor`.
  Eight hits: varying-ring `SheafOfModules.restrictScalars`, fixed-ring
  ModuleCat restriction adjoints, and other forgetful/pushforward adjoints.
  None constructs this algebra-valued derived internal Hom.
- Loogle: `SheafOfModules.homFunctor` is not indexed (unknown identifier;
  zero hits). I therefore opened the actual upstream declaration directly;
  it constructs O-module-valued Hom, not B-module-valued Hom.
- LeanSearch: `derived coinduction for a sheaf of algebras` returned Internal
  Server Error. Recorded as unavailable, not evidence of absence.
- rg over Mathlib sheaf modules, upstream WeilConjectures and project
  lean/Sheaf for `coinduc`, `coextend`, `derivedRHomAlgebra`,
  `sheafAlgebraHom`, restriction adjoints and rightAdjoint. The upstream
  sheaf RestrictScalars module treats fixed coefficient rings. Existing
  ordinary Hom and the derived internal Hom serve the dependencies; the
  project FiniteSheafHomAffine theorem concerns adjunction for f_*O and
  does not define this derived B-valued functor. No matching definition
  was found. The delivery keeps the common ordinary Hom and scalar
  restriction definitions rather than duplicating them.

No mismatch was found and no Lean or node change was needed. No new node,
dependency module, statement correction or unresolved dispute is present.
Every delivered definition has explicit data; postponed arguments are named
Prop obligations with source and natural-language proof docstrings.
Every theorem remains `by sorry`, as stage 2 requires. All declarations carry
the item's blueprint tag and source; the node is a definition with no proof
steps, and its descent argument is reproduced in the inversion and underlying
comparison docstrings. The recorded main signature was checked against the
file verbatim. The second reading changes only this report.

Validation: scompile compiled the full module cleanly on the server in
28.8 seconds, exit code 0, with no warnings or errors. All lines are at
most 100 characters. The delivery dry run and push follow this review.
