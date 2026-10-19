## Worker report

The module `Sheaf.Paper.ConstantTowerTransition` states
`AlgebraicGeometry.ProEtale.constantTowerTransition`, with `sorry` as its whole proof.
Its real-data helper `constantTowerTransitionAugmentation` composes the published
unbounded/bounded-below single-object cohomology comparison with Mathlib's canonical
zeroth-derived comparison, then inverts this composite. It is the augmentation from
ordinary direct image to H⁰ of the total derived direct image, not a chosen abstract
isomorphism. There are no new axioms, proof hypotheses or new definition nodes.

Source read: Stacks `derived.tex`, `lemma-left-exact-higher-derived` (Tag 05TD),
lines 5565–5627, especially part (3) and the reduction to nonnegative resolutions;
the complete recorded coefficient-comparison module and its K-injective normalization;
and current blueprint main-20261015 `prop-cohomological-finiteness.proof.md`, Step 7.
The node's five proof steps are reproduced, with their inputs, in the theorem docstring.

Hypothesis and clause correspondence:

- Arbitrary schemes X,Y and morphism f are `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
  No properness, connectedness, smoothness or nonemptiness condition is imposed.
- The two finite commutative rings are `{A B : Type (u + 1)}` with `[CommRing A]`,
  `[CommRing B]`, `[Finite A]`, `[Finite B]`; their homomorphism is `(φ : A →+* B)`.
  These are precisely the coefficient universe and fixed-scalar presentation used by
  the recorded comparison dependency, on sites with object universe u+1 and Hom universe u.
- The small pro-etale sites are exactly `Scheme.ProEt.topology X` and its Y counterpart,
  on Mathlib's `Scheme.ProEt` from the site's dependency record.
- F and G are `Sheaf ... (ModuleCat.{u + 1} A)` and the B analogue. These are the
  fixed-scalar presentation of sheaves of modules over the corresponding constant ring
  sheaves, already used by the recorded coefficient-comparison dependency. A fixed A
  action extends uniquely to the sheafified constant ring: locally represent a coefficient
  by a constant and apply that scalar, then glue by the sheaf condition. Conversely
  restrict this action to constant sections. This preserves objects, linear maps and
  restriction maps, and excludes no sheaf or morphism in the node.
- The A-linear map is the arbitrary binder
  `u : F ⟶ (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).obj G`.
- The derived direct images are `(lowerStar (ModuleCat ...) f).rightDerivedFunctor`;
  these are the existing K-injective total right derived functors, with no replacement
  by a different functor or an assumed equivalence.
- The comparison c is exactly `(fixedScalarRestrictionDirectImage φ f).hom.app` at G[0],
  whose supplied theorem `fixedScalarRestrictionDirectImage_kInjective` fixes the
  inverse-on-resolutions normalization. It is not an arbitrary natural isomorphism.
- `DerivedCategory.singleFunctor ... 0` renders [0] on objects and the map u.
  The inverse of `mapDerivedCategorySingleFunctor 0` explicitly identifies
  `(Res G)[0]` with `Res(G[0])` before applying c.
- `DerivedCategory.homologyFunctor ... 0` applied to the displayed composite is exactly
  H⁰(c composed with Rf_*(u[0])), with that necessary single-object identification.
- The first factor on the left is `(constantTowerTransitionAugmentation A f F).hom`.
  On the right the B augmentation is mapped by ordinary coefficient restriction, and
  `mapDerivedCategoryHomologyFunctorIso 0` then identifies Res H⁰ with H⁰ Res.
  Thus both sides have the precise same source and target, through the prescribed
  augmentation identifications. These are isomorphisms by construction from the existing
  canonical isomorphisms; no independent existence statement is substituted.
- The right side starts with `(lowerStar (ModuleCat A) f).map u`, the actual ordinary
  direct-image map. Precomposition with base change and coefficient postcomposition
  commute definitionally here, including on maps: both send u at V to its component
  at V ×_Y X. Therefore this equality asserts the section-map clause, not only an
  isomorphism between its endpoints.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`
  and `AlgebraicGeometry.Scheme.ProEt.topology`, the recorded site and topology.
- `Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage`:
  `AlgebraicGeometry.ProEtale.fixedScalarRestrictionDirectImage` and
  `fixedScalarRestrictionDirectImage_kInjective`. Their full statements and docstrings
  were read; finite coefficients and the K-injective normalization are retained.
- `Mathlib.CategoryTheory.Abelian.RightDerived`:
  `CategoryTheory.InjectiveResolution.toRightDerivedZero'`, its cycles-inclusion
  equation and naturality, `CategoryTheory.instIsIsoToRightDerivedZero'`, and
  `CategoryTheory.Functor.rightDerivedZeroIsoSelf`. Together with
  `InjectiveResolution.of` in `Mathlib.CategoryTheory.Abelian.Injective.Resolution`,
  these are the dependency's recorded one-declaration-per-clause Mathlib interface.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`:
  `Functor.homologyRightDerivedFunctorObjSingleFunctorIso`; its definition uses the
  bounded-below/unbounded comparison and the single-object injective resolution.
- `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.ProEtale.lowerStar`, its section and morphism formulas
  `lowerStar_obj_val_obj` and `lowerStar_map_hom_app`, and the additive and
  finite-limit-preserving instances. This is the implementation module; the
  FiniteCoefficient module is a compatibility re-export. The intrinsic dependency
  record remains `AlgebraicGeometry.Scheme.proEtaleConstantModuleDirectImage` in
  `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`, unchanged from Q02's reviewed record.
  Here f_* uses `lowerStar (ModuleCat A) f` in the fixed-scalar presentation forced
  by the recorded `fixedScalarRestrictionDirectImage` comparison, as explained in
  the item's `lean.note`; this is the counterpart of the intrinsic declaration.
- Exact restriction and its derived functor use `CategoryTheory.Sheaf.restrictScalars`
  in `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars`,
  `derivedRestrictScalars` in `...Sheaf.DerivedBaseChange`,
  `Functor.mapDerivedCategorySingleFunctor` in Mathlib's derived ExactFunctor module,
  and `Functor.mapDerivedCategoryHomologyFunctorIso` in the upstream ExactFunctor module.

The recorded proof modules `KInjectiveDerivedMapComputation`,
`NormalizedDerivedComparisonCommonResolution`, and
`RingedSiteKInjectiveResolutionsOfUniverses` are imported without `public`; their full
statements and docstrings were read. Mathlib's derived KInjective/Plus modules carry
`Qh_map_bijective`, `quasiIso_iff` and the bounded-below comparison; the enough-injective
and bounded-below-injective facts are available in their import closure. The recorded
`ProEtaleModuleDirectImageLeftExact` module is also imported for its proof input;
`lowerStar_additive` and `preservesFiniteLimits_lowerStar` give that same input
in the equivalent fixed-scalar presentation.

Edge cases checked: φ = identity reduces to naturality of the ordinary canonical
augmentation; u = 0, F = 0 and G = 0 give zero maps throughout. The empty scheme and
zero ring are allowed. The nonflat ring map Z/4 → Z/2 remains allowed: restriction,
not scalar extension, is the exact functor used here, and no hypothesis that
restriction preserves K-injectives occurs. f is unrestricted. No site universe equality
has been introduced. There is no statement correction or disputed statement.

Searches actually run:

- msearch leanfinder: `degree zero derived direct image comparison compatible with
  restriction of scalars`. Eight hits, including
  `PresheafOfModules.restrictScalarsCompToPresheaf`, generic
  `rightDerivedZeroIsoSelf` identities, and an open-restriction adjunction. No theorem
  gives the specified changing-coefficient, normalized direct-image equality.
- msearch loogle: `"toRightDerivedZero"`. Twelve generic augmentation, naturality and
  invertibility results. These supply the canonical augmentation interface, not the
  required two-coefficient comparison theorem.
- msearch grep: `toRightDerivedZero|restrictionOfScalars` in `CategoryTheory/Abelian`.
  Five hits in RightDerived.lean, lines 36,263,273,275,277; inspected the full augmentation,
  naturality and isomorphism definitions through line 370.
- msearch leansearch: `degree zero derived direct image comparison commutes with
  restriction of scalars and the canonical injective resolution augmentation`.
  Eight results, chiefly `InjectiveResolution.toRightDerivedZero'_naturality_assoc`,
  `toRightDerivedZero_eq`, and `desc_commutes_zero`, plus projective analogues.
  None states the required normalized coefficient-comparison square.
- rg on the upstream WeilConjectures tree, project Sheaf tree, and upstream-name index:
  `constantTowerTransition|constantTowerTransitionAugmentation|constant.tower.transition`;
  no match. The item id also has no upstream source match. A broader constant-tower
  search finds inverse-limit/completion material, not this coefficient-square theorem.

Validation: `scompile.py Q130 lem-pod-constant-tower-transition` compiled the exact
module both as a sandbox and at its library path, without errors or warnings (5.5 s
and 5.8 s in the successful run). Every theorem written here has only `sorry` as proof;
the helper has full canonical data. The initial compile identified two invalid
line-breaks after a field-notation dot; these were corrected before the successful run.


## Repair of return L (head 939168b38928)

H2/H13: removed the dependency node from the delivery packet, retaining Q02's
reviewed `Scheme.proEtaleConstantModuleDirectImage` record on the base. Its
intrinsic constant-ring module sheaves and rho-action already state the dependency
exactly, so no §1(B) repair is claimed. Added the requested item `lean.note`
explaining the fixed-scalar counterpart forced by `fixedScalarRestrictionDirectImage`.
Deleted the dependency-modules section and corrected the implementation-module
sentence above. The accepted item module, its helpers, theorem signature and
sorry-only proof are unchanged. No landed citer is edited.

Self-check: compared the sandbox item with the current base; the only changed
node field is `lean`. Read the theorem and helper against the saved statement:
all coefficient, scheme, sheaf and morphism binders, comparison and augmentation
clauses remain unchanged. The recorded signature is verbatim from the module.
There are no new nodes or dependency-record changes in the repaired packet.

Repair validation: `scompile.py` compiled the unchanged module cleanly in sandbox
and library modes (9.9 s and 8.5 s). The repaired packet removes the rejected
dependency override; the item signature remains verbatim and every other item
field agrees with the current base.

## Second reading by Q130

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
