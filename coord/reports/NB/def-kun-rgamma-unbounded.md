## Worker report

Repair of immutable head 2c02e0b6975a, addressing H4 and H8. This delivery now
attaches existing declarations and contains no Lean module. The former
`AlgebraicGeometry.Etale.RGamma` and `etaleCohomology` definitions duplicated
`AlgebraicGeometry.Etale.rightDerivedGlobalSections` and
`AlgebraicGeometry.Etale.cohomology` in
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`. Removed
`lean/Sheaf/AlgebraicGeometry/RGammaUnbounded.lean`; its missing blueprint marker
(H8) is resolved by removing the duplicate declaration, rather than retaining
another spelling. The prior worker and second-reading claims of no existing
construction were incorrect and are superseded by this report. The node changes
only in `lean`; there is no statement correction and no new or dependency module.

Hypothesis and clause correspondence:

- Scheme T: specialize the existing `X : Scheme.{u}` parameter to T.
- Commutative coefficient ring Λ: specialize the existing coefficient category A
  to `ModuleCat.{u + 1} Λ`, for `Λ : Type (u + 1)` with `[CommRing Λ]`.
  The generic categorical assumptions on A are supplied by the existing module
  category instances; they impose no new ring hypothesis.
- `Mod(T_et,Λ)` and its unbounded derived category: the input of the specialized
  functor is `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat Λ))`,
  the recorded six-functor encoding of `def-weil-pbc-derived-categories`.
- A representing cochain complex C and a K-injective resolution C → I:
  `DerivedCategory.exists_iso_Q_obj_of_isKInjective` constructs the K-injective
  representative from `DerivedCategory.Q.objPreimage K` and
  `HasKInjectiveResolutions.exists_isKInjective`. Its proof uses the comparison
  `Q.objObjPreimageIso` and the isomorphism `Q.map` of the resolution map.
- Sections Γ(T_et,M) = M(T), retaining Λ-module structure: the existing functor
  is `Sheaf.Γ T.smallEtaleTopology (ModuleCat Λ)`. Its comparison
  `Sheaf.ΓNatIsoSheafSections` identifies it with sections at the terminal
  object, which is T on the small étale site. Sections land in `ModuleCat Λ`,
  not in an underlying abelian-group category.
- The displayed RGamma clause: use
  `(AlgebraicGeometry.Etale.rightDerivedGlobalSections (ModuleCat Λ) T).obj K`.
  It is defined by `R(Sheaf.Γ T.smallEtaleTopology (ModuleCat Λ))`.
  The explicit API `CategoryTheory.Functor.rightDerivedFunctorObjQIso`,
  specialized to F = Γ and a K-injective I, has signature
  `F.rightDerivedFunctor.obj (DerivedCategory.Q.obj I) ≅
  DerivedCategory.Q.obj ((F.mapHomologicalComplex _).obj I)`.
  Thus transporting along K ≅ Q(I) gives exactly the node's localized complex
  of termwise sections. A different choice of resolution is the same derived
  construction under its canonical comparison, and is not a new notion.
- The target D(Λ): `DerivedCategory (ModuleCat Λ)` is the functor's target.
- Every integer q and the H^q clause: use
  `(AlgebraicGeometry.Etale.cohomology (ModuleCat Λ) T q).obj K`, with `q : ℤ`.
  The existing definition is `rightDerivedGlobalSections A X ⋙
  DerivedCategory.homologyFunctor A i`, exactly cohomology of RGamma.
- Independence and agreement on D+: these are deferred properties in the node,
  not additional definition clauses. The source's
  `Functor.rightDerivedFunctorPlusCompatibility` identifies the restriction
  along `DerivedCategory.Plus.ι` with the bounded-below construction. For
  Λ = ℤ, passage to abelian sheaves is the usual module/abelian-group encoding;
  general Λ keeps the module structures throughout.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.KInjectiveResolutions`:
  `CochainComplex.IsKInjectiveResolution` = `QuasiIso f ∧ I.IsKInjective`.
- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`:
  `CochainComplex.etale_kinjective_resolutions_exist` supplies existence,
  functoriality up to homotopy, uniqueness and the bounded-below clause.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.cohomology` and `rightDerivedGlobalSections`, already
  attached to `def-weil-pbc-etale-cohomology`.
- `Sheaf.AlgebraicGeometry.DerivedCategories` and its imported
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, the coefficient encoding.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf`: `SheafOfModules` describes the
  general module-sheaf notion; this item's constant coefficients use the
  dependency's recorded equivalent `Sheaf ... (ModuleCat Λ)` encoding.
- `Mathlib.CategoryTheory.Sites.GlobalSections`: `CategoryTheory.Sheaf.Γ` and
  `Sheaf.ΓNatIsoSheafSections`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`;
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor` and `homologyFunctorFactors`.

Additional source API read in full:
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective`
(`DerivedCategory.exists_iso_Q_obj_of_isKInjective`,
`CategoryTheory.Functor.rightDerivedFunctorObjQIso`), its `Defs` module
(`rightDerivedFunctor`, `rightDerivedFunctorUnit`, and the K-injective IsIso
instance), and `PlusCompatibility` (`rightDerivedFunctorPlusCompatibility`).
These existing APIs establish the precise K-injective recipe, not merely a
similar generic functor name.

Edge cases: no bound on q, so negative, zero and positive degrees are all
included; no boundedness on K, so genuinely unbounded complexes are included;
zero objects and acyclic representatives are admitted and mapped to zero
(`Functor.isZero_rightDerivedFunctor_obj` in Defs); the empty scheme and the
zero commutative ring require no extra exclusions. No finiteness, separation,
Noetherian, characteristic or nonzero-ring assumption is added.

Searches in this repair:

- `msearch.py ... leanfinder "unbounded derived global sections computed by
  K-injective resolutions"`: eight generic Mathlib hits including
  `CochainComplex.IsKInjective` and `isKInjective_of_injective`, no étale RGamma.
- `msearch.py ... loogle "DerivedCategory.homologyFunctor"`: twelve hits,
  including the exact cohomology functor.
- `msearch.py ... grep "rightDerivedGlobalSections|RGamma"`: four unrelated
  Dold-Kan Gamma hits, no matching Mathlib definition.
- `rg -uuu -n 'rightDerivedGlobalSections|RGamma|cohomology'` in the source:
  found the exact definitions in Etale/Derived/LowerShriek.lean, with signatures
  and docstrings read; searching RightDerivedFunctor found the explicit
  KInjective.lean computation API. `-uuu` matters: this source directory is
  ignored by ripgrep's default traversal in this environment.
- `rg -uuu` over `lean/Sheaf/AlgebraicGeometry` found many existing uses of
  the source `rightDerivedGlobalSections`, confirming the shared convention.
- Read the blueprint definition at its recorded source place and every
  statement-dependency node and signature. No statement fault remains.

Validation: the dry run checks both recorded existing declarations by server
`#check` through scompile.py and checks delivery preflight. No local compiler
or library build is used. An independent second reader must review this repair;
previous second-reading sections were removed because they described the
now-removed module.

## Second reading by NB

I reread the node statement and the recorded existing declarations. The object and
hypothesis correspondence is:

- A scheme `T` is rendered by the declaration's `X : Scheme.{u}` parameter, specialized
to `T`.
- A commutative ring `Λ` is rendered by `A := ModuleCat.{u + 1} Λ`, with
`Λ : Type (u + 1)` and `[CommRing Λ]`; the generic category assumptions required by
`rightDerivedGlobalSections` are supplied by the module-category instances.
- The coefficient sheaf category `Mod(T_et,Λ)` and its unbounded derived category are
`Sheaf T.smallEtaleTopology (ModuleCat Λ)` and
`DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat Λ))`, matching
`def-weil-pbc-derived-categories`.
- A representing complex and K-injective resolution are supplied by the dependency APIs
`DerivedCategory.exists_iso_Q_obj_of_isKInjective` and
`HasKInjectiveResolutions.exists_isKInjective`; this is the node's chosen `C → I`.
- Termwise sections `Γ(T_et,M)=M(T)` are the existing
`Sheaf.Γ T.smallEtaleTopology (ModuleCat Λ)` functor (with
`Sheaf.ΓNatIsoSheafSections` identifying terminal-object sections).
- The RGamma clause is exactly
`(AlgebraicGeometry.Etale.rightDerivedGlobalSections (ModuleCat Λ) T).obj K`,
whose definition is `R(Sheaf.Γ T.smallEtaleTopology (ModuleCat Λ))`.
The K-injective computation API `CategoryTheory.Functor.rightDerivedFunctorObjQIso`
identifies this with the derived category object represented by termwise sections of
`I`, and the comparison is independent of the selected resolution.
- The target `D(Λ)` is `DerivedCategory (ModuleCat Λ)`.
- For every `q : ℤ`, the H^q clause is exactly
`(AlgebraicGeometry.Etale.cohomology (ModuleCat Λ) T q).obj K`, since the existing
`cohomology` is `rightDerivedGlobalSections ⋙ DerivedCategory.homologyFunctor`.
- Independence of choices and agreement on `D+` are explicitly properties deferred by
the node, so no extra conclusion was introduced. The existing plus-compatibility API
supports the stated bounded-below agreement. The `Λ = ℤ` sentence and the general
module-structure sentence are correctly explanatory consequences of this specialization.

Edge cases were checked: `q` ranges over all integers (including negative and zero),
`K` is unbounded, zero and acyclic objects are admitted, and no nonzero, characteristic,
Noetherian, finiteness, separation, or universe restriction is added. Empty schemes and
zero rings are not excluded by the binders.

I searched the source with `rg -uuu` and read
`WeilConjectures/SixFunctors/Etale/Derived/LowerShriek.lean`: its declarations
`AlgebraicGeometry.Etale.rightDerivedGlobalSections` and
`AlgebraicGeometry.Etale.cohomology` have exactly the specialized meanings above.
`msearch.py` LeanFinder/Loogle searches and Mathlib/source grep found only generic
K-injective, derived-category, and global-sections APIs, with no separate etale RGamma
notion. The dependency declarations and their signatures were also opened. Therefore
H4 requires using the existing declarations; the former duplicate module was correctly
removed. No mismatch was found in the repaired node or its `lean` record, and no file
requires changes.
