## Worker report

The module `Sheaf.Algebra.Homology.RationalTermHomComparison` states
`CategoryTheory.RationalTermHom.rational_term_hom_comparison`, with one postponed
proof. Its helpers are transparent specializations of the recorded sheaf-Hom,
Hom-complex, single-complex and scalar-localization constructions. No new independent
notion, theorem axiom, private copy of a module category, or arbitrary comparison map
is introduced. Every definition has real data; the only `sorry` is the main theorem.

The statement is unchanged. Its correspondence with the Lean is:

| Natural statement | Lean |
| --- | --- |
| Small site C | `{C : Type u} [SmallCategory C] {J : GrothendieckTopology C}` |
| Commutative ring A and t in A | `(A : Type v) [CommRing A] ... (t : A)`; v is independent of u |
| Sheaf R of commutative A-algebras | `R : Sheaf J CommRingCat.{u}` and `a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)`; the latter is exactly a restriction-compatible family of coefficient ring maps |
| D(R), with induced A action | `DerivedCategory (ringedSiteModules ... R)` under `[HasDerivedCategory.{w} ...]`; the explicitly applied instance lambda supplies `scalarLocalizationCoefficientLinear A R a`, and Mathlib supplies the induced derived linear structure |
| Q_t | `localizedObject` and `localizedMap` are the object and morphism actions of `ScalarLocalization.localization A _ t` after `DerivedCategory.Q` |
| Fixed K-injective resolution j:R[0]→I | `(I : CochainComplex ... ℤ) [I.IsKInjective] (j : single R (coefficients R) ⟶ I) [QuasiIso j]`; no boundedness or functorial replacement assumption |
| Module sheaf F, F[0] | `F : ringedSiteModules ...`, `single R F` |
| R as its own module | `coefficients R := SheafOfModules.unit ...` |
| B(F)=Hom_R(F,R)[0] | `ordinary R F`, using `SheafOfModules.homObj` |
| T(F)=Hom-complex(F[0],I) | `resolved R I F`, using `homComplex` |
| c_F is postcomposition with j | `comparison R e j F := (e F).hom ≫ ((homComplexFunctor ...).obj (op (single R F))).map j` |
| Its ordinary-Hom identification is canonical | The existential `e` is a family of complex isomorphisms, constrained by `IsNormalized R e`: its degree-zero (0,0) projection is the identity on local linear maps, with only the canonical `singleObjXSelf` identifications inserted. All other source degrees are zero, so this determines its chain map uniquely. The existential supplies this canonical identification instead of assuming it as additional data. |
| Some integer m≥0 | Quantification over `(m : ℕ)` |
| R^{⊕m}[0] | `single R (SheafOfModules.free ... (ULift.{u} (Fin m)))`; Mathlib free is the coproduct of m copies of its unit module |
| Localized i,p with pi=1 | The quantified `i,p` have exactly the displayed localized degree-zero source and target, and `i ≫ p = 𝟙 _` uses Lean's left-to-right composition |
| Q_t(c_F) invertible | `IsIso (localizedMap R A t (comparison R e j F))` |
| B(F) direct summand of that same free object | Existential localized maps `i',p'` to and from the same `free ... (ULift (Fin m))`, with `i' ≫ p' = 𝟙 _`; no complement or idempotent-completeness assumption |
| Naturality under module maps | `ordinaryMap R f ≫ comparison ... F = comparison ... G ≫ resolvedMap R I f` as an equality of chain maps |
| Naturality extends A[1/t]-linearly to localized degree-zero maps | Existential families `b,z` of `→ₗ[Localization.Away t]` maps on the actual localized Hom modules of `single R F` and `single R G`. Their values on localized module maps are the specified ordinary/resolved precomposition maps; the final equality is naturality for every localized morphism f. Full faithfulness of the degree-zero derived embedding makes these generators all the required derived degree-zero maps. Linearity specifies the extension on every tensor, including arbitrary sums of pure tensors. |

Dependencies read and used:

- `def-weil-pbc-sites-and-cohomology`: read `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`. Only the associated site topology
  and sheaf convention are needed; no stronger site axiom is assumed.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`,
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`, definitionally Mathlib `SheafOfModules`.
- `def-weil-linear-scalar-localization`: `Sheaf.CategoryTheory.ScalarLocalization`,
  `ScalarLocalization.localization`, its tensor-Hom category and localized-ring action.
- `def-pur-derived-internal-hom`: `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`,
  read `derivedInternalHomOfUniverses` and its arbitrary-representative comparison;
  its public imports provide the K-injective and Hom-complex conventions used here.
- `def-pur-hom-complex`: `Sheaf.Algebra.Homology.HomComplex`,
  `homComplex`, `homComplexFunctor`, and the product/map specification
  `homComplex_exists`, through the already-landed
  `homComplex_projections_exists` interface. `zeroProjection` takes exactly the projections attached to
  the already chosen bifunctor, not a new choice of Hom complex.
- `def-pur-sheaf-hom`: `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`,
  `SheafOfModules.homObj`, `homObjMap`; read the complete signatures and docstrings.
- `lem-weil-linear-abelian-derived-category`: Mathlib
  `Algebra.Homology.DerivedCategory.Linear`, its derived, Q and shift linear instances.
- Added already-landed `lem-weil-pbc-scalar-localization-derived-hom` to `stmt_deps`
  solely for its existing helper `scalarLocalizationCoefficientLinear` in
  `Sheaf.CategoryTheory.ScalarLocalizationDerivedHom`. This installs the canonical
  coefficient action from a, avoiding a duplicate coefficient-action definition.
  The scalar-extension cohomology theorem itself is not assumed here.
- Added already-landed `lem-sc-hom-complex-projections` for
  `Sheaf.Algebra.Homology.HomComplexProjections`, `homComplex_projections_exists`.
  This is the product projection specification of the existing Hom-complex
  functor and avoids reducing its larger existence theorem while elaborating.
- Proof-only imports retain `ringedSite_boundedFree_rhom_model` from
  `Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomModel` and Mathlib's
  `DerivedCategory.instFullSingleFunctor` / `instFaithfulSingleFunctor` from
  `Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`.

Edge cases checked before writing: m=0 permits a retract of the zero object, and
both conclusions say zero after localization. The zero ring and t=0 are allowed:
localization has zero Hom modules and the identity is zero. A unit t recovers the
integral assertion. F=R makes comparison the single copy of j under unit duality.
F=Z/2 over Z with t=2 is zero only after rationalization; no integral comparison
is asserted. Empty sites and zero sheaves introduce no excluded objects. There is
no demand that raw scalar localization split every idempotent. The module and
coefficient universe can be chosen to contain any given small site and sheaf;
A has its own unrestricted universe, and w is the chosen derived morphism universe.

Searches for an existing complete statement (raw service outputs are in the sandbox
`searches.jsonl`):

- LeanFinder, `sheaf internal Hom from a module retract of finite free after scalar
  localization comparison with derived Hom is invertible`: eight unrelated hits on
  free sheaves, generators and sheafification; no localized comparison theorem.
- Loogle, `SheafOfModules.homObj, CochainComplex.singleFunctor`: no match; the service
  does not index the project internal-Hom declaration.
- LeanSearch, `Internal sheaf Hom into a K-injective resolution agrees with ordinary
  sheaf Hom for a finite free retract after scalar localization`: eight hits on
  sheafHom, sheafification and injective resolutions; none states this theorem.
- msearch grep, `homObj|homComplex|ScalarLocalization` in `CategoryTheory`: returned
  ordinary Hom-complex and unrelated functor Hom declarations, no statement match.
- ripgrep in Mathlib, project upstream, shared Lean, and upstream name index for
  `RationalTermHom|rational_term_hom_comparison|homComplexFunctor.*Linear`: no match.
- ripgrep of the item id upstream: no match. Searches for Hom-complex single and
  rational-Hom comparisons found the scheme-specific `homComplex_single_iso` and
  its natural variant, not an arbitrary-site comparison with scalar retractions.
  The existing arbitrary-site bounded-free RHom theorem supplies only the free
  case, so it is imported as the proof dependency rather than recorded as a match.
- Read the source missing from the older checkout using the authorized
  `scompile.py --source WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule`;
  it confirms the coefficient-section Hom module and linear structure used by
  the existing coefficient-action helper.

No statement correction or disputed clause was needed. The existential normalized
identification is uniquely determined by the same product-Hom formula already
specified by the dependencies. The proof docstring carries all three node proof
steps, the inverse in its correct contravariant order, and the finite-free duality.

## Self-check

Reopened the node and read its clauses against the complete module. The retraction
maps and conclusion use exactly the same rank m; the equation has the correct
composition order. Naturality is stated before imposing any finite-free-retract
hypothesis, as required for its application to arbitrary i,p. The extension uses
all localized derived degree-zero Hom groups, rather than only images of integral
maps. The A action is supplied from a explicitly, not left as an arbitrary
`Linear A` assumption. All universes and variables are explicit. The only
postponed theorem is the named main declaration for this DAG node.

## Validation

The full module compiled cleanly through `scompile.py`, both as a fresh sandbox
module and under its final library module name. The first drafts exposed an
elaboration timeout when the category of `ScalarLocalization.localization` was
left implicit. The delivered helpers instead name the derived category in their
result types and give Q_t directly by its existing object wrapper and tensor-with-one
morphism formula. This is exactly the existing localization functor's data, avoids
the expensive category inference, and leaves every mathematical clause unchanged.
Only the prescribed single-file wrappers were used; no global build or direct
change of a shared source was made. The node changes only `lean` and additions to
`stmt_deps` for the two already-landed helpers described above.

## Second reading by Q56

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
