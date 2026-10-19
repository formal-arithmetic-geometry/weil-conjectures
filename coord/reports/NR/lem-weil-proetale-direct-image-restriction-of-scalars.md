## Worker report

Item: `lem-weil-proetale-direct-image-restriction-of-scalars`.

The module `Sheaf.AlgebraicGeometry.ProEtaleDirectImageRestrictionOfScalars`
states `AlgebraicGeometry.Scheme.proEtaleDerivedDirectImage_restrictScalars`.
There are two postponed theorems: this theorem and the uniquely normalized
underived identity-on-sections comparison. Both have complete proof docstrings.
All definitions have real data; the underived comparison is selected from an
existence-and-uniqueness theorem whose sectionwise normalization determines it.
No proof was filled. No statement correction or disputed statement is needed.

Hypotheses and clauses, individually:

- A scheme morphism f is `{X Y : Scheme.{u}} (f : X ⟶ Y)`; no condition
  whatsoever is imposed on f or the schemes.
- Finite commutative rings are `{A B : Type u} [CommRing A] [CommRing B]
  [Finite A] [Finite B]`, and the unital ring homomorphism is `(φ : A →+* B)`.
- The original small sites are `ProEt.topology X` and `ProEt.topology Y`.
  Their objects still have universe u+1 and morphisms universe u. No equality
  of those universes is assumed. Coefficients are lifted to u+1 exactly as in
  the recorded `proEtaleDerivedCategory`.
- The induced ring-sheaf map on either site is
  `(constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
  (CommRingCat.ofHom φ.ulift)` (and similarly for Y). This is sheafification
  of the actual constant-presheaf homomorphism, not an arbitrary ring-sheaf map.
- Restriction is `proEtaleCoefficientRestrictScalars X φ`, an abbreviation
  for the existing `proEtaleRingRestrictScalars` and thus Mathlib's
  `SheafOfModules.restrictScalars`, forgetting commutativity through sheafCompose.
  It retains the underlying abelian sheaf and restricts its scalar action.
- Exactness is supplied by `proEtaleRingRestrictScalars_properties`. The two
  explicit instance aliases register its finite-limit and finite-colimit
  conclusions for this constant-coefficient abbreviation; they prove nothing
  new. The derived restriction is `.mapDerivedCategory`, Mathlib's termwise
  triangulated descent, with its canonical `.mapDerivedCategoryFactors`.
- The unbounded ordinary K-injective-derived direct images are
  `proEtaleConstantDerivedDirectImage f A` and its B version. Their definitions
  use `.rightDerivedFunctor` of the recorded canonical sectionwise direct image,
  in the same `proEtaleDerivedCategory` as the site dependency. They impose no
  boundedness, completion or constructibility restriction.
- The natural isomorphism is the existential `d` between restriction-then-RfA
  and RfB-then-restriction, exactly the direction of the node (Lean's `⋙`
  lists the functor applied first on the left). An isomorphism in the functor
  category includes naturality for all derived objects and derived morphisms.
- Every K-injective B-complex J is quantified as a `CochainComplex` with
  `[J.IsKInjective]`; every K-injective A-resolution is quantified as I with
  `[I.IsKInjective]` and a chain map j from the termwise restriction of J with
  `[QuasiIso j]`. Restriction is NOT assumed to preserve K-injectivity.
- The equality `f_* Res J = Res f_* J` is represented by
  `proEtaleCoefficientDirectImageComparison f φ`, uniquely determined by its
  identity action on every section n over every test object W. This expresses
  the stated equality despite propositional differences of scalar-action data.
- The first normalization conjunct asserts `QuasiIso (fA.mapHomologicalComplex.map j)`.
  The second says that, after `mapDerivedCategoryFactors`, the canonical
  `rightDerivedFunctorObjQIso` for J and I, and the identity-on-sections
  identification, d followed by Q(fA j) equals the A-resolution identification.
  Since Q(fA j) is invertible by the first conjunct, this is exactly the specified
  inverse-of-f_*(j) formula, for every resolution and with no arbitrary choices.

Dependency declarations used (all names below in AlgebraicGeometry.Scheme unless
qualified otherwise):

- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: `proEtaleDerivedCategory`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage` (retained publicly through the
  recorded `ProEtaleCoefficientPullbackUniverses` interface):
  `proEtaleConstantRing`, `proEtaleBaseChange`, `proEtaleConstantModuleDirectImage`.
- `Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction`: all the
  arbitrary identified-coefficient module and derived operations remain publicly
  available; in particular `proEtaleRingModules` and its K-injective resolutions.
  The dependency module delivered here adds the canonical constant specialization.
- `Sheaf.AlgebraicGeometry.ProEtaleModuleDirectImageLeftExact`:
  `proEtaleConstantModuleDirectImage_additive_leftExact`, used for additivity.
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`:
  `proEtaleRingRestrictScalars`, `proEtaleRingRestrictScalars_properties`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`; `Mathlib.CategoryTheory.Sites.ConstantSheaf`:
  `CategoryTheory.constantSheaf`; `Mathlib.Algebra.Ring.ULift`: `RingHom.ulift`.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective` (nullhomotopy of every map from an acyclic complex).
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategory`, `mapDerivedCategoryFactors`,
  and its triangulatedness instance.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective`:
  `CategoryTheory.Functor.rightDerivedFunctorObjQIso` (canonical inverse derived
  unit on a K-injective representative).
- Stated proof tools are imported: `RingedToposDerivedPushforwardComposition`,
  `ExactFunctorDerivedFunctor`, and `RingedSiteKInjectiveResolutions`. The
  remaining recorded proof-dependency interfaces occur in their import closure.

The two added statement dependencies are already landed nodes:
`lem-weil-pbc-ring-sheaf-change-adjunction` and
`lem-weil-proetale-module-direct-image-left-exact`. Their recorded declarations
are used directly, with no copied notion or duplicated theorem.

Edge cases checked: empty source or target schemes, zero coefficient rings,
identity coefficient maps, noninjective and nonsurjective ring maps, and the
nonflat map Z/4 → Z/2. No nonzero, flatness or invertibility hypothesis is added.
Unbounded complexes and the zero complex are retained. All universes and variables
are explicit, with `set_option autoImplicit false` in both modules. The finite-ring
universe convention matches the already recorded site interface.

Searches performed through msearch.py (results are also recorded in searches.jsonl):

- LeanFinder: "Unbounded derived pushforward commutes with restriction of scalars
  along a ring homomorphism": eight hits, including underived pushforward
  comparison and section formulas. None gives the normalized unbounded theorem.
- Loogle: `SheafOfModules.restrictScalars`: four hits, the actual restriction
  functor, its additivity instance and two formulas, all reused.
- grep of Mathlib `Algebra/Category/ModuleCat/Sheaf`:
  `restrictScalars|pushforwardComp`: thirteen hits, underived constructions only.
- LeanSearch: "Derived pushforward commutes with restriction of scalars for
  sheaves of modules": unavailable, Internal Server Error.
- rg of upstream WeilConjectures and side lean/Sheaf for restriction, derived
  direct images and constant coefficients found the general ring-sheaf-change
  comparison, which requires identified coefficient isomorphisms, and the canonical
  sectionwise direct image, which does not. Read the full signatures/docstrings.
- Upstream `SixFunctors/ProEtale/ScalarExtension.lean` has an underived comparison
  for sheaves valued in ModuleCat, not this unbounded normalized theorem for the
  recorded SheafOfModules constant-ring-sheaf category. It was not duplicated.
- rg of Mathlib, upstream WeilConjectures and side lean/Sheaf for all new declaration
  names found no collision. Upstream search for this item's id found no declaration.

Sources read: the full blueprint definition `def-weil-derived-direct-image`,
order 1468, including the finite-level K-injective construction and coefficient-tower
sentence; Stacks sites-cohomology.tex, `lemma-derived-pushforward-composition`
(Tag 0D6E), and the node's explicit K-injective normalization proof. The existing
constant-ring-map prerequisite was examined, but the direct constant-section
construction below removes the need to supply its inverse-image isomorphism merely
in order to name Rf_*. Its mathematical theorem is neither assumed nor duplicated.

Validation: both modules compiled separately in dependency order through scompile.py,
with no errors or warnings. The main theorem includes the explicit resolution
normalization, not just an uncharacterized Nonempty isomorphism.

## Dependency modules

`def-weil-pbc-proetale-operations`: the recorded interface exposed Rf_* only after
supplying an isomorphism f⁻¹R ≅ S. For constant coefficients the previous worker
therefore waited for the unstated constant-ring-map theorem merely to name the
canonical direct image. Section 1(B) is used to expose
`proEtaleConstantDerivedDirectImage`, the identical K-injective `.rightDerivedFunctor`
of the already recorded `proEtaleConstantModuleDirectImage`, using its canonical
constant-section ring map directly. `ProEtaleConstantDerivedDirectImage` publicly
imports the complete old operations and canonical adjunction module, so every
arbitrary identified-coefficient operation is retained. It registers additivity
from the already landed left-exactness theorem. There is no new coefficient map,
arbitrary isomorphism, Nonempty choice, changed site, changed category or new
hypothesis. Only the dependency's lean record changes, with this explanation in
lean.note. The item's mathematical statement and proof plan are unchanged.

## Second reading by NR

I read the item statement against the blueprint source `def-weil-derived-direct-image`,
order 1468 (the sentence introducing the finite-level tower maps), and against Stacks
Project, sites-cohomology.tex, Section 21.20, Tag 0D6E
(`lemma-derived-pushforward-composition`) and Tag 0D6J
(`lemma-modules-abelian-unbounded`). The source assumes only a morphism of schemes and
the coefficient change between finite commutative rings; it imposes no condition on
the morphism, no flatness, boundedness, constructibility, characteristic, or
injectivity condition.

The statement-by-statement match is:

- The scheme morphism is rendered by `{X Y : Scheme.{u}}` and `f : X ⟶ Y`; no
  property of `f`, `X`, or `Y` is added.
- The finite commutative rings and their unital map are rendered by
  `{A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]` and
  `φ : A →+* B`. The shared universe is the pro-etale site convention, and does
  not remove any finite coefficient case in that convention.
- The induced constant ring-sheaf map is rendered by
  `(constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
  (CommRingCat.ofHom φ.ulift)` (and the corresponding map on `Y`).
- Restriction of scalars is rendered by
  `proEtaleCoefficientRestrictScalars X φ`, the recorded
  `proEtaleRingRestrictScalars`, hence Mathlib's unchanged-underlying-sheaf
  `SheafOfModules.restrictScalars`. The finite-limit and finite-colimit instances
  register its exactness, and `.mapDerivedCategory` is the resulting termwise
  triangulated functor.
- The two derived direct images are rendered by
  `proEtaleConstantDerivedDirectImage f A` and `... f B`, the canonical
  K-injective `rightDerivedFunctor` of the sectionwise pro-etale direct image in
  the recorded derived categories.
- The natural isomorphism is rendered in exactly the node's direction by
  `(Res X).mapDerivedCategory ⋙ Rf_*^A ≅ Rf_*^B ⋙ (Res Y).mapDerivedCategory`.
  The underived comparison is the identity-on-sections isomorphism
  `proEtaleCoefficientDirectImageComparison f φ`; its orientation is the inverse
  direction needed inside the normalization equation.
- The K-injective normalization quantifies over a B-complex `J`, an A-complex
  `I`, and a quasi-isomorphism `j : Res J ⟶ I`, with both K-injective instances.
  The displayed equation expands the node's phrase “the inverse of
  `f_* Res J = Res f_* J ⟶ f_* I`” through the canonical derived-category
  factorization isomorphisms and `rightDerivedFunctorObjQIso`. Its first conjunct,
  `QuasiIso (f_*^A j)`, is the explicit well-definedness condition implicit in
  taking that inverse and is supplied by the recorded Tag 0D6E composition
  interface; it adds no hypothesis.

Edge cases were checked: `f` may be an identity, an empty-scheme morphism, or any
other morphism; `A` or `B` may be the zero ring; `φ` may be noninjective,
nonsurjective, or the identity (including `Z/4 → Z/2`); complexes may be zero or
unbounded; and no characteristic assumption is present. The explicit `u`/`u+1`
site and coefficient universes preserve the small pro-etale convention.

The searches were repeated with `msearch.py` (LeanFinder, Loogle and grep) for
derived direct image plus restriction of scalars, and with `rg` over Mathlib,
`WeilConjectures/`, and this project's `lean/Sheaf`. The hits are underived
`SheafOfModules.restrictScalars`, pushforward formulas, and generic derived
functor infrastructure only. No existing declaration gives this normalized
unbounded comparison, and no declaration-name collision was found. LeanSearch was
unavailable; that failure is recorded in `searches.jsonl`.

No mismatch was found in the item's statement or its Lean rendering, so no
statement correction, citer audit, or edge-case restriction was needed. The only
delivery repair is the authorized §1(B) dependency interface: the copy of
`def-weil-pbc-proetale-operations` now records
`Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage`, exposing the canonical
constant-coefficient K-injective derived direct image while retaining the original
identified-coefficient operations. Both delivered modules compile cleanly with
`scompile.py`.
