## Worker report

The module `Sheaf.Paper.PodReindexingHomResolutionModel` states the full node in four
named theorems, all with `sorry`: `podReindexingCoefficient_existsUnique`,
`podReindexing_resolution_preservation`, `podReindexing_hom_resolution_model`, and
`podReindexing_roundTrip_shift` (namespace `WeilConjectures`). Its other declarations
are explicit constructions or abbreviations of the recorded dependency constructions.
There is no statement correction, new node, or dependency-module repair. The node copy
changes only `lean`, which lists every declaration.

Sources read: the current blueprint at
`literature/blueprint/latest/blueprint/sec-poincare-duality/sk-thm-frobenius/prop-pod-dual-tate-data-compatibility.proof.md`,
Steps 1--2, and the item's complete eleven-step proof. The node's historical source
path uses `sk-lem-finite`; the current blueprint places the same ancestor in
`sk-thm-frobenius`. The source path is preserved in the node. Stacks anchors are 03EL,
0GMX, 0A8X, 0A95, 079I, 08J7, and the ring-sheaf limit construction 03CO.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Prime ell; finite E/Q_ell, valuation ring, uniformizer | `(l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`; the existing `Padic.coefficientExtensionRing` uses the dependency's valuation ring and chosen uniformizer. |
| Small pro-etale sites of X and Y | `X Y : Scheme.{u}`, `X.ProEt`, `Y.ProEt`, and `ProEt.topology`; site objects have universe `u+1`, morphisms `u`. |
| g an isomorphism | `(g : X ⟶ Y) [IsIso g]`; the inverse is the actual `inv g`. |
| ell invertible on both schemes | `[∀ x : X, Invertible (l : X.residueField x)]` and the identical Y binder on the three comparison/preservation theorems. The coefficient existence helper is valid independently of this geometric restriction. |
| Either B_(W,n), n >= 1, or R_W | `s : Option ℕ`; `some n` means the existing `integralCoefficientCommRingSheaf l E W n`, whose exponent is `n+1`; `none` means `completedIntegralCommRingSheafUnrestricted l E W`. Every positive exponent occurs. |
| F is reindexing with canonical coefficient identifications | `podReindexingFunctor` abbreviates `isoSectionwiseModuleInverseImage g` with the ring map obtained by forgetting commutativity in `podReindexingCoefficient`. Its action is restriction of scalars along the inverse coefficient isomorphism, so the underlying sections are unchanged. |
| Finite coefficients are the canonical identifications | First conjunct of `podReindexingCoefficient_existsUnique`: the forgotten finite map equals `isoSectionwiseConstantMap`, which is uniquely normalized on constant sections. |
| Completed coefficient map commutes with every projection | Second conjunct: `c none ≫ completedIntegralCommRingProjectionUnrestricted ... X n = F(projection ... Y n) ≫ c (some n)` for every n. The entire family is unique, not merely nonempty. |
| Exact equivalence of module categories, inverse reverse reindexing | First four clauses of `podReindexing_resolution_preservation`: an actual equivalence with functor equal to `podReindexingFunctor g` and inverse equal to `podReindexingFunctor (inv g)`, plus additivity and preservation of finite limits and colimits. |
| All small limits and colimits | `PreservesLimitsOfSize.{w,z}` and `PreservesColimitsOfSize.{w,z}` with explicitly declared independent size variables w,z. |
| Flat modules, K-flat and K-injective complexes | The final quantified clauses use precisely `SheafOfModules.IsFlatOnSite`, `CochainComplex.IsKFlatIndependentCoefficients`, and `CochainComplex.IsKInjective` from the dependencies. Quasi-isomorphisms are also preserved, so the corresponding resolution augmentations remain quasi-isomorphisms. Applying the same statement to `inv g` gives reverse preservation and reflection. |
| Canonical tensor and Hom comparisons on local sections | The main theorem quantifies isomorphisms σ,η and states `σ(s ⊗ t) = Fs ⊗ Ft` using the existing `purTensorSection`; for η it evaluates at every arrow V→U and every input section, giving exactly the original local linear map evaluated at its reindexed arrow. These equations determine the comparisons and therefore their naturality in both module inputs. |
| Actual Hom-complex isomorphism, arbitrary K and K-injective I | `χ K I hI` is an isomorphism in `CochainComplex`, using the dependency's actual `homComplex` on both sides. There is no boundedness hypothesis. |
| Product over all integer p in every integer r; normalized components | The equation with `homComplexπ ... r p (p+r) rfl` says that each projection of `χ.hom.f r` is F of the original product projection followed by η on `(K.X p, I.X (p+r))`. The existing projections exhibit precisely the stated products. |
| Differential d_I f - (-1)^r f d_K | Both endpoints are the recorded Hom complexes, with the exact sign fixed in `homComplex_d_π`. Since χ is an isomorphism of actual complexes, its `hom.comm` equation is the required differential compatibility. This is stronger information than cohomology-object isomorphisms and is the node's requested chain-level clause. |
| Naturality; quasi-isomorphism invariance in both inputs | The next equation states the commuting square for all precomposition maps a and postcomposition maps b. The next clause states that its reindexed Hom map is a quasi-isomorphism when a,b are and both targets are K-injective. The square identifies this with the corresponding Hom map after reindexing. It makes no claim for arbitrary second-variable targets. |
| Natural derived isomorphism for all ordinary unbounded objects | δ is a natural isomorphism of bifunctors `H_Y ⋙ DF ≅ (DF.op.prod DF) ⋙ H_X`, where `H` is exactly the recorded `derivedInternalHomOfUniverses` and DF the exact termwise `mapDerivedCategory`. This quantifies the full derived categories, not their constructible or bounded subcategories. |
| Represents χ; independent of representatives | Final main-theorem equation evaluates δ at `(QK,QI)` and equates it to F of the specified Hom model, the canonical exact-functor localization factorization, Qχ, the inverse target Hom model, and the two input localization comparisons. `podReindexingHomModel` is explicitly `Localization.fac` followed by the inverse of the localized `Hom(K,I→I₀(I))`; it does not select an arbitrary isomorphism from a Nonempty theorem. The natural δ and this equation implement descent and representative independence. |
| Both reverse composites are identities on coefficient projections and actions | `podReindexing_roundTrip_shift` first states equality of the double coefficient map with the canonical restriction along the inverse site round trip. The projection equations above imply identity on every quotient projection. The theorem applied to `inv g` gives the other composite. Its module equivalence has unit and counit sections equal to the original restriction maps along these same identity-on-underlying-scheme site identifications. These are module morphisms, hence also identify their scalar actions. |
| Termwise unit and counit of derived equivalence | `podReindexingLiftedEquivalence` is the existing `Equivalence.mapDerivedCategory` applied to that normalized module equivalence; the final theorem identifies its forward and inverse functors with the specified exact derived functors. The imported construction defines its unit and counit by localization of the module unit/counit, applied termwise via `mapDerivedCategoryNatIso`. |
| Shift comparison identity in every degree | `∀ K n i, (((podReindexingComplexFunctor ...).commShiftIso n).hom.app K).f i = 𝟙 _`, including every integer shift. The derived functor and factorization are the existing shift-compatible descent of this exact termwise functor. |
| Finite functor is specified Lg_n^* | Last clause: a natural isomorphism to the recorded `finiteDerivedPullback l E n g`. Its categories are definitionally the recorded finite coefficient categories, with positive exponent n+1. |
| Completion is ordinary ring inverse image before tower comparison | `s = none` still uses `mapDerivedCategory` of the ordinary completed-ring module reindexing. No derived completion or quotient-tower pullback is substituted. |

The `EssentiallySmall.{u+1}` binders in the K-flat preservation and main Hom statements
are the allowed, derivable size interface from brief-stage2 §2. They do not identify
site universes or impose a mathematical restriction: `essentiallySmallSelf` supplies
them for the `Type (u+1)` site. All other universes are explicitly declared. There is
no auto-bound term variable, local notation, local instance, or private definition.

Dependency declarations read and used (including imported constructions of each module):

- `Sheaf.Paper.DerivedPullbackTensorHom`: `WeilConjectures.finiteDerivedPullback`,
  `finiteCoefficientRing`, `finiteIntrinsicDerivedInternalHom` and its ordinary ambient
  ring-sheaf Hom construction. The integral/rational/common-stage operations are not
  substituted for ordinary completed inverse image.
- `Sheaf.Paper.PurInverseImageTensorHom`: `AlgebraicGeometry.Scheme.inverseImage_tensor_hom_iso`;
  its public definitions include `purTensorSection` and the existing general ring-sheaf
  module inverse image. The local tensor/Hom normalizations specialize this result.
- `WeilConjectures.Algebra.Homology.HomComplex`: `CategoryTheory.homComplexFunctor`,
  `homComplex`; `...HomComplexComponents`: `homComplexπ`, `homComplexIsLimit`,
  `homComplex_d_π`, and the componentwise map formulas.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom` publicly reexports
  `CategoryTheory.derivedInternalHomOfUniverses`,
  `derivedInternalHomOfUniverses_inverts`, and the representative comparisons from
  `...DerivedInternalHomOfUniverses`. The ordinary-ModuleCat specialization named as
  the dependency's primary declaration is not used as a substitute for site modules.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`
  and the reexported `coefficientExtensionRing`, `coefficientExtensionIntegers`,
  `coefficientExtensionUniformizer`, `coefficientExtensionTransition`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` publicly reexports
  `WeilConjectures.completedIntegralCommRingSheafUnrestricted`,
  `integralCoefficientCommRingSheaf`, `completedIntegralCommRingProjectionUnrestricted`,
  `integralCoefficientSheafSystem`; these are the recorded completion construction,
  with commutativity retained, without an extra finite-field datum.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective` (dependency's exact Mathlib match).
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, an
  abbreviation for the exact `SheafOfModules` category used here.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`;
  the actual tensor product is `siteSheafTensorRight` from its public imports.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory.standard`, `DerivedCategory.Q`, `isIso_Q_map_iff_quasiIso`.
- `def-weil-scheme-morphism-properties` is explicitly a convention with no declaration;
  schemes, isomorphisms, and residue fields use the named Mathlib notions directly.
- Proof dependency `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`:
  `Scheme.isoSectionwiseInverseImage`, `isoSectionwiseConstantMap`,
  `isoSectionwiseModuleInverseImage`, and its exactness/additivity instances.
- Proof dependency `WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap`:
  `CategoryTheory.quasiIso_homComplex_map`. Its import is public because the explicit
  Hom-model definition uses this theorem in its data construction.
- Proof dependency `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`:
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`;
  publicly available through the recorded derived-Hom dependency as well.
- Proof dependencies `Mathlib.CategoryTheory.Limits.HasLimits` (`limit`, `limit.π`) and
  `Mathlib.Algebra.Homology.BifunctorShift` (`CochainComplex.mapBifunctor`).
- Derived-equivalence construction is the existing
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Equivalence.mapDerivedCategory`, exact-functor factors and natural-isomorphism descent.

Edge cases checked before and during writing: the empty scheme and zero module/complex
are admitted; g may be the identity; `some 0` is exponent one, not the excluded exponent
zero; `none` is the inverse-limit ring, never the discrete constant integer ring;
K can be unbounded in both directions, p,r range over all integers, and n in the shift
clause can be zero or negative. The limit/colimit size variables are independent, so
empty diagrams and every existing small diagram are included. No infinite-product
exactness or boundedness is assumed. The quasi-isomorphism clause requires both Hom
targets to be K-injective, exactly as in proof Step 9. In the round-trip section
formula the input lies over the twice-reindexed object and the right side restricts
along the inverse site isomorphism; this variance was checked explicitly.

Searches actually run:

- `msearch.py ... leanfinder "Exact inverse image equivalence of ringed sites preserves K-injective and K-flat resolutions and unbounded derived internal Hom"`:
  eight hits, including `Functor.mapDerivedCategory`, `mapDerivedCategoryFactors`,
  `CochainComplex.IsKInjective.Qh_map_bijective`, and exact-functor Ext maps; none
  states this coefficient-normalized chain/derived comparison.
- `msearch.py ... loogle "CochainComplex.IsKInjective, CategoryTheory.Equivalence"`:
  zero hits.
- `msearch.py ... grep "IsKInjective.*(map|equiv)|homComplex.*(Iso|iso)|reindexingHom" Algebra/Homology`:
  seven hits in KInjective, KProjective, derived KInjective and Plus files; none gives
  the ringed-site coefficient/projection normalized comparison.
- Initial `msearch.py ... grep "reindexing|Hom.*resolution|reindex" WeilConjectures`:
  zero hits (this was a search-service subdirectory query, not the project-source check).
- `rg -n "reindex|Reindex|resolution_model|resolutionModel|lem-pod-reindexing-hom-resolution-model" lean/WeilConjectures lean/Sheaf`:
  numerous unrelated reindexing constructions and relevant sectionwise inverse-image
  interfaces, no exact statement. Narrow `rg` for the item id and expected declaration
  names, including `dag/lean_names_upstream.json`, found no existing declaration.
- Local source search for `homComplex` projections found the already published
  `HomComplexComponents` API; this is reused, not copied.

Validation: `scompile.py Q04 lem-pod-reindexing-hom-resolution-model` compiled the delivered
module in sandbox and library module mode with no errors or warnings (18.2 s and 12.8 s
before the final explicit dependency-import/format pass). All verification uses the
prescribed wrapper and live server build; no local/global build or repository edit.
Dry-run and final delivery results are recorded below when completed.

## Second reading by Q04

This is this worker's separate source-and-statement re-read; the dispatcher explicitly
forbids starting another agent, and the maintainer performs the independent delivery
review. I do not represent this as an independent worker's review.

Reopened the original node, its eleven proof steps, and the complete final module.
Checked every row above against actual binders/conclusions. Found and repaired three
interface details during the re-read: the Hom abbreviation initially left the module
universe implicit (now all Hom universes are fixed to the stated site/module sizes);
the derived model equation needed the two localization input comparisons as well as
the output comparison (now included, and it is a homogeneous equality of morphisms);
and contravariance reverses the site round-trip arrows in the scalar composite,
module unit and counit (now source-typed and compiled). The completed coefficient
choice is made only from `∃!` with every projection pinned. The Hom-model isomorphism
is explicit and uses the actual canonical K-injective replacement arrow, rather than
an unspecified existence choice. The four `sorry`s correspond to the four portions
of this single DAG statement, and each has its source and the relevant full proof
steps in its docstring. No mathematical statement fault or disputed clause remains.

Final validation: the explicit dependency-import/format pass compiled cleanly in sandbox
and library modes (7.5 s and 9.7 s). `deliver2.py ... --no-push` printed
`OK (dry run): commit 770bbf789a3 passes the preflight and compiles; nothing pushed`.
A source/JSON comparison confirms `lean` is the only changed node field, every Lean
line is at most 100 characters, and exactly the four named theorem proofs are `sorry`.
