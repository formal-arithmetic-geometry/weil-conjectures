## Worker report

The delivery states `CategoryTheory.RingedKFlatModel.ringed_kFlat_native_model_identification`
in `Sheaf.Algebra.Homology.RingedKFlatNativeModelIdentification`. The single theorem has
proof `sorry`. All six accompanying helper definitions have actual data/formulas; none
chooses an object from a postponed existence assertion. The node statement and proof
are unchanged. Added statement dependencies are the already landed native tensor node
`lem-sf-ringed-derived-native-tensor` and model-data node
`def-coef-ringed-tensor-hom-model`, both used directly.

Clause-by-clause rendering:

- The site is `{C : Type c} [Category.{v} C] (J : GrothendieckTopology C)`.
  Coefficients and modules lie in `max c v u`, independently of site objects and homs;
  `HasSheafify` and `WEqualsLocallyBijective` are the standard small-site interfaces.
  This does not equate c and v, or restrict the auxiliary coefficient bound u.
- `R : Sheaf J CommRingCat.{max c v u}` is the commutative ring sheaf.
  `RingedTensorModules J R` is the recorded `ringedSiteModules`/`SheafOfModules`
  category. `cochainModulesMonoidal` supplies the sheafified tensor. The derived
  universe is the independent `[HasDerivedCategory.{w} ...]` binder.
- `_flatResolution : Abelian.LeftResolution ObjectProperty.flat.ι` is precisely
  the fixed functor into flat objects with natural epimorphism to the identity.
  It imposes no projective, bounded or flat-cohomology hypothesis.
- All representatives are `CochainComplex ... ℤ`. `DerivedCategory.Q` is quotient
  by homotopy followed by quasi-isomorphism localization; its recorded factorization
  is `quotientCompQhIso`. Consequently cochain model equations express the specified
  homotopy model equations, since the homotopy quotient is full and surjective on objects.
- Every total is the existing `coefficientTotalTensor`, itself the recorded signed
  `CochainComplex.mapBifunctor` with direct sums and sign (-1)^p.
- Acyclic-test flatness is exactly `IsKFlatIndependentCoefficients`. Two-sided
  quasi-isomorphism-test flatness is exactly `IsKFlatForTotalTensor`. The first
  conjunct quantifies over EVERY complex P and equates these predicates, without
  flatness of P's terms.
- The ringed tensor is `S.tensor` of the dependency's `CoefficientClosedStructure`;
  `T : CoefficientTensorModels J R S` is its natural simultaneous K-flat model map.
  The independent tensor S is not identified definitionally with the native tensor.
  `β` and `hc : RingedDerivedTensorCoherence J R S T β` express the stipulated
  ringed constraints induced by unsigned reassociation and the degree-zero unit.
- `nativeTensor` transparently names the abstract K-flat monoidal localization
  `RingedDerivedNative.monoidal`, constructed using
  `DerivedCategory.hasDerivedMonoidalCategory`. `RingedDerivedNative.tensorIso`
  is its canonical inverse-tensorator model map. No second native tensor is defined.
- The node's resolving class is rendered explicitly inside `Normalized` and
  `LocalizationNormalized`: both complexes satisfy the acyclic test and every term
  satisfies the recorded `IsFlatOnSite`.
- `Localization` is the type of NATURAL transformations from the ringed tensor
  pulled back to complex pairs to localized ordinary total tensor.
  `∃! ε, LocalizationNormalized ... ε` supplies its missing name by its unique
  characteristic property: ε is the inverse ringed model map on resolving pairs.
  This is the canonical resolution transformation: naturality along resolving
  augmentations forces its value on each arbitrary complex pair. It is not an
  unconstrained map or an added hypothesis. `nativeLocalization` is the actual
  native lax tensorator of Q, with the existing native lax instance explicitly used.
- The existential e is a natural ISOMORPHISM `nativeTensor ≅ S.tensor`.
  `Normalized ... e` says `ra.hom ≫ e.hom = rR.hom` on resolving pairs.
  The next conjunct says every e' with exactly this normalization equals e.
- The next conjunct is `e.hom.app (QU,QV) ≫ ε.app (U,V) = nativeLocalization U V`
  for ALL U,V. It assumes neither input K-flat.
- The one-K-flat conjunct assumes `U.IsKFlatIndependentCoefficients ∨
  V.IsKFlatIndependentCoefficients` and asserts `IsIso` for BOTH transformations.
  No degreewise-flat condition occurs there.
- The following conjunct gives `ra.hom ≫ e.hom = hc.tensorIso.hom` on ALL K-flat
  pairs U,V, again with no termwise-flat restriction.
- `Constraints` writes out the associator square and the two unitor squares for
  every derived X,Y,Z. The units are identified with the SAME recorded
  `Q(ringedTensorUnitComplex J R)` through `RingedDerivedNative.unitIso` and
  `hc.unitIso`. Thus the unit comparison on q(R[0]) is the identity. No equality
  between distinct chosen unit objects is assumed.
- The final “Thus” assertion follows directly by composing any comparison into S
  with e.inv: the all-complex equation gives its native localization equation, and
  the all-K-flat normalization gives its native representative equation. It adds
  no independent mathematical condition beyond the preceding conjuncts.
- Lean composition `≫` is in traversal order, the reverse of the displayed
  right-to-left formulas in the node.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`;
  topology/sheaf specialization used here, with no need to choose actual coverings.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `cochainModulesMonoidal`, `cochainModulesPreadditive`, countable tensor-colimit instances.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`, `Qh`,
  `HasDerivedCategory`; and `Mathlib.Algebra.Homology.BifunctorShift`:
  `CochainComplex.mapBifunctor`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso`:
  `CochainComplex.IsKFlatForTotalTensor` (the required first part of that node).
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`,
  and the exported native `ObjectProperty.flat`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `site_derived_tensor_descent_independentCoefficients`, with its natural model and
  unique transformation-extension clauses; imported for the comparison proof plan.
- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`:
  `RingedTensorModules`, `ringedTensorUnitComplex`, `RingedDerivedTensorCoherence`.
- `Sheaf.Paper.CoefficientRingedTensorHomModel`: `CoefficientClosedStructure`,
  `CoefficientTensorModels.iso`, `coefficientTotalTensor`.
- `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`:
  `DerivedCategory.hasDerivedMonoidalCategory`; the existing ringed specialization
  is `RingedDerivedNative.monoidal`, `.lax`, `.tensorIso`, `.unitIso` in
  `Sheaf.Algebra.Homology.RingedDerivedTensorNative`.
- Proof-only imports are the recorded `TotalTensorHomotopyConeSigns`,
  `KFlatResolutionIndependentCoefficients`, `RingedSiteModulesGrothendieckOfUniverses`,
  and `FlatTermKFlatTensor` modules. The seven-step proof docstring identifies their uses.
- `def-weil-size-convention` is a convention record; explicit universe binders
  implement it and it supplies no declaration/import.

Edge cases checked mathematically before writing: zero complexes and zero ring;
empty site; arbitrary unbounded complexes; contractible complexes with nonflat terms
(the predicates and one-K-flat assertions still apply); Z/2[0] over Z (the all-pair
identity applies but does not assert invertibility); distinct site object/hom universes,
in particular c=t+1 and v=t. Resolving flatness appears only where the node requires it.

Searches actually run using batch2/msearch.py:

- leanfinder: “The two K-flat tests for complexes of module sheaves agree and the
  ringed and abstract derived tensors have a unique normalized natural isomorphism”:
  eight ordinary flat-module tensor exactness hits, no model comparison.
- loogle: `CategoryTheory.Localization.Monoidal.tensorBifunctorIso`: one ordinary
  monoidal localization comparison, not the K-flat two-model theorem.
- grep: `KFlat|tensorBifunctorIso` in `CategoryTheory/Localization`: ordinary
  localization comparison only, no K-flat comparison.
- leansearch: “Unique comparison of derived tensor products normalized on K-flat
  complexes”: total tensor and ordinary flat-module results, no exact theorem.
- grep: `KFlat|[Dd]erived.*[Tt]ensor`: Tor and group-homology results, no exact theorem.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for the node id, new names and
  native-identification/counit patterns found the native tensorator API but no
  declaration asserting all clauses of this item together. The dependency sources,
  including RingedDerivedTensorNative, were read in full at their relevant signatures.

Source verification used the local Stacks sites-cohomology.tex labels definition-K-flat,
lemma-K-flat-quasi-isomorphism, lemma-derived-tor-quasi-isomorphism-other-side,
definition-derived-tor, lemma-symmetric-monoidal-cat-complexes and
lemma-symmetric-monoidal-derived. The latter explicitly omits its proof, as reflected
by the node's agent proof origin. No external source lookup was necessary.

Validation: scompile.py NJ lem-pd-ringed-kflat-native-model-identification on the
single delivered file passed both sandbox mode (23.8 s) and its actual library module
mode (24.8 s), with no diagnostics. Earlier elaboration failures were repaired by
explicit universes and map domains/codomains and factoring the constraint formulas
through generic monoidal structures; the mathematical equations were preserved.

No statement correction, disputed statement, new DAG node or dependency-module repair.
The helper declarations belong to this node's comparison and are all listed in lean.declarations.

## Second reading by NJ

The delivered section under this heading was a self-check by the same worker ("no second
agent was started"; delivery-errors H11). The maintainer's reviewer replaces it with an
independent reading. The reading used the node, its cited Stacks tags (sites-cohomology.tex
06YP, 06YS, 06YT, 06YU, 07A2, 0FPQ, 0FPT) and the Lean module, with every dependency
declaration open.

Node clauses, with the Lean that renders each and the verdict:

- Site (C,J), small relative to the module universe: `{C : Type c} [Category.{v} C]`, modules
  and ring in `max c v u`, with the standard `HasSheafify` and `WEqualsLocallyBijective`
  instances of every ringed-site dependency. c and v are never equated. OK.
- R commutative ring sheaf, M = Mod(R), sheaf tensor: `R : Sheaf J CommRingCat.{max c v u}`,
  `RingedTensorModules J R` (= ringedSiteModules), and the global `cochainModulesMonoidal`
  instance. That instance is `SheafOfModules.monoidalCategory R`, the same one that
  `IsKFlatIndependentCoefficients` installs; the two differ only in a Prop instance
  argument. OK.
- Fixed functorial flat resolutions: `_flatResolution : Abelian.LeftResolution
  ObjectProperty.flat.ι`. This is a hypothesis of the node, and it is unused because the
  native construction uses the project's resolution instance. Harmless. OK.
- K(R), q, unbounded ℤ-complexes, signed totals: `CochainComplex _ ℤ`, `DerivedCategory.Q`,
  and `coefficientTotalTensor` (the recorded mapBifunctor total with sign (-1)^p). OK.
- Acyclic-test K-flat: `IsKFlatIndependentCoefficients`. Two-sided test:
  `CochainComplex.IsKFlatForTotalTensor` from def-sfb-preserves-kflat-quasi-iso (both
  `tensorHom (𝟙 P) s` and `tensorHom s (𝟙 P)`). The resolving class 𝒫 is written out inside
  `Normalized` and `LocalizationNormalized`: both K-flat, and every term `IsFlatOnSite`. OK.
- B_R with model maps r^R and the stipulated constraints: arbitrary `S`, `T`, `β` and
  `hc : RingedDerivedTensorCoherence S T β`. The dependency
  lem-sf-ringed-derived-closed-symmetric-monoidal states ∃ S T β with such a coherence, so
  quantifying over all such data covers the node's B_R. r^R is `T.iso` (= `hc.tensorIso` on
  K-flat pairs by `tensorIso_both`). OK.
- B_a with r^a and ε^a: `nativeTensor` = `@tensor _ _ RingedDerivedNative.monoidal`;
  r^a = `RingedDerivedNative.tensorIso` (the inverse of the lax μ of Q); ε^a =
  `nativeLocalization` = μ of Q, the actual native lax tensorator. OK.
- ε^R: `Localization` is the type of natural transformations
  (Q×Q)⋙S.tensor ⟶ Tot⋙Q. The conclusion asserts `∃! ε` with ε = (r^R)⁻¹ on 𝒫. This is the
  canonical derived-counit: naturality along resolutions forces its values everywhere, and
  the node's Step 3 argument is exactly the uniqueness proof. The uniqueness is asserted,
  not assumed. OK.
- Equivalence of the two tests for every complex: first conjunct, ∀ P, with no flat terms. OK.
- A unique natural iso w with w r^a = r^R on 𝒫: `∃ e : nativeTensor ≅ S.tensor, Normalized e`
  (`(tensorIso P Q).hom ≫ e.hom.app = (T.iso P Q).hom`; ≫ is in the reverse order of the
  node's notation), and `∀ e', Normalized e' → e' = e`. OK.
- ε^R w = ε^a for all U,V: `e.hom.app (QU,QV) ≫ ε.app (U,V) = nativeLocalization U V`. It
  holds for all pairs with no K-flat hypothesis. OK.
- Invertibility when U or V is K-flat: `IsIso` of both ε and nativeLocalization under
  `U.IsKFlat… ∨ V.IsKFlat…`, with no flat-terms condition. OK.
- w r^a = r^R on every K-flat pair: `(tensorIso U V).hom ≫ e.hom.app = (hc.tensorIso U V).hom`
  for both inputs K-flat, without flat terms. OK.
- Associator and both unitors, with unit comparison id of q(R[0]): `Constraints` with
  I = Q(ringedTensorUnitComplex), ua = `RingedDerivedNative.unitIso` and ur = `hc.unitIso`.
  I rederived the monoidal-functor axioms for the identity functor with μ = e⁻¹ and
  ε = ur ≫ ua⁻¹. The associator square is the inverted form. The unitor squares are
  equivalent after naturality of e along ua⁻¹. All hold for all derived X,Y,Z. OK.
- Final "Thus" sentence: this is a formal consequence of the preceding conjuncts (compose with
  e⁻¹). It is not separately stated, which is acceptable.
- "Composition read right to left": the Lean `≫` order was checked against each displayed
  formula. OK.

Edge cases: the zero ring and the empty site (every complex is zero, and all clauses hold
trivially); unbounded complexes; K-flat complexes with nonflat terms (covered by the
one-K-flat and all-K-flat clauses); Z/2[0] over Z (only the all-pair equation applies, with no
invertibility); c = t+1, v = t (universes independent).

Theorem stmt_dep lem-sf-ringed-derived-native-tensor: the statement uses
`RingedDerivedNative.tensorIso` and `unitIso`. These are `asIso` of μ and ε, built from that
theorem node's proved conclusions `isIso_mu` and `isIso_ε`. They are objects constructed from
the theorem's conclusion, so the stmt_dep is genuine.

Searches: rg in live lean/Sheaf and the snapshot for `RingedKFlatModel`, `RingedDerivedNative`
owners and the item id. No existing declaration or parallel module was found, and no def node
owns the RingedDerivedNative declarations. The worker's Mathlib searches were rechecked by
reading Localization/Monoidal and Monoidal/Tor; neither covers this statement.

No Lean or node change by the second reader.
