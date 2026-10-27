## Worker report

This delivery states `WeilConjectures.AmbientPullbackTensor.ambientPullbackTensorCoherence`
in `Sheaf.Paper.AmbientPullbackTensorCoherence`. All theorem proofs are `sorry`;
all definitions have actual data. The natural-language statement and accepted proof split
are unchanged. Helper declarations in this module are coordinates for the same notion,
not replacement module categories, tensor products, or a category of diagrams in a
derived category. There are no new nodes and no dependency-node replacements.

### Hypotheses and ambient objects

- The section binders `ell`, `[Fact ell.Prime]`, `E`, `[Field E]`,
  `[Algebra ℚ_[ell] E]` and `[FiniteDimensional ℚ_[ell] E]` give exactly the
  prime and finite coefficient-field extension. The recorded
  `Padic.coefficientExtensionRing ell E (n+1)` uses its recorded valuation ring
  and chosen uniformizer. It occurs through `integralCoefficientCommRingSheaf`.
- `k₀`, `[Field k₀]`, `[Finite k₀]`, `k`, `[Field k]`, `[Algebra k₀ k]`,
  `[IsAlgClosure k₀ k]` express an algebraic closure of a finite field;
  `_hell : ell ≠ ringChar k` expresses the invertible prime condition.
- The maps `aX`, `aY`, `aZ` to `Spec k`, their `LocallyOfFiniteType` and
  `QuasiCompact` instances, and `_hf`, `_hg` make the schemes finite type over
  k and f,g morphisms over k. No separatedness instance is assumed. The universal
  associativity and unit laws in `CompositionLaws` impose the same hypotheses on
  all additional schemes and arrows that occur there.
- `s : Option ℕ` chooses the setting: `some n` means the positive exponent n+1;
  `none` means the entire semilinear system. `Site`, `topology`, `coefficients`
  select, respectively, the actual small pro-etale site or ℕ-product sequence site,
  its existing topology, and its existing constant or sequence coefficient sheaf.
  `Modules` abbreviates the dependency's `Mod`, hence `ringedSiteModules`, hence
  Mathlib `SheafOfModules`; `Derived` abbreviates its ordinary unbounded localization.
- Scheme universe t and coefficient-field universe u are independent. Site objects
  live in t+1 and arrows in t. Coefficients and module sections live in max u (t+1).
  `siteSmall` states the smallness witness needed by the existing coefficient-universe
  sheafification API; it is a conclusion, not an additional mathematical hypothesis.
- `A`, `B`, `C` and `TA`, `TB`, `TC` name the existing closed derived tensor models
  and their K-flat representative computations (`Closed` and `Models`). These are
  coordinate choices for derived tensor, not extra flatness assumptions on inputs.
  The theorem works with every such model. `TensorData` retains the existing
  `TensorComparisonModel`, including its summand and localization equations.
- The opening mentions of exact j_! and its adjunction are ambient conventions;
  no displayed coherence formula contains j_!. The published exact localized
  module interface is imported unchanged rather than restated.

### Clauses of the conclusion

1. `ringComponent` is the existing constant-section ring map at every index.
   `ringComponent_naturality` includes every arrow of the sequence site, so in
   particular every quotient coefficient transition. `ringUnit`, `ringMap`,
   `moduleRingUnit`, `push`, `pull`, `adjunction` construct the actual ringed-site
   operations. The left adjoint is selected from an adjoint existence property,
   which determines it up to the unique adjunction-compatible isomorphism; this
   is the permitted universal-property construction, not a choice of arbitrary map.
   `pullExact` and its instance projections expose exactness. `derivedPull` is
   literally `pull.mapDerivedCategory`.
2. `baseComp` is the canonical fibre-product base-change comparison, preserving
   the sequence index. `pushComp_existsUnique` specifies its section restriction
   formula on every test object and every section. `pushComp` selects that unique
   isomorphism, and `comp` is its `Adjunction.leftAdjointCompIso` mate. Thus the
   comparator is fixed by the stated direct-image comparison, not supplied as a
   free isomorphism. The unit conjunct of the main theorem is exactly the composite
   adjunction unit equation.
3. The local-generator conjunct is the formula
   `(m tensor a) tensor b ↦ m tensor c_f(a)b`. `generator` is restriction of the
   specified adjunction unit followed by scalar multiplication; `scalar` is the
   image under the constant-ring map and restriction. Every indexing arrow is
   quantified. For `none`, these are morphisms of sheaves on the sequence site,
   already compatible with every semilinear transition.
4. The three `IsIso (ringMap ...)` assertions and the following equation state
   the canonical constant coefficient identifications and the cocycle
   `c_fg = alpha ; pull_f(c_g) ; c_f`. `ringComp` is the mate of the same
   fibre-product ring direct-image comparison, with exactly the item's direction.
5. `CompositionLaws` gives associativity and both unit laws on modules, then on
   derived categories. Canonical `eqToHom` maps account for associativity and unit
   equalities of scheme arrows. Naturality is part of each `NatIso`. `identity`
   is the mate of the section-normalized identity direct image. `derivedComp` and
   `derivedIdentity` are the existing exact-functor localization constructions.
6. `tensorData_existsUnique` defines the canonical tensor comparison by its
   full pure-tensor normalization. `TensorData.Normalized` states the ordinary
   formula `(x tensor y) tensor r ↦ (x tensor r) tensor (y tensor 1)`, simultaneous
   ordinary naturality, invertibility of its total maps and preservation of
   flat-term K-flat representatives. The main theorem asserts this normalization
   for f, g and fg. The representative `model.summand` fixes the total map on every
   direct-sum summand and `model.derived` fixes its localization; no arbitrary
   natural isomorphism is accepted as the canonical tensor map.
7. The ordinary tensor conjunct is the requested equation, written in Lean's
   left-to-right composition order. It is quantified over both actual module
   sheaves. `tensorHom` is the dependency's ordinary sheaf tensor of morphisms.
8. The chain conjunct is the same equation for total complexes, using the inverse
   tensor comparison orientation of `TensorComparisonModel.chain`. P,Q are assumed
   `FlatRepresentative`, exactly the node's K-flat flat-term case. Its square and
   the `model.derived` equations specify that this equality represents the displayed
   derived equality. Successive pullbacks preserve both K-flatness and flat terms
   by applying the normalization at g then f, and at fg.
9. The final universally quantified F,G equation is
   `P_f(mu_g) ; mu_f ; tensor(d_F,d_G) = d_(F tensor G) ; mu_fg`.
   It is the requested equality of natural transformations, stated on every
   object pair. All involved maps are components of natural transformations, so
   componentwise equality is equivalent to their equality. F,G are arbitrary
   objects of the ordinary unbounded derived category. There is no boundedness,
   cartesian-system, flat-transition, or evaluation-detection hypothesis.

### Dependency declarations used

- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`.
- `def-weil-scheme-morphism-properties`: `convention`, `convention`.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`, `AlgebraicGeometry.Scheme.ProEt`.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`.
- `def-weil-pbc-proetale-operations`: `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`, `AlgebraicGeometry.Scheme.proEtaleConstantRingDerivedPullback`.
- `lem-coef-semilinear-derived-sections`: `Sheaf.Paper.SemilinearDerivedSections`, `WeilConjectures.SemilinearSections.semilinearDerivedSections`.
- `lem-weil-pbc-site-morphism-composition`: `WeilConjectures.CategoryTheory.SiteMorphismComposition`, `CategoryTheory.siteMorphism_composition`.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`: `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`, `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
- `def-pc-kflat-complex`: `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`, `CochainComplex.IsKFlatIndependentCoefficients`.
- `def-pc-sheaf-restrict-scalars`: `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`, `SheafOfModules.restrictScalars`.
- `lem-pur-site-restriction-module-adjunction-exact`: `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`, `SheafOfModules.localizedSystemExact`.
- `def-weil-pbc-composite-adjunction`: `Mathlib/CategoryTheory/Adjunction/Basic.lean`, `CategoryTheory.Adjunction.comp`.
- `def-pc-tensor-complex-sheaves`: `Mathlib.Algebra.Homology.BifunctorShift`, `CochainComplex.mapBifunctor`.

The ordinary categories and K-flat models are used transitively through the public
SemilinearDerivedSections imports. All recorded proof-dependency modules that have a
Lean record are imported; the Mathlib proof dependencies are imported by their defining
modules as well. `def-weil-scheme-morphism-properties` is a convention record and has no
module to import. `ProEtaleCoefficientPullbackUniverses` supplies the independent-size
constant-section map, rather than imposing the single-universe intrinsic finite API.
`def-coef-ringed-sequence-site` is used through the public semilinear imports.

### Edge cases checked

- `some 0` is A_1, not the zero quotient at exponent zero. Every positive exponent
  is present, as n+1; the entire system is `none`.
- Identity f or g: `baseId`, `pushId`, `identity` and both sets of unit laws retain
  the actual canonical comparisons. No assumption that pullback is definitionally
  the identity functor is made.
- Empty schemes/sites and zero module objects: all section and generator statements
  remain meaningful; no nonempty indexing object or nonzero-module hypothesis occurs.
- Nonflat quotient transitions (e.g. R/t² to R/t) and arbitrary noncartesian systems
  are included: transitions are restriction arrows in the actual ringed sequence site.
- Unbounded complexes: `CochainComplex ... ℤ`, `totalTensor` and all derived binders
  have no boundedness constraint. Direct-sum totalization and its signs come from
  the existing representative model.
- Nonseparated finite-type k-schemes: only locally finite type and quasi-compact
  structure maps are used, never separatedness.
- A coefficient universe larger than the scheme universe is preserved throughout;
  site object and Hom universes are never equated.

### Searches

The prescribed msearch searches were already completed in the recovered sandbox;
`searches.jsonl` records their exact results (2026-10-23):

- leanfinder: "Canonical pullback composition preserves tensor comparison on ordinary
  unbounded derived sheaves and semilinear systems": 8 hits, including
  `SheafOfModules.pullbackComp`, `pullback_assoc`, and ordinary free-module comparisons.
  None states the simultaneous finite/sequence-site, local-generator and K-flat-normalized
  derived tensor equality of this item.
- loogle: "SheafOfModules.pullback_assoc, CategoryTheory.Adjunction.leftAdjointCompIso_assoc":
  no hits from that combined query. The latter declaration was then read directly in
  Mathlib and is used as the proof-dependency associativity tool.
- grep: "pullback_assoc|pullbackComp|leftDerivedUpperStarTensor": 25 hits, primarily
  ordinary `ModuleCat/Sheaf/PullbackContinuous` and presheaf pullback composition.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `ambientPullbackTensor`, and pullback/tensor coherence: no declaration for the item;
  there are consumer proof comments and generic cochain and ringed-topos comparison
  statements. They do not supply the fixed coefficient cocycle and system laws together.
- `grep -rn` for the exact item id in `lean/WeilConjectures`: no result.
- Read the actual dependencies, especially `SemilinearDerivedSections`,
  `SemilinearSystemModels.TensorComparisonModel`, `CoefficientRingedSequenceSite`,
  `ProEtaleConstantRingOperations`, `ProEtaleCoefficientPullbackUniverses`,
  `ProEtaleTensorCompositionUnit`, `RingedTopoiCanonicalTensorPullbackOfUniverses`,
  `LocalizedModuleExactForSystems`, and the recorded Mathlib signatures.
- Read Stacks `sites-modules.tex` label `lemma-adjoint-push-pull-modules` (03D3)
  and `sites.tex` label `lemma-composition-morphisms-sites` (03CB). Their actual
  adjunction and compositor conventions agree with the module's orientations.

No statement dispute or source correction was needed.

### Validation

The recovered draft compiled with only seven long-line warnings. All seven were
wrapped. The representative chain equality was restricted to the K-flat flat-term
representatives named in the node. The revised file passed both the sandbox and
module-path compilations through scompile.py with no warnings or errors.

## Second reading by Q60

No independent worker was started: the dispatch explicitly prohibits sub-agents and
requires self-delivery. The maintainer's independent review is the second reading.
During the writer's clause-by-clause reread, the seven long lines were fixed and
`FlatRepresentative` hypotheses were added to the chain-level equality to match
precisely the representative clause. The ordinary and derived tensor squares have
opposite chain-comparison orientations as required by `TensorComparisonModel.chain`;
the final derived equation has the exact direction in the node. This is a writer
self-check, not a claim of an independent second review.
