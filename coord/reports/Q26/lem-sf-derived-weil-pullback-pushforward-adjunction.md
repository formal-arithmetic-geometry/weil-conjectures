## Worker report

Item: lem-sf-derived-weil-pullback-pushforward-adjunction. Stage 2, group Q26.

This delivery attaches the existing declaration
`AlgebraicGeometry.WeilComplex.upperStarDerivedLowerStarAdjunction` in
`WeilConjectures.WeilSheaf.Localization` (Localization.lean:191–195).
No Lean module or new declaration is delivered. Only the item's `lean` record
changes; its statement, dependencies, proof and all other fields are preserved.
The declaration is real adjunction data, constructed without a sorry in its own
body; this is a statement attachment, not a claim about its transitive axioms.

### Source and exact statement match

Read the complete target node, both statement dependencies, the framework's
recorded definitions in Category, LowerStar, LowerShriek, OpenImmersion and the
Adic coefficient modules, and the preservation theorem's signature/docstring in
`Sheaf.WeilSheaf.NativePullbackStarPreservation`. Also read the resolved stage-1
repair note: its accepted re-split does not require any stage-2 statement change.
Read the current blueprint at
`literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/fix-lem-tensor-adjunction.proof.md`,
Step 1, final Hom equivalence. It explicitly invokes `Lf^* ⊣ Rf_*`.
The node specifies its native derived-Weil realization, and names the selected
existing declaration as its attachment candidate.

Every hypothesis of the node is accounted for:

- The finite field is `{k₀ : Type u} [Field k₀] [Finite k₀]` in the upstream
  section. The prime and invertibility hypotheses are `{l : ℕ} [Fact l.Prime]`
  and `[Fact (ringChar k₀ ≠ l)]`. The coefficient is the framework's fixed
  `PadicAlgCl l`, not an arbitrary coefficient ring or a chosen substitute.
- The schemes are `{X Y : Scheme.{u}}` equipped with
  `[X.Over (Spec (CommRingCat.of k₀))]` and the analogous instance for Y.
  The map is `(φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]`.
- The node's finite-type morphism gives `[LocallyOfFiniteType φ]` and
  `[QuasiCompact φ]`; its separatedness supplies `[QuasiSeparated φ]`.
  The existing declaration requires those three hypotheses and no stronger one.
- The separated finite-type structure maps of X and Y are retained in the
  compile probe. The existing declaration only needs
  `[LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]` and
  `[QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]` from them. Thus it applies
  directly under every stated hypothesis. Its validity in the greater
  generality of qcqs morphisms does not restrict or alter this node's datum.
- No closure or Frobenius data is newly chosen: the categories and functors
  use the same geometric fibers, algebraic closure and geometric Galois
  Frobenius as the recorded framework.

Every clause of the conclusion is accounted for:

- The objects are the actual `WeilComplex k₀ l Y` and `WeilComplex k₀ l X`,
  the full subcategories of the native derived categories cut out by
  `WeilComplex.objectProperty` (bounded cohomology and constructible underlying
  cohomology sheaves). This is not a fixed-pair category formed after derivation.
- The declared type is exactly
  `WeilComplex.upperStar (k₀ := k₀) (l := l) φ ⊣ WeilComplex.derivedLowerStar φ`.
  Category.lean defines the left side as the full-subcategory lift of the
  termwise exact native inverse image's `mapDerivedCategory`. LowerStar.lean
  defines the right side as the lift of the native direct image's
  `rightDerivedFunctor`. These are precisely the framework's restricted functors.
- For every T and N the requested bijection is
  `(WeilComplex.upperStarDerivedLowerStarAdjunction φ).homEquiv T N`.
  Its domain is `upperStar.obj T ⟶ N` and its codomain is
  `T ⟶ derivedLowerStar.obj N`. `Equiv` supplies both inverse identities.
- Naturality in the two variables is provided by the adjunction API,
  `Adjunction.homEquiv_naturality_left` and
  `Adjunction.homEquiv_naturality_right` (Mathlib Adjunction/Basic.lean).
- The restriction clause is not inferred from the type alone: the definition's
  body is
  `(ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction k₀ l φ).restrictFullyFaithful`
  with the two `ObjectProperty.fullyFaithfulι` inclusions and two `Iso.refl`
  comparisons. Read the full `restrictFullyFaithful` construction in Mathlib.
  It composes the inclusions' Hom equivalences with the ambient Hom equivalence.
- The ambient adjunction is the existing
  `ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction k₀ l φ`, whose body is
  `(ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l φ).mapDerivedCategoryRightDerivedAdjunction`.
  Read that construction: it applies `Adjunction.derived` to the termwise
  homotopy adjunction, using `mapDerivedCategoryFactorsh.hom` and the actual
  `rightDerivedFunctorUnit`. Thus this is the specified derived adjunction.
- Actual unit and counit: Mathlib's
  `Adjunction.map_restrictFullyFaithful_unit_app` and
  `Adjunction.map_restrictFullyFaithful_counit_app` identify their images with
  the ambient components. Both comparison isomorphisms here are identities,
  so the formulas reduce to those exact components. Likewise the transposition
  maps are composition with this unit and counit, by `homEquiv_apply` and
  `homEquiv_symm_apply`. No arbitrary adjunction or arbitrary natural bijection
  is substituted.
- Preservation is separately stated, as required by the node. The existing
  functors already include their preservation witnesses; the item merely
  attaches their specified adjunction. There is no additional preservation
  assertion or altered preservation hypothesis in this delivery.

### Dependencies used

`def-sf-native-weil-derived-framework` records
`WeilConjectures.WeilSheaf.LowerShriek` as its public entry module. Its primary
name is `AlgebraicGeometry.WeilComplex.derivedLowerShriek`; the exact notions
needed here, all listed in its `lean.declarations`, are
`AlgebraicGeometry.WeilComplex`, `AlgebraicGeometry.WeilComplex.objectProperty`,
`AlgebraicGeometry.ProEtaleWeilSheaf`,
`AlgebraicGeometry.ProEtaleWeilSheaf.upperStar`,
`AlgebraicGeometry.ProEtaleWeilSheaf.lowerStar`,
`AlgebraicGeometry.WeilComplex.upperStar`, and
`AlgebraicGeometry.WeilComplex.derivedLowerStar`. Read their complete signatures,
docstrings and construction bodies. Their owning modules are Category and
LowerStar, publicly imported through the framework entry module.

`lem-sf-native-weil-pullback-star-preservation` records
`Sheaf.WeilSheaf.NativePullbackStarPreservation`, declaration
`AlgebraicGeometry.WeilComplex.native_pullback_star_preservation`.
Its first two conjuncts assert both ambient preservation properties; its last
two conjuncts identify exactly these restrictions through the inclusions.
The signature and docstring were read. The existing attachment needs no new
consumer module importing this statement; its DAG dependency is unchanged.

The two other proof dependencies are already recorded as
`Sheaf.WeilSheaf.NativeInjectiveAdjunctionModel` /
`AlgebraicGeometry.nativeWeilInjectiveAdjunctionModel` and
`Sheaf.WeilSheaf.NativeDerivedHomComparison` /
`AlgebraicGeometry.ProEtaleWeilSheaf.derivedHomComparison`.
They remain the node's stage-3 proof plan, unchanged. No new module is written
whose proof imports could need updating.

### Edge cases and universes

Checked the empty scheme, the zero complex, identity morphisms and open/closed
immersions: the declaration has no Nonempty, nonzero, surjectivity, properness,
positive dimension or immersion hypothesis. Its Hom equivalence is defined for
every pair of objects, including zero objects. It does not require semisimple
Frobenius or a special Frobenius eigenvalue. All bounded complexes, with arbitrary
finite cohomological range and arbitrary shifts, are allowed. The coefficient
prime is arbitrary subject to the stated inequality; characteristic 2 is not
excluded. The common `u` is exactly the framework's universe convention; the
underlying sites/categories retain their framework universe increases.

### Searches

All prescribed searches preceded attachment:

- msearch.py, leanfinder: `Exact inverse image of Weil complexes is left adjoint
  to right derived direct image with its actual derived unit and counit`:
  eight generic sheaf/module adjunction hits, no native Weil match.
- msearch.py, leansearch: `Derived pullback is left adjoint to right derived
  pushforward on Weil complexes`: eight generic pullback/sheaf hits, no exact
  native Weil declaration.
- msearch.py, loogle:
  `CategoryTheory.Adjunction.derived,AlgebraicGeometry.WeilComplex.upperStarDerivedLowerStarAdjunction`:
  zero hits; the native identifier is not in the search index.
- msearch.py, grep:
  `upperStarDerivedLowerStarAdjunction|derivedUpperStarLowerStarAdjunction`:
  zero Mathlib hits.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for these names located
  the exact native construction at Localization.lean:191, its ambient
  construction at line 175, and upstream consumers. Other similarly named
  etale and coefficient adjunctions operate in different categories.
- Direct search for this item's id in `lean/WeilConjectures` found no hit;
  the exact declaration is documented under the localization blueprint id.
  Direct search in `dag/lean_names_upstream.json` and `lean/Sheaf` for the exact
  restricted adjunction name found no duplicate declaration.

No new nodes, dependency repairs, statement corrections or disputed statements.
The resolved stage-1 repair note was read and its accepted split preserved.

### Validation

A scratch module-mode probe with `autoImplicit false` imports the exact upstream
module, checks both adjunction signatures, and checks its `homEquiv T N` with
all of this node's finite-field, characteristic and separated finite-type
hypotheses explicitly bound. Only scompile.py is used for compilation.
The delivery wrapper also checks the recorded existing declaration on the server.
The probe passed both sandbox and library checks (22.6 s and 19.3 s), with no
errors or warnings. Its inferred type is the requested Hom equivalence under
all the node's hypotheses. The compiler also confirms that the restricted
adjunction retains the characteristic inequality and that the ambient one
needs no such additional hypothesis beyond the native category datum.

## Second reading by Q26

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
