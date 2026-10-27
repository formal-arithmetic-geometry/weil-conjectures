## Worker report

The module `Sheaf.WeilSheaf.NativePullbackStarPreservation` states
`AlgebraicGeometry.WeilComplex.native_pullback_star_preservation`, with a single
`sorry` proof. It states the entire node: two preservation assertions about actual
ambient objects, followed by the identification of both restricted functors on
objects and morphisms. No definitions, axioms, new nodes, dependency repairs or
statement corrections are introduced. Only the item's `lean` record changes.

Hypotheses and clauses, matched against the node:

- Finite field k₀: `(k₀ : Type u) [Field k₀] [Finite k₀]`.
- Prime l different from the characteristic: `(l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]`. This is the existing native framework's convention;
  reversing the inequality does not change it.
- Ω = the algebraic closure of Q_l is fixed inside the dependency's existing
  `ProEtaleWeilSheaf` and adic coefficient constructions; no arbitrary coefficient
  ring or independent topology is substituted. The geometric algebraic closure
  is likewise the native `AlgebraicClosure k₀` geometric fibre.
- X₀ and Y₀ are `X Y : Scheme.{u}`, each with its `Over (Spec (CommRingCat.of k₀))`
  instance. The morphism is `(f : X ⟶ Y)` with `[f.IsOver ...]`.
- Separated finite type of f: `[IsSeparated f] [LocallyOfFiniteType f]
  [QuasiCompact f]`. Separated finite type of each scheme over k₀ is written as
  those same three properties of its structure map. Quasi-separatedness required
  by the existing direct-image restriction follows by instance from separation;
  it is not a new hypothesis. No nonemptiness, smoothness or properness is added.
- D(W_X), D(W_Y) are exactly `DerivedCategory (ProEtaleWeilSheaf k₀ l X)` and
  its Y version, not fixed pairs in a geometric derived category.
- Membership L in WC^der(Y₀) is `objectProperty k₀ l Y L`; similarly for K on X.
  The predicates are applied to arbitrary ambient objects. This is equivalent to
  quantifying over the full subcategory, without choosing representatives.
- The first conjunct applies the full target predicate to
  `(ProEtaleWeilSheaf.upperStar k₀ l f).mapDerivedCategory.obj L`, namely termwise
  exact native pullback on the actual unbounded ambient derived categories.
- The second conjunct applies the full target predicate to
  `(ProEtaleWeilSheaf.lowerStar k₀ l f).rightDerivedFunctor.obj K`, the total
  right derived ordinary direct image. It is not compact-support direct image.
- `objectProperty` is the intersection of `DerivedCategory.TStructure.t.bounded`
  and `DerivedCategory.homologyProperty (WeilSheaf.objectProperty ...)`.
  Consequently both conjuncts assert boundedness AND constructibility of every
  cohomology sheaf, exactly as the final sentence of the node requests.
- The third and fourth conjuncts identify `upperStar f` and `derivedLowerStar f`
  with the restrictions: compose each restricted functor with the target full
  inclusion `.ι`, and equate this to the source inclusion followed by the actual
  ambient functor. Equality of functors covers both objects and morphisms. These
  are the literal full-subcategory lifts defined upstream; proof irrelevance
  removes any dependence on preservation witnesses. No unrequested adjunction,
  exactness or extra cohomological bound is asserted.

Statement dependency used:
`def-sf-native-weil-derived-framework`, recorded on the public entry module
`WeilConjectures.WeilSheaf.LowerShriek`, declaration
`AlgebraicGeometry.WeilComplex.derivedLowerShriek` and its list of constituent
framework declarations. The actual constituent declarations used by this theorem
are `ProEtaleWeilSheaf`, `WeilComplex.objectProperty`,
`ProEtaleWeilSheaf.upperStar`, `WeilComplex.upperStar` from
`WeilConjectures.WeilSheaf.Category`, and `ProEtaleWeilSheaf.lowerStar` and
`WeilComplex.derivedLowerStar` from `WeilConjectures.WeilSheaf.LowerStar`.
The framework module is publicly imported. No private replacement notion is used.

The proof-only imports retain all nine proof-dependency nodes in the stated plan:

- `lem-pod-separated-finite-type-base-change`: Mathlib's
  `IsSeparated.isStableUnderBaseChange`,
  `locallyOfFiniteType_isStableUnderBaseChange` and
  `quasiCompact_isStableUnderBaseChange`, in the corresponding three morphism modules.
- `lem-weil-pbc-finite-type-over-noetherian`: `LocallyOfFiniteType.isLocallyNoetherian`
  in `Mathlib.AlgebraicGeometry.Noetherian` and
  `QuasiCompact.compactSpace_of_compactSpace` in the QuasiCompact module.
- `lem-weil-pbc-qcqs-over-affine`: the same compactness theorem and
  `quasiSeparatedSpace_of_quasiSeparated` in the QuasiSeparated module.
- `lem-sf-locally-finite-coefficient-ring-realization`:
  `AlgebraicGeometry.ProEtale.locallyFiniteCoefficientRing_realization` in
  `Sheaf.Paper.LocallyFiniteCoefficientRingRealization`.
- `lem-sf-native-encoding-derived-operations`:
  `AlgebraicGeometry.ProEtale.NativeEncoding.native_encoding_derived_operations`
  in `Sheaf.Paper.NativeEncodingDerivedOperations`.
- `lem-sf-native-forget-constructible-criterion`:
  `AlgebraicGeometry.ProEtale.NativeEncoding.native_forget_constructible_criterion`
  in `Sheaf.Paper.NativeForgetConstructibleCriterion`.
- `sk-def-sfb-qlbar-condensed`: `Profinite.padicAlgClCondensedRing` and
  `Profinite.padicAlgClRingObj` in
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`.
- `det-thm-sf-ctf-stability-direct-images`:
  `AlgebraicGeometry.ProEtale.CondensedRing.constructibleFiniteTor_stability_direct_images`
  in `Sheaf.SixFunctors.CtfStabilityDirectImages`.
- `def-sf-native-weil-derived-framework`: the public import already listed.

The theorem docstring retains the four proof steps of the reviewed split,
including the coefficient comparisons and reflection of bounded constructibility.
It does not replace that plan by the upstream finiteness proof's SGA citation.
The resolved stage-1 repair note required a re-split, already completed and
reviewed by Q40; this delivery preserves that split and its dependencies verbatim.

Edge cases checked before writing: the zero object remains covered, including
rank-zero constructible sheaves; an empty scheme or empty geometric fibre is not
excluded; identity maps and nonproper open immersions are included; arbitrary
bounded support intervals, including negative degrees, are covered by the native
bounded predicate; no uniform bound for all inputs is claimed. The finite-type
hypothesis includes quasi-compactness of the target, so the unbounded-dimension
infinite disjoint-union counterexample mentioned in LowerStar.lean is excluded by
an explicit node hypothesis. The existing site has object universe u+1, morphism
universe u and coefficients in ModuleCat at u+1; the theorem uses those exact
native categories and adds no universe equality or derived-category model.

Searches performed:

- `msearch.py ... leanfinder`: "Termwise pullback and total right derived ordinary
  direct image preserve bounded constructible native Weil complexes over finite
  fields". Eight hits about generic sheaf pullbacks and finite-limit preservation;
  no native bounded-constructible preservation statement.
- `msearch.py ... loogle`: `"Constructible", "Derived"`. Zero hits.
- `msearch.py ... grep`: `WeilComplex|objectProperty_rightDerivedLowerStar|ProEtaleWeilSheaf`.
  Zero Mathlib hits.
- `rg` in live `lean/WeilConjectures` and `lean/Sheaf` for native upperStar,
  lowerStar, pullback-star preservation, and `objectProperty_rightDerivedLowerStar`.
  Upstream provides direct-image preservation alone in
  `WeilComplex.objectProperty_rightDerivedLowerStar`, and embeds pullback
  preservation in the definition of `WeilComplex.upperStar`. It also defines
  both restricted functors. None states the complete four-clause assertion of
  this node, so the delivery adds only its aggregate proposition and no duplicate
  definitions or copies of individual preservation theorems.
- `grep -rn` of the item id in `lean/WeilConjectures`: no declaration for this id.
- `rg` for `native_pullback_star_preservation` in both library roots and the
  upstream name index: no name collision.

Source read: the current `literature/blueprint/latest/.../sk-thm-sf-ctf-stability/`
statement and proof for clauses (1),(3), plus the recorded native Category,
LowerStar and LowerShriek declarations and their docstrings. All notions needed
by this item already have usable recorded declarations. No statement fault or
STATEMENT-DISPUTED issue was found.

## Second reading by Q68

This dispatcher assignment permits no additional agents; this is a second
in-thread reading, with independent maintainer review still required. I reopened
the node and compared every hypothesis and clause against the theorem signature.
The three separated finite-type assumptions, finite coefficient characteristic
condition, ambient object quantifiers, and full bounded-constructible predicates
match. In particular the direct image is ordinary right derivation on all native
Weil sheaves, and the final two equalities identify the actual named restrictions
as functors, including morphisms. The signature adds no geometric-coefficient
identification, extra map or finiteness hypothesis. The proof-only imports match
the reviewed split. No mismatch required a statement correction.

Validation: prescribed `scompile.py Q68 lem-sf-native-weil-pullback-star-preservation`
compiled this module both as sandbox and with its actual library name, exiting 0
with no diagnostics (13.4 s and 18.1 s in the recorded run). No global or local
Lake build was run. Every Lean line is at most 100 characters; `autoImplicit` is
explicitly disabled and the single universe is bound. A JSON comparison confirms
that the only modified node field is `lean`.
