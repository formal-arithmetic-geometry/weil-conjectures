## Worker report

The module `Sheaf.Paper.PurSequenceProjectionHomNormalization` states
`WeilConjectures.purSequenceProjectionHomNormalization`, with one `sorry` and no
new definitions. It asserts existence of the actual geometric, ordinary and
universal derived projection data, identifies the entire derived Hom bijection
with the supplied calculus, and states its chain-map transpose on every specified
simultaneous K-injective replacement.

Hypotheses and clauses, with the node and source open:

- The global finite-field datum is `F : FiniteFieldDatum.{t}`. Its fields give
  the prime characteristic, finite base field, and fixed algebraic closure.
  `hl : l ≠ F.p`, `[Fact l.Prime]`, `[Field E]`, `[Algebra ℚ_[l] E]` and
  `[FiniteDimensional ℚ_[l] E]` give exactly the coefficient assumptions.
  The valuation ring, uniformizer, quotient rings and completion are the
  existing constructions used by `CoefficientDerivedSystemCalculus`.
- `W : Scheme.{t}`, `[W.Over (Spec (.of F.k))]`, and the `LocallyOfFiniteType`
  and `QuasiCompact` instances give precisely a finite-type scheme over k.
  Its site is the dependency's essentially small `W.ProEt` convention, with
  object universe t+1, morphism universe t, and coefficient universe max u (t+1).
  These universes remain independent. The index n is exponent n+1, so no
  positive quotient level is omitted or zero quotient level inserted.
- `S : CoefficientDerivedSystemCalculus l E W` and
  `hS : CoefficientDerivedSystemCoherence l E W S` fix the supplied calculus
  and coherence. The total-limit functor is the existing
  `coefficientSequenceLimit = coefficientSequenceDerivedRestriction ⋙
  coefficientConstantTowerLimit`, with the dependency's actual exact U.
- `∃ D : PurSequenceResolutionData l E W S` asserts existence, rather than
  assuming the canonical projection or its comparisons. This landed record
  is now an additional statement dependency. It does not assert existence
  in its own definition and introduces no downstream theorem assumption.
- `D.ordinary.p`, `.constant` and `.quotient` specify the ringed projection,
  actual constant-system inverse image and quotient structural map.
  `D.factorization.a`, `.g`, `.a_identity`, `.g_constant`, `.a_quotient`,
  `.g_ring`, `.inverse_comp`, `.direct_comp`, `.ring_comp`, `.modules_comp`
  give precisely p = g after a, including its structural maps.
  `.restriction`, `.limit`, `.exact_limits`, `.exact_colimits` identify
  a_* with exact U and g_* with ordinary limit. The `.towers`, `.sections`,
  and `.transitions` fields retain the actual constant-ring tower category.
- `D.ordinary.pullback`, `.adjunction`, `.limit`, `.tensor`, and
  `.tensor_transition` give p*Q = (Q tensor B_n)_n, p_* = lim U and the
  actual quotient transitions. `.projection_limit` identifies each pi_n
  with the genuine limit projection. `.transpose` expresses the ordinary
  scalar-extension transpose using `purSequenceFiniteAdjunction`: its
  inverse sends x tensor b to b pi_n h(x), and its forward sends f to the
  cone x ↦ (f_n(x tensor 1))_n. The finite adjunction is the recorded
  `scalarReductionExtension_adjunction`, whose tensor-unit normalization
  fixes this formula. Adjunction Hom equivalences are inverse natural
  correspondences of module-sheaf morphisms, so include section restriction
  and horizontal compatibility, not merely maps of unrelated section sets.
- `D.derived.L`, `.R`, `.ε`, `.η`, `.left_derived`, `.right_derived`,
  `.adjunction` give the universal unbounded derived pair and adjunction.
  `.left` is alpha, `.right` is kappa. `.left_model` identifies epsilon
  with alpha and the exact single strict quotient tensor model through
  `CoefficientReductionPresentation`, including all quotient transitions.
- `.right_model` and `.composition_model` fix kappa on every K-injective
  I and every quasi-isomorphism j:UI→J with K-injective J: lim(j) is a
  quasi-isomorphism and represents the comparison under resolution
  identifications. `.model_eq` fixes the model on arbitrary N and every
  simultaneous replacement by the canonical derived U and limit maps.
- The first explicit conjunct quantifies over **all** P, N and
  `v : S.reduction.obj P ⟶ N`, and says
  `S.adjunction.homEquiv P N v =
  D.derived.adjunction.homEquiv P N (alpha_P ≫ v) ≫ kappa_N`.
  Thus equality of entire derived system Hom correspondences is the
  conclusion; equality of evaluated Hom sets is no hypothesis.
- The second explicit conjunct binds a flat-term K-flat Q, K-injective I,
  every chain map f:p*Q→I, every K-injective J and quasi-isomorphism j:UI→J.
  The input `alpha_Q⁻¹ ≫ ε_Q ≫ Q(f)` is f in the supplied reduction model.
  After applying the supplied transpose and the canonical `.model I J j`,
  the output is exactly the localization of the ordinary transpose,
  followed by the ordinary module/limit identification and lim(j).
  The middle map only converts p_*I to lim(UI), as required to type the
  node's displayed formula; it changes no chain map.
- `.unit` and `.counit` identify the supplied unit and counit as precisely
  the identity transposes of this correspondence. Natural isomorphisms,
  adjunction naturality, `.model_eq` for every replacement, and the
  universal-derived properties give naturality and independence of choices.
  Ordinary Mathlib cochain complexes and derived categories retain the
  cochain shift differential (-1)^r d, without adding shift-compatibility
  conclusions from the stronger neighboring shift theorem.

Dependency declarations used (module → declaration):

- `Sheaf.Paper.CoefficientRingedSequenceSite` →
  `coefficientSequenceModules`, `coefficientSequenceRestriction`,
  `coefficientSequenceLimit`, their evaluation and exactness interfaces.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` →
  `CoefficientDerivedSystemCalculus`, `CoefficientDerivedSystemCoherence`,
  `CoefficientReductionPresentation`, `coefficientOrdinaryQuotient`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite` →
  `SheafOfModules.IsFlatOnSite`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients` →
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective` →
  `CochainComplex.IsKInjective`.
- `Sheaf.Paper.SequenceSiteCompletionProjection` →
  `CategoryTheory.RingedToposMorphismOfUniverses` (the recorded independent
  universe interface), also used through the existing resolution data.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic` → `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.Paper.FiniteFieldFiber` → `FiniteFieldDatum`.
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition` →
  `CategoryTheory.ringedToposDerivedPushforwardComposition`: its resolution
  normalization is rendered by the existing `.composition_model`, without
  imposing the narrower original interface's equality of site universes.
- Added landed dependency `def-pur-sequence-adjoint-resolution-data`:
  `Sheaf.Paper.PurSequenceAdjointResolutionData` →
  `PurSequenceOrdinaryAdjoints`, `PurSequenceDerivedAdjoints`,
  `PurSequenceRingedFactorization`, `PurSequenceResolutionData`.

The remaining stated proof dependencies are imported plainly. In particular
`SequenceSiteCompletionProjection` is publicly available through the resolution
data module. No definition or dependency record is replaced.

Edge cases checked: zero complexes and zero morphisms are permitted; W may be
empty; there is no boundedness assumption; Q may be any flat-term K-flat complex;
I may be any K-injective system complex, with no requirement that UI or its levels
be K-injective. J and j are arbitrary simultaneous replacements, including the
identity replacement whenever UI itself is K-injective. No normalization,
completeness, exactness of products, or evaluation-faithfulness hypothesis is added.
Different coefficient and site universes and positive level n=1 are retained.

Searches actually run:

- `msearch.py ... leanfinder`: "The derived Hom adjunction for ringed sequence
  projection agrees with coefficient reduction and total inverse limit under
  canonical K-flat K-injective representative comparisons". Eight results:
  `localCohomology.diagram`, `Adjunction.derivedε_fac_app`, and six projective/
  injective left/right-derived computation lemmas. No specialized whole-system
  correspondence. The generic Mathlib derived-adjunction API was read.
- `msearch.py ... loogle`: `CategoryTheory.Adjunction.derived`. Three results:
  `Adjunction.derived`, `derived_counit`, `derived_unit`; generic infrastructure,
  not the quotient sequence calculus comparison.
- `msearch.py ... grep`: `sequenceProjection|SequenceProjection|derived.*[Aa]djunction`
  in `CategoryTheory`. Three generic derived-adjunction documentation matches.
- `msearch.py ... leansearch`: "Derived adjunction for the constant sequence
  projection and quotient tensor reduction preserves whole system Hom sets and
  canonical resolution transposes". Eight results, including `Adjunction.derived`,
  `Limits.constLimAdj`, `FunctorToTypes.adj`, `Adjunction.derivedη`,
  `constantPresheafAdj`, `Limits.isLimitConeOfAdj_lift`, `Limits.piConstAdj`,
  `Adjunction.derivedε`. None identifies the supplied coefficient calculus.
- `rg` in `lean/WeilConjectures` for the item ID and sequence-adjunction or
  normalization names: no exact statement. `rg` in `lean/Sheaf` found the
  ordinary/derived projection adjunction, its limit-projection theorem, the
  existing resolution-data definition, and the neighboring stronger shift
  theorem. Their signatures and data were read. The data definition is reused;
  the shift theorem has additional coherent-shift conclusions and is not an
  exact existing declaration for this node.
- `rg` in the local Mathlib `CategoryTheory` tree and both project source trees
  for `purSequenceProjectionHomNormalization`, `PurSequenceResolutionData`, and
  related names: the data record exists only in its landed Sheaf module, and
  the proposed theorem name is fresh.

The source was read in the newest blueprint's coefficient-comparison paragraph
and in the local Stacks sources at Tags 03D7, 09T5, 070I and 0D6E. No statement
correction or disputed statement was necessary. The node changes only `lean`
and adds the already-landed definition dependency to `stmt_deps`.

Validation: scompile.py compiled this file separately as both its sandbox module
and its intended library module, with no errors or unexpected warnings (11.9 s
and 8.2 s). The only proof is the required stage-2 `sorry`.

## Second reading by Q23

Author's second reading for direct delivery; the maintainer supplies independent
review. Reopened the node, the complete Lean signature, and all four existing
resolution-data structures. The existential record includes the geometry and
factorization, genuine tensor/limit ordinary adjunction, universal derived pair,
K-flat comparison, lim(j) normalization, and exact unit/counit identifications.
The first conjunct ranges over all derived system morphisms. The second has the
correct direction for alpha (its inverse at the chain-map input), maps lim(j)
in the correct direction, and includes the necessary ordinary limit comparison.
Its output object is the canonical J-model of the fixed total limit. Q's flatness
and K-flatness, both K-injective hypotheses, and QuasiIso j match the node.
No evaluated-Hom equality is assumed, no canonical construction is replaced by
an arbitrary map, and no extra shift conclusion is asserted. The added dependency
is an existing definition with no existence assertion and no dependency on this
item; hence it introduces no dependency cycle. No mismatch remained after this
reading.
