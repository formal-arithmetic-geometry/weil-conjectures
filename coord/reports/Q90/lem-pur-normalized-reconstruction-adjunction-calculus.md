## Worker report

The delivery states `lem-pur-normalized-reconstruction-adjunction-calculus` in
`Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus`. There are three postponed
theorems, all clauses of this same node: `purNormalizedReconstruction`,
`purRestrictedUnitCounit`, and `purNormalizedReconstructionAdjunctionCalculus`.
Every theorem has proof `by sorry` and a source/proof-plan docstring. All definitions
contain actual data. There are no new nodes, dependency repairs or statement corrections.

Source read: current `main-20261015` blueprint,
`sec-smooth-purity/sk-thm-purity-transport/prop-pur-adic-reconstruction-trace-coherence.proof.md`,
sole proof paragraph: the realized trace is the transported counit, and reconstruction
includes transport and compatible composition. The item is the agent-extracted
intermediate lemma, not a verbatim blueprint assertion. Its seven proof steps were
read and supplied in the theorem docstrings: normalized reduction on K-flat
representatives; effectivity and counit; derived Nakayama and unit; restriction to
replete subcategories; transported counit; transpose; composition and transformations.

Hypothesis and clause correspondence:

- Prime ell: `(l : ℕ) [Fact l.Prime]`. Finite extension E/Q_l:
  `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
  The valuation ring, chosen uniformizer and actual quotients are the recorded
  `Padic.coefficientExtensionIntegers`, `Padic.coefficientExtensionUniformizer`
  and `Padic.coefficientExtensionRing`, not new coefficient data.
- Scheme W and invertibility of ell: `W : Scheme.{t}` and
  `hl : IsUnit (l : Γ(W, ⊤))`. The final statement separately binds X, Y, Z
  with independent scheme universes and their invertibility hypotheses.
- Small pro-etale site and size convention: inherited actual `W.ProEt`,
  `Scheme.ProEt.topology W`, site objects in t+1, morphisms in t, coefficients
  and module sections in max u (t+1), with the standard derived localizations.
  No equality of the coefficient universe and scheme universe is imposed.
- B_n and completed R: the recorded `integralCoefficientSheaf` and
  `completedIntegralCoefficientSheafUnrestricted`; zero-based Lean level n
  means exponent n+1. The recorded completed sheaf is the inverse limit,
  not a discrete constant integral ring.
- Strict semilinear systems with componentwise maps and their unbounded derived
  category: `coefficientSequenceDerived l E W`, imported without alteration
  from `CoefficientRingedSequenceSite` through the evaluation-calculus module.
- Normalized subcategory: `IsNormalizedCoefficientSequence l E W`, the
  universal Hom formulation of invertibility of every transition-adjoint for
  m ≥ n, including identities. Its identification with the actual finite
  derived-scalar-extension adjunct is the dependency's
  `coefficientSequenceTransitionAdjoint_isIso`.
- Complete subcategory: the recorded `IntegralOnSlice.IsComplete l E W none`,
  definitionally `IsDerivedCompleteUnrestricted`, retaining the augmented
  reduction-tower Roos-triangle definition. No new completeness predicate.
- The specified reduction/limit adjunction: parameter
  `S : CoefficientDerivedSystemCalculus l E W`; `S.reduction` is its
  K-flat-representative reduction functor, `coefficientSequenceLimit` is exactly
  total derived limit after scalar restriction, and `S.adjunction` is its
  specified adjunction. Existence of S is the already stated
  `coefficientDerivedSystemEvaluationCalculus`; this parameter names the
  adjunction in the node and is not an extra mathematical hypothesis.
  No hypothesis of reconstruction, boundedness, constructibility, finite Tor
  interval or a local model is imposed.
- Reconstruction: `purNormalizedReconstruction` states that normalized N has
  complete L(N), its actual `S.adjunction.counit.app N` is invertible, and
  the actual unit at every complete K is invertible. Their normalization to
  total-limit projections and actual reduction maps remains exactly
  `S.counit_projection` and `S.unit_projection` from the dependency. Naturality
  remains that of these actual natural transformations.
- The full/replete subcategories are `purNormalizedProperty Q` (normalized ∧ Q)
  and `purCompleteProperty S Q` (complete ∧ Q applied to the reduction).
  `Q : ObjectProperty ...` with `[Q.IsClosedUnderIsomorphisms]` selects any
  replete full subcategory. Q = top gives the whole normalized category.
  Conversely any replete full subcategory of normalized systems is realized
  by its ambient iso-closed object predicate; normalization is itself invariant
  under isomorphism. Thus this encoding covers all of the node's subcategories.
- `purRestrictedReduction` and `purRestrictedLimit` act by the actual ambient
  functors and maps. The latter uses completeness of L(N) and Q transported
  along the inverse of the actual counit. `purRestrictedAdjunction` restricts
  the original adjunction along the full inclusions and identity comparison
  squares. `purRestrictedUnitCounit` asserts both invertibility and equality
  with the ambient unit/counit after inclusion. `purReconstructionEquivalence`
  is `Adjunction.toEquivalence` of this particular adjunction, so preserves
  its actual unit and counit without adjointification or arbitrary choices.
- F and G and their adjunction are quantified in `PurReconstruction.Calculus`.
  `realized` is R_X followed by F followed by L_Y; `realizedAdjunction`
  composes the three specified adjunctions. These are definitions, not
  existentially supplied functors or an unrelated adjunction.
- Counit formula: `Calculus.counit` is L_Y F(e_X at G R_Y K), followed by
  L_Y(epsilon at R_Y K), followed by `eY.unitInv.app K`. Composition is in
  Lean's left-to-right `≫` order, exactly the node's right-to-left formula.
- Transpose: `Calculus.transpose` quantifies P, N and a : P → G N. It uses
  the inverse of `realizationComparison eY eX G` to put L_X(a) into the
  correct Hom set, applies the inverse transported Hom equivalence, and
  identifies the result with `realizationComparison eX eY F` followed by
  L_Y(F(a) ≫ epsilon_N). These identifications are actual natural
  isomorphisms formed by whiskering the actual counit; their naturality
  for arbitrary system maps is part of their type, not omitted.
- Composition: `compositionComparison` is a natural isomorphism obtained by
  whiskering the middle system counit. `Calculus.composition` explicitly
  identifies its component with L_Z H(e_Y at F R_X K).
- Naturality for transformations: `realizedTransformation` is the actual
  whiskered transformation. `Calculus.transformation` gives the commuting
  square for arbitrary alpha : F → F' and beta : H → H', hence in either
  variable as a specialization.
- The primary theorem specializes the entire calculus to the three actual
  reconstructed (possibly restricted) categories. All F, G, H and adjunctions
  are quantified only between these subcategories; no ambient extension of
  them is required.

Dependency declarations and source interfaces read:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing` and imported coefficient constructions.
- `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`, `Scheme.ProEt` and `ProEt.topology`.
  The size-convention node is a universe convention, with no declaration.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`,
  `integralConstantToCompletionOfUniverses`, reexporting the actual completed
  integral coefficient sheaf and finite quotient cone with independent universes.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`,
  `CoefficientDerivedSystemCalculus`, `coefficientDerivedSystemEvaluationCalculus`,
  its `reduction`, `adjunction`, `reduction_normalized`, `unit_projection` and
  `counit_projection`; also the recorded system normalization and limit above.
- `Sheaf.Paper.NormalizedDVRTower`, `NormalizedDVRTower`; the system predicate
  uses the same universal finite scalar-extension normalization criterion.
- `Sheaf.Paper.DerivedCompleteOnSlices`, `IntegralOnSlice.IsComplete` at `none`.
- Proof-only imports: `Sheaf.Paper.NormalizedDVREffectivity`,
  `normalizedDVRTower_effectivity`, and `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`,
  `SheafOfModules.changeOfRings_isKFlat_of_flat_terms`. The proof dependency
  `sk-lem-pe-derived-nakayama` has no Lean record on this base; no fictional
  import is supplied. Its intended use is recorded in the proof docstring.
- Mathlib `ObjectProperty.lift`, `ObjectProperty.fullyFaithfulι`,
  `Adjunction.restrictFullyFaithful`, `Adjunction.toEquivalence`,
  `Equivalence.toAdjunction` and `Equivalence.symm` were read to ensure the
  constructions retain the specified units and counits.

Edge cases checked before and during writing: level zero means exponent one, not
exponent zero; m=n is included; there are no bounds on complex degrees; zero
complexes and the empty scheme are permitted. Q may be top or bottom, so full
and empty replete subcategories are included, with no Nonempty assumptions.
Identity F, H and identity transformations are allowed, and both naturality
variables are arbitrary. In the transpose the inverse right-side comparison
has the necessary direction L_X G N → Gbar L_Y N. Independent X/Y/Z site
universes are preserved. The node and dependencies have no identified statement
fault; no STATEMENT-DISPUTED flag is warranted.

Searches actually run (via prescribed msearch wrapper unless noted):

- LeanFinder: `Derived complete complexes and normalized coefficient systems are
  equivalent via reduction and total inverse limit with transported adjunction
  counit` — eight Dold–Kan/normalization hits, no coefficient reconstruction match.
- Loogle: `CategoryTheory.Adjunction, CategoryTheory.Equivalence` — six hits,
  including `Equivalence.toAdjunction`, `toAdjunction'`, `trans_toAdjunction`,
  `Adjunction.toEquivalence`, a sheafification transport and an algebra/coalgebra
  equivalence. The general adjunction APIs are used; none states this node.
- LeanSearch: `Derived reduction and total inverse limit restrict to an equivalence
  between complete complexes and normalized systems` — eight Dold–Kan and
  ordinary inverse-system hits, no match.
- Mathlib grep: `normalized.*[Rr]econstruction|reconstruction.*[Aa]djunction`
  in CategoryTheory — zero hits.
- Direct rg in both upstream WeilConjectures and project lean/Sheaf:
  `normalized.*[Rr]econstruction|NormalizedReconstruction|reconstruction.*[Aa]djunction`
  — only comments about other reconstruction comparisons in
  CompletedExchangeCoherence and ProEtaleSupportedReconstruction; no matching
  declaration. Upstream grep by this exact node id returned no hits.
- Name-collision rg for `PurReconstruction|purNormalizedReconstruction|
  purRestrictedReduction|purCompleteProperty` in Mathlib, upstream WeilConjectures,
  lean/Sheaf and dag/lean_names_upstream.json — zero hits before this delivery.

Validation uses only scompile.py file compilation and deliver2.py preflight;
no direct compiler or global build, no live edits, and no direct git commands.
The first compile found an explicit asIso argument-count error and missing
Functor namespace opens; both were repaired. Subsequent final-path results
and delivery preflight are recorded by the wrapper output.

## Second reading by Q90

Reopened the item and the completed module and traced each clause against the
Lean, as listed above. In particular checked that the chosen adjunction retains
the actual S.unit/counit after inclusion, that completeness is the recorded
Roos-triangle predicate, and that no arbitrary coefficient-comparison map or
equivalence is selected. Checked the directions of both e-induced identifications
in the transpose, the order of the three counit factors, and the two-variable
transformation square. The full-subcategory version quantifies the functors on
the smaller categories themselves. No mathematical mismatch was found; the two
elaboration fixes described above changed no statement. This is the dispatcher's
author rereading; the independent delivery review is performed by the maintainer.
