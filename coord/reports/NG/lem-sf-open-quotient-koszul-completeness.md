## Worker report

This delivery states `WeilConjectures.openQuotientKoszulCompleteness` in
`Sheaf.SixFunctors.OpenQuotientKoszulCompleteness`. Its proof is `sorry`, with the
node's eight-step mathematical proof in its docstring. All helper definitions have
real data. The three model structures package comparison maps and the precise
normalizations asserted by this node; their existence is a conclusion of the theorem,
not an extra hypothesis. There are no new independent notions or dependency repairs,
and the DAG node changes only in `lean`.

Hypotheses and clause-by-clause translation:

- Prime: `(l : ℕ) [Fact l.Prime]`. Finite extension: `(E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. The ring, uniformizer, and
  positive quotients are the existing `Padic.coefficientExtensionIntegers`,
  `Padic.coefficientExtensionUniformizer`, and `Padic.coefficientExtensionRing`.
  The natural-number index `n` everywhere means the paper's positive exponent
  `n + 1`; exponent zero is not included.
- Schemes are arbitrary `Scheme.{u}`. Invertibility of ℓ is
  `IsUnit (l : Γ(T, ⊤))`, and separately for U and X in the open clause.
  No field of definition, finite-type, constructibility or boundedness condition
  is introduced. The small site is exactly `Scheme.ProEt`; its objects have
  universe u+1 and morphisms universe u. Coefficient and module sections are
  in u+1. A single common ambient u contains the scheme and coefficient field;
  object and morphism universes of the site are never identified. Three instance
  wrappers expose already available sheafification, local bijectivity, and
  smallness at these sizes, with no extra size hypothesis.
- The strict semilinear calculus is the already recorded
  `coefficientDerivedSystemEvaluationCalculus` witness, exposed as `openDvrSystem`.
  Its reduction, right adjoint, actual unit, evaluated reductions, and projection
  are used directly. This abbreviation selects the normalized universal
  adjunction from the recorded theorem; it constructs no substitute maps.
  Normalization of its reductions is its existing `reduction_normalized` field;
  transition-adjoints retain the recorded calculus meaning.
- The first existential supplies `d : AdicCoefficientDatum R`. The inherited
  `noetherian`, `finitelyGenerated`, `quotientTorsion`, `quotientPerfect`, and
  `quotientFinite` fields express every arithmetic condition. `hd` identifies its
  ideal with the span of the singleton uniformizer, expressed as the range of
  the constant `Fin 1` family used by the recorded Koszul theorem.
- `openDvrResolution n` is literally the mapping cone of multiplication by
  `t^(n+1)` between R in degree zero, hence [R --t^(n+1)--> R] in degrees -1,0.
  The first conjunct asserts a quasi-isomorphism to the specified quotient in
  degree zero, strict bounds -1 and 0, and free, finite, projective terms. This
  is the stated finite-free resolution, and also witnesses perfectness.
- `OpenDvrCoefficientModel.finite` compares the existing finite constant sheaf
  with `completedAdicFiniteRing`, the existing sheafified continuous-component
  function construction. `finite_constants` fixes this map on every quotient
  scalar. `finite_transition` commutes with the actual adjacent quotient maps,
  hence with all composites. `completed` and `completed_projection` identify
  the limits and every limit projection. `modules_functor` requires module
  transport to be restriction along this very ring comparison.
- This uses `AdicCoefficientDatum`, `completedAdicFiniteRing`,
  `completedAdicOrdinaryTower`, and `completedAdicReduction` already publicly
  supplied by the recorded Koszul-reconstruction module. In particular these
  are the exact coefficient category and quotient tower occurring in that
  dependency's theorem signature. The two completed-coefficient interface
  families in the library have different presentation names; no third
  completion, tower, coefficient ring, or intrinsic-completeness predicate is
  defined here. The comparison to the integral constant-sheaf presentation is
  an asserted canonical isomorphism with explicit section/projection laws.
- `OpenDvrCompletionModel.tower` identifies the actual derived strict quotient
  functor with scalar restriction of semilinear reduction, before evaluation or
  total limit. `representative` quantifies over one arbitrary flat-term K-flat
  Q and supplies a complex B of strict towers, a single chain augmentation
  `a : Δ Q ⟶ B`, its strict identification κ with the recorded quotient tensor
  tower, and its derived comparison e with the actual semilinear reduction.
  Equality with `unrestrictedTowerUnit` makes every component x ↦ x tensor 1.
  κ is an isomorphism of entire strict towers, so this also fixes transitions.
- The same `representative` supplies τ comparing the ordinary datum quotient
  complex with the scalar transport of B. Its first equation fixes τ on the
  actual quotient augmentations. These quotient augmentations are epimorphic
  on module sheaves, so the comparison cannot be changed by an unrelated
  automorphism. Its next equation fixes `tower` using the universal derived
  reduction counit and τ. The final equation identifies the actual unit with
  the localization of the whole ordinary strict augmentation followed by the
  universal ordinary-limit-to-total-derived-limit comparison. It does not
  infer equality of derived maps from their finite projections.
- `rlim` compares the existing total right-derived limit functors.
  `limit_model` fixes it by the ordinary projection-preserving limit comparison
  σ on complexes and the universal right-derived comparisons, including all
  localization factor isomorphisms. Thus `tower` and `rlim` are canonical
  normalized comparisons rather than unconstrained isomorphisms of outputs.
- `unit` states `comp = u` after precisely those coefficient, strict-tower and
  limit comparisons. `koszul_unit` uses the specified witness of the recorded
  `koszulReconstruction`. `intrinsic_unit` gives the same equation for the
  actual intrinsic fibre and its (unit-preserving) existing
  `reconstructionKoszulIntrinsicComparison`: this is `c ∘ κ = u`.
  `complete_iff` is the exact equivalence between the existing quotient-Roos
  predicate `IsDerivedCompleteUnrestricted` and invertibility of
  `completedAdicIntrinsicUnit`. The global branch of the recorded
  `IntegralOnSlice.IsComplete` is definitionally this predicate.
- The last conjunct binds `[IsOpenImmersion j] [QuasiCompact j]` and supplies
  `OpenDvrOpenModel`. Its finite restriction maps are fixed by identity on
  constant sections; its completed ring comparison commutes with every finite
  projection; its module equivalence is actual scalar restriction.
  `extension` uses the recorded `OpenTensorNormalization.OpenExtension`,
  including its actual restriction adjunction, exactness, and sectionwise
  unit normalization. Its ordinary functor is therefore extension by zero,
  determined up to the unique adjoint isomorphism, not an arbitrary functor.
  `jShriek` is its exact localization after this canonical coefficient change.
- For every unbounded quotient-complete K the conclusion explicitly asserts
  quotient completeness of `O.jShriek.obj K`, invertibility of the actual
  `openDvrSystem` adjunction unit there, and its exact projection equation with
  `coefficientFiniteAdjunction.unit` and `reductionEvaluation`. The earlier
  `unit` equation applies to every P, including this same extension, and thus
  identifies that invertible map with quotient completion. There is no
  separate assumption that extension commutes with inverse limits.

Dependency declarations used (module, declarations):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and the recorded coefficient ring,
  uniformizer and quotients reexported from `CoefficientExtension`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `CoefficientDerivedSystemCalculus`, `coefficientDerivedSystemEvaluationCalculus`,
  `coefficientSequenceDerivedRestriction`, `coefficientConstantTowerLimit`,
  `coefficientSequenceProjection`, `coefficientFiniteAdjunction`, and
  `coefficientFiniteDerivedRestriction` (the latter public interface helpers
  from `CoefficientRingedSequenceSite`).
- `Sheaf.Paper.DerivedCompleteOnSlices`: `IntegralOnSlice.IsComplete`, with
  global branch `IsDerivedCompleteUnrestricted`.
- `Sheaf.Paper.AdicCoefficientDatum`, and the completed-adic interface publicly
  reexported by `Sheaf.Paper.KoszulReconstruction`: `AdicCoefficientDatum`,
  `completedAdicFiniteRing`, `completedAdicFiniteStep`, `completedAdicCommRing`,
  `completedAdicProjection`, `CompletedAdicModules`, `CompletedAdicTowers`,
  `completedAdicOrdinaryTower`, `completedAdicReduction`.
- `Sheaf.Paper.CompletedConstantSheafReduction`:
  `CompletedConstantReduction.completed_constant_sheaf_reduction`,
  `CompletedConstantReduction.finite_coefficient_identification`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`;
  `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`.
- `Sheaf.Paper.IntrinsicCompletionCompleted`, and the completed-adic intrinsic
  interface publicly reexported by the Koszul-reconstruction module:
  `completedAdicIntrinsicUnit`, `completedAdicIntrinsicCompletion`.
- `Sheaf.Paper.KoszulReconstruction`: `koszulReconstruction`,
  `reconstructionKoszulIntrinsicComparison`, `reconstructionKoszulDerivedUnit`,
  `reconstructionCompletionUnit`, `reconstructionReductionComplexCounit`,
  `reconstructionOrdinaryUnit`, `reconstructionRlimComparison`.
- `Sheaf.SixFunctors.OpenTensorNormalization`: the public `OpenExtension`,
  `restrictRing`, `openInclusion` interface and `SheafOfModules.openTensorNormalization`.
- Scheme-property convention: Mathlib `IsOpenImmersion`, `QuasiCompact`, and
  `IsUnit` for invertibility of ℓ; the convention node has no declaration.

All stated proof-dependency modules are imported. The theorem docstring follows
all eight proof steps, including the regular-generator argument and reflector
needed for the existential Roos convention. Source checks include Stacks
algebraization.tex Tag 0A0E, sites-modules.tex Tag 093M, proetale.tex Tag 09BP,
and the current main-20261015 fix-prop-coherence proof. Tag 09BP does apply to
quasi-compact open immersions; the contrary comment in an older completion
module is not a counterexample to this source statement.

Edge cases checked by reading the definitions and equation types: n=0 here is
A_1 and multiplication by t, not A_0; E=Q_l remains allowed; P=0 and K=0
have zero augmentations and invertible identity completion units; t-torsion
objects remain allowed since flatness is imposed only on the representative,
not on P; the empty scheme and empty open are allowed; j=id is allowed and
reduces to completeness/unit invertibility for K itself. No regularity of a
scheme or boundedness of a complex is implicit in any binder.

Searches for an existing full statement:

- `msearch.py leanfinder`: "Derived completed DVR quotient tower adjunction unit
  Koszul completion and open extension by zero completeness" returned eight
  ordinary adic-completion/valuation hits; no sheaf/strict-tower/open theorem.
- `msearch.py loogle`: `"IsIso", "unit"` returned twelve generic adjunction-unit
  results, none identifying this quotient augmentation or asserting the open clause.
- `msearch.py grep`: `quotient.*[Cc]omplet|[Kk]oszul.*[Cc]omplet` returned
  ordinary Mathlib completion results, no exact match.
- `msearch.py leansearch`: "Derived completion quotient tower Koszul complexes
  extension by zero sheaves" returned general complexes and completion
  declarations, no exact match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for this node id, quotient
  completeness, and Koszul completion found the recorded ingredients and
  related interfaces, but no theorem containing all this node's assertions.
  All notions used in this module are built from those existing declarations.

Validation: the complete module passed scompile.py as both a renamed sandbox
module and its actual library module, without errors or warnings (23.0s and
21.9s respectively). There are no `#check` probes in the delivered file.
There is one postponed theorem and no postponed definition or inline proof.
No statement dispute, statement correction, new node or dependency record
change is needed.

## Second reading by NG

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
