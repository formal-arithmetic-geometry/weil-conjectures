## Worker report

Module: `Sheaf.Paper.PodReindexingCompletedEvaluationReflection`.
Namespace: `WeilConjectures.PodCompletedReflection`.
The primary theorem is `podReindexingCompletedEvaluationReflection`; the other listed
statements and canonical helper constructions collectively render this node. Every theorem
has `sorry` as its whole proof and a source and natural-language proof in its docstring.
All definition data are explicit, or the inverse of a uniquely characterized bijection.
No statement correction, new independent notion, or dependency-record repair was needed.

The source was read at the current blueprint location
`literature/blueprint/latest/blueprint/sec-poincare-duality/sk-thm-frobenius/prop-pod-dual-tate-data-compatibility.proof.md`,
Steps 2 and 4 (the older source-path directory in the node has moved). The additional
reflector refinement is the node's own six-step proof. The local Stacks sources were read:
`algebraization.tex`, lemma-derived-completion (099B),
lemma-derived-completion-koszul (0A0E), and `proetale.tex`, lemma-naive-completion (099M).
The first gives the unit-precomposition Hom bijection, the second its Koszul tower,
and the third its Noetherian quotient-tower identification.

Hypothesis and clause correspondence:

- Prime ell: `(l : ℕ) [Fact l.Prime]`. Finite extension E/Q_l:
  `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
  The valuation ring, uniformizer, positive quotients, completed ring and projections
  are those already used by `podReindexingRing`, `scalarReductionSource`,
  `integralCompletedTensor` and `podReindexCalculus`; no coefficient datum is substituted.
  The implicit positive tower index n encodes exponent n+1 as in the dependencies.
- Schemes and scheme isomorphism: `{X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]`.
  Invertibility on each scheme is exactly
  `[∀ x : X, Invertible (l : X.residueField x)]` and its Y counterpart.
  No field of definition, finite type, separatedness or perfection is added.
- F is the actual inverse image with projection-normalized coefficients:
  `podOrdinaryReindex l E g`. The Hom-model presentation uses
  `podReindexingDerivedFunctor l E g none`; `reindex_eq` identifies these functors
  using uniqueness at every completed coefficient projection. `reindexIso` is the
  equality isomorphism, not a freely chosen site equivalence or map.
- H_W is `hom l E W M N`, exactly `podReindexingDerivedHom ... none` applied to
  `(op M,N)`. `D`, `closed` and `models` abbreviate the recorded ambient category,
  closed calculus and K-flat tensor models. These keep the site object and morphism
  universes u+1 and u and the standard derived localization universe u+2.
- M,N and L belong to `sfIntegralConstructibleCategory l E Y`, the full subcategory
  with derived completeness, constructible positive reductions and one common finite
  cohomological interval. H_Y(M,N) constructible is the explicit binder `hH` only in
  `evaluation`, `constructible_hom`, `restrictedComparison` and the evaluation clause.
  It is not an assumption on the ambient `homComparison` or `tensorComparison`.
- The first displayed bijection is `precompose_bijective`, on the actual function
  `fun f ↦ unit ... ≫ f`; `reflectorEquiv` is `Equiv.ofBijective` for this function.
  `unit` writes precisely the existing reduction adjunction unit, the reduction tensor
  comparison, and inverse normalized Roos tensor realization. This is a canonical
  composite from existing constructions, not an arbitrary isomorphism between limits.
- The second bijection is `ordinaryTranspose`, ordinary Hom-first currying after
  precomposition with `pullbackTensorBraiding`. This fixes the M-first tensor order
  and its Koszul sign. `transpose` composes exactly those two equivalences.
  `reflection_laws` states its normalization and all three variances: precomposition
  in M, precomposition in L, and postcomposition in N. Fullness makes these ambient
  Hom sets precisely the indicated full-subcategory Hom sets when H is constructible.
- The completed tensor is the recorded `integralCompletedTensor`, with its actual
  strict finite-tensor/Roos normalization. The unit definition and bijection proof plan
  identify it as completion of ordinary tensor with the unit-preserving Koszul/quotient
  comparison. No assertion that ordinary tensor is complete occurs, and M is not perfect.
- `evaluation` is the inverse completed transpose of the identity of the actual H.
  `reflection_laws` states both its unit-precomposition equality with ordinary signed
  evaluation and uniqueness among all arrows satisfying that equation.
- The projection-normalized F ≅ Lg* is `podOrdinaryToCompleted`; the main theorem says
  it is an isomorphism on every constructible input. Its `A.completion` obeys the existing
  `PodCompletionReindex.Laws`, and `A.tensor` obeys the existing normalized tensor laws.
- `Comparison` is the ordinary lemma's `PodReindexingCoherence.Comparison` at stage none
  with these same closed structures and K-flat models. Its `derived_model` fixes c⁰
  as the localization of the recorded Hom-resolution comparison, rather than an arbitrary
  natural isomorphism. `homComparison` transports precisely c.derived via `reindexIso`.
  `tensorComparison` transports c.tensor by the identical identification.
- `constructible_hom` asserts H_X(FM,FN) constructible for M,N,H_Y(M,N) constructible.
  `restrictedComparison` uses `ObjectProperty.isoMk` on exactly `homComparison`, so its
  underlying map is the ambient one and no replacement internal Hom is introduced.
- `ReindexingLaws` first states F(unit) followed by μᶜ = μ⁰ followed by unit, for all
  constructible M,L, and then bijectivity of precomposition with F(unit) into FN.
  Its third clause is exactly completed evaluation after 1 completed-tensor c⁰ and μᶜ
  equals F(completed evaluation). The two unit equations and the bijection make this
  precisely the unique extension of the ordinary equation, not just existence of some
  completed evaluation-compatible isomorphism.
- The fourth `ReindexingLaws` clause is the transpose equation for every completed b:
  transpose(μᶜ inverse followed by F(b)) = F(transpose(b)) followed by c⁰.
  The final clause gives contravariant/covariant naturality of the actual ambient c⁰.
  `reindexing_laws` asserts this package for every normalized presentation of the data;
  the main theorem supplies the data and therefore adds no existence assumptions.
- `coherence_iff` states equality of completed maps iff their unit-precompositions agree.
  This is the explicit universal transfer principle for all the requested completed
  coherence squares. `signed_shifts` retains both existing signed Hom shifts through
  `ShiftLaws`, the actual tensor shifts via `PodReindexSignedShifts`, and the explicit
  `RoosFst` and `RoosSnd` equations. The main theorem selects these on the same family.
- `identity_composition` states the identity and successive-isomorphism equations for
  c⁰ with exactly `A.identityDerived` and `A.compositionDerived`, not an unrelated
  compositor. These hold on unbounded inputs; coherence_iff and the evaluation/unit
  equations transport them to completed evaluation. `A.Relabelling`, `A.Identity`,
  `A.Composition`, and `A.TensorConstraints` retain the specified tensor compositors.
- Both normalized Roos coordinates are retained in the very same `A.completion g`:
  `PodCompletionReindex.Laws` includes `RoosFst`, `RoosSnd`, `RoosBoundary`, and signed
  shift compatibility; tensor `Model` localizes that same chain map. `signed_shifts`
  also states both coordinate laws explicitly, with no independently selected maps.

Dependency declarations read and used:

- `Sheaf.Paper.PodReindexingCompletionUnitTensor`:
  `podReindexingCompletionUnit`, `podReindexingCompletionUnitTensor`, and its definition
  owners `PodReindexFamily`, `PodCompletionReindex`, `PodCompletedTensorReindex`,
  `podOrdinaryReindex`, `podReindexCalculus`, `podOrdinaryToCompleted`,
  `PodReindexSignedShifts` and their laws.
- `Sheaf.Paper.PodReindexingHomResolutionModel`: `podReindexingRing`,
  `podReindexingDerived`, `podReindexingDerivedFunctor`, `podReindexingDerivedHom`,
  `podReindexingCoefficient_existsUnique`, `podReindexingHomModel`,
  `podReindexing_hom_resolution_model`; all used through the recorded ordinary Comparison.
- `Sheaf.Paper.PodReindexingEvaluationShiftComposition`:
  `PodReindexingCoherence.Comparison`, `comparison_exists`, `EvaluationLaws`, `ShiftLaws`,
  `ChainShift`, `signedShift`, `composition`, `identity`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `constructibleIntegralTensor`,
  `constructibleIntegralHomPairs`, `constructibleIntegralHom` and its ambient calculus.
  This module is publicly imported as required; no alternative constructible notion is made.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`,
  `sfIntegralConstructibleCategory` (reexported by the completion dependency).
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the original coefficient constructions.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`, via the
  same pro-etale framework. `def-weil-scheme-morphism-properties` is a convention node
  with no declaration; its scheme isomorphism is Mathlib `IsIso`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses` and the unchanged completed ring construction.
- `Sheaf.Paper.ConstantCompletionEquivalence`:
  `CategoryTheory.ConstantCompletion.equivalence`, `koszul_quotient_reflector` and their
  normalized completion units; imported publicly for the stated reflector interpretation.
- `Sheaf.Paper.WeilCompletedTensorReflector`: `Scheme.wfCompletionReflector`, the
  actual completed-coefficient specialization with small-site object/Hom sizes u+1/u.
- Proof-only imports: `Sheaf.Paper.AmbientCompletedTensorAdjunction`
  (`integralAmbientCompletedTensorAdjunction`, `integralConstructible_locallyComplete`),
  `Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction`
  (`CategoryTheory.RingedDerivedNative.closedAdjunction`),
  `Sheaf.Paper.IntegralOperationsPreserveConstructible`
  (`integralOperations_preserve_constructible`). All recorded proof prerequisites are imported.

Edge cases checked before and during writing: empty X or Y; zero M,L,N; ell=2;
positive level exponent 1 (n=0 in the tower); zero, positive and negative signed shifts;
unbounded ambient M,N; nonperfect M and possibly noncomplete ordinary tensor.
The category and universal bijection include these cases. Constructibility is a restriction
only where explicitly stated. The common universe u for scheme and coefficient sizes
is the dependency convention and allows both to be enlarged into any common universe;
it does not equate site object and morphism universes. No new hypothesis restricts a
scheme or the tensor factors to finite type or perfect objects.

Searches for existing statements (2026-10-24):

1. `msearch.py ... leanfinder` query:
   `Completion reflector extends ordinary derived tensor evaluation uniquely to completed tensor and transports internal Hom under scheme isomorphism`.
   Eight results: `LightCondensed.ihomPoints`, its symm lemmas,
   `Scheme.Pullback.Triplet.tensorCongr`, its refl/inv and SpecTensorTo lemmas,
   `LightCondensed.internallyProjective_iff_tensor_condition`. No statement match.
2. `msearch.py ... loogle` query:
   `CategoryTheory.Adjunction, CategoryTheory.MonoidalClosed`.
   Twelve hits, including `MonoidalClosed.ofEquiv`, `Monoidal.Reflective.monoidalClosed`,
   `Monoidal.Reflective.closed` and related generic comparison lemmas. These do not
   identify the actual quotient completion unit, reindexing c⁰ or strict Roos coordinates.
3. `msearch.py ... grep` query:
   `completion.*(homEquiv|Adjunction)|reflective.*closed`.
   Three Mathlib hits in LightCondensed Monoidal and Monoidal Closed Ideal. No match.
4. `rg` on Mathlib, `lean/WeilConjectures`, and `lean/Sheaf` for
   `PodCompletedReflection|Completion.*[Ee]valuation|[Rr]eindexing.*[Rr]eflection`, and
   `grep -rn` for this blueprint id in `lean/WeilConjectures`: no matching statement.
   Broader completion/evaluation searches located the dependency modules and the
   more specialized `PointCompletedEvaluation` (point/perfect models), and downstream
   `DerivedAutomorphismHomEvaluation`/`CompletedTensorHomTranspose` (additional global
   hypotheses and different comparisons). They are not this node's normalized statement.
   The latter's unit expression agrees with the same canonical composite written here;
   importing the downstream proof consumer would reverse the intended dependency.

Validation: all delivered declarations compile through `scompile.py` in both sandbox
and library module modes within the unchanged 60-second per-file limit. No warnings
other than allowed sorry warnings, no auto-bound variables, no local notation, no
file-local instances, no private definitions, and no proofs in definitions postponed.
Every declaration is listed in `lean.declarations`; every postponed theorem carries
this node's blueprint id and the relevant proof steps. Only the item's `lean` record
is changed. No STATEMENT-DISPUTED issue was found.

## Second reading by Q39

No second reading by a worker: the dispatcher explicitly forbids starting other agents;
the maintainer's independent delivery review supplies the independent reading.
