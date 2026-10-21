## Worker report

The module `Sheaf.Paper.IsomorphismScalarComparisonAgreement` states
`WeilConjectures.isomorphismScalarComparisonAgreement`, with its sole proof `sorry`.
It compares the actual specified ambient derived morphisms. No definition, dependency
record, natural-language statement, or proof plan is changed; no new node is needed.

Hypothesis and clause correspondence:

- A prime ell is `(l : ℕ) [Fact l.Prime]`.
- Finite extensions E and L of Q_ell are the two `Type u` parameters with `Field`,
  `Algebra ℚ_[l]`, and `FiniteDimensional ℚ_[l]` instances.
- Their inclusion is `(ι : E →ₐ[ℚ_[l]] L)`. A homomorphism of fields is injective;
  using embeddings rather than literally nested subfields does not change the data.
  The coefficient nodes fix the valuation rings, chosen uniformizers, and quotient rings.
  No unramifiedness or finite-level flatness is assumed.
- The scheme isomorphism is `{X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y)
  [IsIso g]`. Invertibility of ell on each scheme is encoded by the two pointwise
  `Invertible (l : _.residueField _)` instance binders, as in both comparison interfaces.
- `D : IntegralComparisonSystem.{u} l` exposes the normalized whole-system realization
  data used to specify (i). It is not an arbitrary arrow, an added geometric hypothesis,
  or an assumption that the desired equality holds. Its coefficient pullback and scalar
  models carry `IsIntegralComparisonPullbackNormalized` and
  `IsIntegralComparisonScalarNormalized`; their equations test the actual K-flat
  quotient presentations and pure-tensor generators. The theorem works for every such D.
  This is the same parameterization used by the existing consumer
  `pullbackIdentities_scalarExtension`.
- `K : sfIntegralConstructibleCategory l E Y` is exactly membership in D^b_c(Y,O_E).
  Its `property.1` is derived completeness; `property.2` supplies all positive finite
  constructible reductions and one common finite cohomological interval.
- The operations T_W and Lg_F^* are the existing `integralScalarExtension` and
  `integralDerivedPullback`, on the same completed coefficient sheaves.
- Map (i), mu inverse after lambda, is
  `(integralComparisonScalar l E L ι D g K).hom`. Reading its definition gives
  `integralComparisonLambda ... ≪≫ (integralComparisonMu ...).symm`.
  Those definitions use the whole-system counits and generator-normalized system
  scalar/pullback associator, retaining the quotient diagram.
- Map (ii) is `(scalarPullbackCompleted ...).hom`. Its existing definition is chi_X
  inverse, followed by the ordinary scalar/pullback comparison, followed by Lg_L^*(chi_Y).
  `specifiedPullbackComparisonAlpha` identifies that exact map with localized delta_P,
  where `scalarPullbackChain` acts on BOTH Roos coordinates and
  `integralScalarCompletionChain` has zero shifted coordinate. Its first existential
  witness supplies the required proof of completeness of Lg_E^*K. The signature uses
  `.choose` only for this proposition-valued proof, not for any object, functor, or map;
  proof irrelevance makes the map independent of that witness.
- The conclusion is equality `=` of these two `.hom` terms in the ambient
  `DerivedCategory (integralTowerModules l L X)`, namely D(X_proet,O_L). It neither
  asserts merely isomorphic endpoints nor tests equality only after finite reduction.

Dependency declarations read and reused (all names below are in `WeilConjectures`
unless a namespace is explicitly given):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`; its public coefficient module supplies
  `Padic.coefficientExtensionIntegers`, `Padic.coefficientExtensionUniformizer`,
  `Padic.coefficientExtensionRing`, and the actual quotient transitions.
- `def-weil-scheme-morphism-properties` is explicitly a convention node with no
  declaration. The existing Scheme, residue-field and `IsIso` interfaces are used.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and
  `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`: the recorded slice interface
  publicly retains `IntegralDerivedOperations`; its `integralDerivedPullback` is
  the global pullback required here, with its K-flat/Roos comparison.
- `Sheaf.Paper.IntegralScalarExtensionUniverses`: the same localization witness
  defines `integralScalarExtensionOfUniverses` and the equal-universe
  `integralScalarExtension` retained publicly. No replacement scalar functor is defined.
- `Sheaf.Paper.IntegralPullbackComparisonRealization`: `IntegralComparisonSystem`,
  `integralComparisonLambda`, `integralComparisonMu`, `integralComparisonScalar`,
  and `integralPullbackComparisonRealization`.
- `Sheaf.Paper.SpecifiedPullbackComparisonAlpha`: `specifiedPullbackComparisonAlpha`;
  its public scalar-operation module supplies `scalarPullbackCompleted` and
  `scalarCompletionIso`, with their specified completion and chain normalizations.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and its `Q`.

Proof dependencies imported privately: `EffectiveComparisonRealizationModels`,
`IntegralComparisonSequenceSystems`, and `IntegralComparisonRealizationModels`.
The two comparison statements used in both statement and proof are public imports.
`lem-trf-counit-realization-substitution` has no Lean record. The record for
`lem-pur-normalized-scalar-comparison-realization` names
`Sheaf.Paper.NormalizedScalarComparisonRealization`, but that source is absent in the
local live clone and `scompile.py --source` reports it unavailable on the server.
An initial import therefore failed for a missing object file; it was removed.
These are proof-only nodes, needed for stage 3 rather than the present signature;
their natural-language steps remain fully documented in the theorem docstring.
The maintainer can add those proof imports when their statements are published.
All statement dependencies are usable unchanged.

Edge cases checked mathematically against the signature before writing:
identity g is allowed; E=L with the identity embedding is allowed and yields the
multiplication/completeness identity normalizations; K=0 and empty schemes are not
excluded; ramified extensions and nonflat maps of finite quotient rings are included.
No bounded Tor-amplitude, perfectness, finite-type, finite-field, or nonempty-scheme
hypothesis occurs. The existing intrinsic constructible category fixes coefficient
and scheme universe u; the actual site still has object universe u+1 and morphism
universe u. No site object/morphism universe equality was added.

Searches for an existing exact statement:

- `msearch.py ... leanfinder`: "The scalar extension comparison for completed integral
  pullback along a scheme isomorphism agrees with the tensor and derived completion
  comparison". Eight hits, all scheme pullback tensor triplets/Spec pullback identities,
  including `Scheme.Pullback.tensorCongr_SpecTensorTo`; none compares these two maps.
- `msearch.py ... loogle`: `SheafOfModules.pullback, ModuleCat.extendScalars`;
  successful query, zero hits.
- `msearch.py ... grep`: `completedPullback|scalarComparison|scalarPullbackCompleted`
  in Mathlib/CategoryTheory; successful query, zero hits.
- `rg` in `lean/WeilConjectures` for `integralComparisonScalar`,
  `scalarPullbackCompleted`, and `isomorphismScalarComparisonAgreement`, and the
  requested grep for the node id: no matches.
- `rg` in `lean/Sheaf` found the two defining modules, the distinct
  `IsomorphismComparisonScalarExtension` theorem (compatibility with inverse image),
  and `PullbackIdentitiesScalarExtension` (composition/inverse compatibility, which
  cites this new equality in its proof). None states this bridge equality.

The source blueprint first paragraph was read directly at the node's recorded path.
The source agrees with the node's normalization intent. No STATEMENT-DISPUTED issue
or source-based statement correction was found. The only interface fault found is
the unavailable proof-only module recorded above.

## Second reading by NK

Single-worker re-reading of the node, both map definitions, and the final signature;
the independent maintainer review follows delivery. No separate reader is claimed.
Prime, two finite coefficient fields, embedding, scheme isomorphism, both ell-unit
conditions, and all constructible-complete K are explicit. D retains the defining
whole-tower normalization; the equality compares its actual lambda/mu composite with
the actual alpha morphism. The alpha theorem supplies only a proof of completeness,
so no hypothesis or object has been silently chosen. Equality is in the full derived
category, with both endpoints definitionally shared. The module contains only the
single named theorem with sorry, and the proof docstring follows all four DAG steps.
The only adjustment during re-reading was dropping the unavailable proof-only import;
no mathematical statement was changed.
