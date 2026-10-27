## Worker report

The module states `WeilConjectures.IntegralSystemRealization.productSystemUniformRealizationDomain`.
Its only postponed result is that named theorem, with the complete eleven-step DAG proof
and dependency IDs in its docstring. Auxiliary definitions contain real data. The
natural-language node and its dependencies are unchanged.

Clause correspondence:

- Distinct primes and the global finite field: `D : FiniteFieldDatum`, `[Fact l.Prime]`,
  `_hl : l ≠ D.p`; D records p, a, q, the finite field and its algebraic closure.
- Finite coefficient extension: E, `[Field E]`, `[Algebra ℚ_[l] E]`, and
  `[FiniteDimensional ℚ_[l] E]`. Rings, ideals, uniformizers and quotient maps use
  the recorded `Padic.coefficientExtension*` constructions. Level n means exponent n+1.
- Noetherian R, regular t, completeness and finite quotients: the first four conjuncts.
  The ring equivalence with `coefficientExtensionPositiveLimit` agrees with every
  actual quotient projection, so it describes the actual completion map.
- Three separated finite-type maps over a separated finite-type k-base: B, its three
  structure-map instances, `X : ULift.{u} (Fin 3) → Over B.left`, and `_hX`.
  Composition gives separated finite-type original source schemes over k.
- Compactifications f=aj, g=bk, h=dl: `c : ∀ i, Compactification (X i).hom`.
  Its i, g and comm give the open, proper and factorization data.
- Integral inputs K,L,M: K and `_hK`, using `finiteTorConstructibleIntegral`.
  This includes `sfIntegralConstructible`, derived completeness and a finite Tor
  interval uniform over the actual reductions. No normalization/domain assumption is added.
- Actual simultaneous operations: `o : Operations l E` records universal right-derived
  proper image and exact termwise open extension, with evaluated adjunctions.
  `inputReduction`, `systemInterpretation`, `calculus` and `Expression` are reused.
- Product geometry: `ProductVertex` includes two- and three-factor vertices, both
  parenthesizations and all product cones. Disjoint finite-set labels allow at most
  three distinct factors, each original or compactified. The empty label includes B.
- Every product vertex is `IsNoetherian`, has finite dimension bounded by d and every
  open subset compact. Every open immersion between vertices is `QuasiCompact`.
  The indicated proper arrows carry `IsProper` in compactification data and
  `Expression.push`; base changes and composites have the existing properness instances.
  `Expression.geometric` is a conclusion, not an extra geometric assumption.
- Finite well-typed diagram expressions: `es : List (Σ W, Expression ... W)` and
  `inProductDiagram`. Singleton lists give individual expressions. The conclusion
  `e.2.domain l E o K` is the published realization domain for every expression.
- Quantitative intervals: arbitrary a,b with the displayed input Tor conditions;
  `torBounds` preserves endpoints for pull/open, adds them for tensor, and adds
  `2*d(source)` to the upper endpoint for proper image. Compact support uses its
  compactifying ambient source, and the hidden open intermediate keeps the input interval.
- Every intermediate: `boundedSystems` lists the root and all subtrees, including
  separately the open intermediate of compact support. Every member satisfies Good,
  its computed `DomainInterval`, and a common `DomainInterval lower upper` independent of n.
- Open extension preserves any separately supplied cohomological interval by the
  explicit `OpenIntervalPreservation` conjunct.
- Normalization: `IsNormalizedCoefficientSequence` in Good uses the actual quotient
  transitions, not unrelated endpoint isomorphisms.
- Constructibility and bounded witnesses: `DomainInterval` asserts intrinsic
  constructibility, cohomological support and Tor amplitude at every level, and a
  bounded constructible ordinary-etale witness in the same interval with its actual
  intrinsic comparison isomorphism. These separate witnesses need no transitions.
- Coherent origins: Good includes `Nonempty (Origins ...)`, the published fixed
  origins with evaluations and commuting transition squares.
- System comparison: `DomainSiteComparison` uses `CoefficientSystemDerivedImage`
  for `Scheme.proEtaleSiteComparison`. Its descends predicate asserts the actual
  `image.system.adjunction.counit` is invertible on the same expression system,
  with bounded-below input and bounded-below normalized direct image.
  `DomainSystemPresentation` fixes quotients on generators, uses the induced
  restriction of scalars at every level, requires identity underlying additive maps
  for level comparisons and heterogeneous equality with the actual sequence's
  underlying additive transition maps, and fixes derived transport by Q.
  These presentation data are conclusions, not added hypotheses or arbitrary maps.
- Empty sources: `∀ Z, IsEmpty Z → d Z = 0` makes the proper contribution zero.

Dependency declarations used (module, declaration):

- def-weil-finite-field-fiber: `Sheaf.Paper.FiniteFieldFiber`, `WeilConjectures.FiniteFieldDatum`.
- def-weil-l-adic-coefficient-extension: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`.
- def-weil-compactifications-refinements: `WeilConjectures.Compactification.RefinementCategory`, `AlgebraicGeometry.Compactification.Refinement`.
- def-weil-finite-tor-amplitude: `Sheaf.Paper.FiniteTorAmplitudeSites`, `WeilConjectures.finiteTorConstructibleEtale`.
- def-weil-derived-complete-integral-detailed: `Sheaf.Paper.SfIntegralConstructible`, `WeilConjectures.sfIntegralConstructible`.
- lem-coef-semilinear-derived-sections: `Sheaf.Paper.SemilinearDerivedSections`, `WeilConjectures.SemilinearSections.semilinearDerivedSections`.
- def-sf-integral-system-expression-domain: `Sheaf.SixFunctors.IntegralSystemExpressionDomain`, `WeilConjectures.IntegralSystemRealization.Expression.domain`.
- lem-pur-coefficient-system-derived-comparison: `Sheaf.Paper.CoefficientSystemDerivedComparison`, `SheafOfModules.coefficientSystemDerivedComparison`.
- lem-sf-integral-compactification-system-realization: `Sheaf.SixFunctors.IntegralCompactificationSystemRealization`, `WeilConjectures.IntegralSystemRealization.integralCompactificationSystemRealization`.

Statement dependencies are publicly imported, directly or through published public
imports. Remaining proof dependencies are plain imports of their recorded modules;
the proof plan names all their IDs and uses their finite-level closure and scalar
comparison interfaces. The CompactObject example has been withdrawn and has no
current declarations; its node record was read. Published module mode is followed.
Auxiliary presentations and diagram predicates belong to this obligation's module,
are listed in lean.declarations, and have source/blueprint docstrings.

Searches:

- msearch leanfinder: "Uniform bounds and normalization for finite expressions in
  derived coefficient systems, pullback tensor extension by zero and proper direct image".
  Eight unrelated polynomial-law/Chevalley/tensor algebra hits; no exact theorem.
- msearch loogle: "IsAdicComplete, IsNoetherianRing". One adic-completion local-ring
  instance; no expression or system-domain theorem.
- msearch leansearch: "Derived coefficient systems normalization uniform Tor amplitude
  proper direct image". Eight unrelated normalization/group-Tor results; no match.
- msearch grep: "IsNormalizedCoefficient|TorAmplitude" in Algebra/Homology: zero hits.
- rg in Sheaf, WeilConjectures and Mathlib derived-category sources for the item ID,
  uniform_realization, uniformRealization, productSystemUniform, and expression/system
  names. Existing IntegralSystemExpressionDomain and IntegralCompactificationSystemRealization
  state a domain and conditional realization, not uniform membership for actual products.
- blueprint_refs search "product compactification": no blueprint-node match.
  FiniteProductCompactification and OpenExternalTensorNormalization were read;
  neither states this uniform domain assertion. The system comparison's strict-family
  category and expression's ringed sequence-site category are different presentations;
  the bridge preserves the actual transitions rather than assuming a domain.

Sources read: current blueprint's Kunneth-coherence proper-reduction proof and local
Stacks sites-cohomology Tag 0941, with the recorded dependency interfaces and docstrings.
No statement fault or STATEMENT-DISPUTED issue was found.

Edge cases: all levels are n+1, including exponent one; equal-index normalization
is inherited from the published definition. Zero inputs, empty schemes and empty
products are allowed; d=0 for empty sources. Two-factor expressions may omit the
third label. An empty collection has arbitrary ordered common bounds; singleton
collections include the root. Identity opens and maps remain in the syntax. Tensor
repetition and arbitrary finite syntax sizes are allowed; the geometric products
have at most three distinct labels. Small-site objects remain in u+1, morphisms in u,
modules in u+1 and derived categories in u+2. No extra universe equality is imposed.

## Second reading by Q133

This was a separate in-thread rereading of the node and module; the dispatch brief
prohibits other agents, so the maintainer provides independent review. Domain is a
conclusion, compact support's hidden open is included, proper bounds use source
dimension, and comparison uses the actual adjunction counit. Three labels use
ULift (Fin 3) to match the existing expression universe. The presentation bridge
uses heterogeneous equality of underlying additive transition maps and identity
level comparisons, avoiding repeated scalar-restriction elaboration. An explicit
open cohomological-interval clause retains that separate assertion, and etale
witnesses are explicitly bounded constructible.

Compilation: scompile.py compiled the sandbox and named library module without
errors or warnings. The dry run's repeated compile also passed; its subsequent
bookkeeping found that the sandbox had disappeared externally. This packet was
restored from the captured source and unchanged original node; preflight and the
compile are repeated on the restored packet before delivery.
