## Worker report

The module `Sheaf.Paper.FixProjectionCompactificationComparison` states
`WeilConjectures.FixProjectionCompactification.comparison`. Its only postponed theorem
is `comparison`; its proof is `sorry`. The three auxiliary definitions contain actual
data or explicit propositions, with no postponed data or additional theorem. The node's
statement is unchanged. No new node or dependency replacement is needed.

Hypotheses and clauses:

- The global finite field and coefficient conventions are `D : FiniteFieldDatum`,
  `C : D.CoefficientDatum`, `E`, its field/algebra/finite-dimensional instances,
  `n`, and `hn : 1 ≤ n`. `hl : IsUnit (C.l : D.k)` expresses the invertibility
  of ell. `S : SixFunctorOperationDatum D C E n hn` is the recorded construction datum,
  not an arbitrary family of maps or an extra projection-coherence hypothesis.
- Finite-type k-schemes are explicit scheme binders with `Over`,
  `LocallyOfFiniteType`, and `QuasiCompact` structure maps in `finiteLaw`.
  In `higherLaw` they are the existing `SixFunctorSpace D` objects; those are precisely
  the full subcategory of finite-type objects of `Over (Spec k)`. There is no
  separatedness assumption on either structure morphism. The morphism is over k,
  separated, locally of finite type and quasi-compact, exactly separated finite type.
- The two compactifications are `c₁ c₂ : Compactification f` (or `f.hom.left`).
  This existing structure retains the open immersion, proper map, and factorization.
  `identitySquare f c` merely packages these same factors with identity base change
  to evaluate the already recorded higher projection family. It constructs the
  compactifying scheme with structure map `c.g ≫ Y.obj.hom`, not a new geometric choice.
- The finite compact-support functor is the dependency's
  `rightDerivedLowerShriekOfCompactification`. In the higher clauses it is the
  `support` functor of the actual normalized stage of S. These functors retain the
  proper/open construction identifications from the datum.
- At finite coefficients, `O : RefinementFiniteLevelOrigin ... X` retains the
  antecedent and comparison isomorphism. `K` is the canonical fixed-module
  realization of that very witnessed input, not a chosen unrelated antecedent.
  Bounded constructibility is `intrinsicFiniteTorsionConstructible` after the
  canonical `sfIntrinsicDerivedEquivalence`; only L has `finiteTorConstructible`.
  In particular there is no finite-Tor assumption on K.
- `OT` and `e` retain any origin witness and identification for the actual tensor
  object T. They express the stated domain of the comparison at T, rather than
  a restriction to a preferred tensor representative. The proof first obtains this
  domain using the cited pullback, tensor and constructible-origin lemmas.
- Finite rho is explicitly `(theta r₁).symm ≪≫ theta r₂` for every common refinement
  d and its two arrows, evaluated using `refinementComparisonIsomorphism` at O or OT.
  At T the actual support image of e conjugates the witnessed map to the displayed
  tensor object. This is precisely the normalization in `compactification_coherence`;
  independence identifies it with the node's rho for arbitrary c₁,c₂. All refinements
  allowed by the recorded definition are included; no Cartesian hypothesis is added.
- The finite PF maps are the upstream
  `ProEtale.projectionMapOfCompactification`, proper counit projection followed by
  proper image of the open tensor comparison and pullback compositor. In the higher
  clauses `SixFunctorExchangeData.projectionComponent` transports exactly
  `ExchangeProjectionStage.projection` to the named operation coordinates. The datum
  normalizes its proper/open adjunctions, tensor maps, factorization and support
  identification; no arbitrary PF or rho is supplied as a hypothesis.
- The equation is written in Lean's composition order: `PF₁ ≫ rhoT.hom =
  tensor.map(rhoK.hom) ≫ PF₂`. `tensor.map(...).app L` is rho(K) tensor identity on L.
  No `IsIso` condition is asserted or used for either PF.
- The integral conjunct specializes `higherLaw` to `S.higher.integral`, its
  `integralTensor` and `integralExchange`, with exactly
  `finiteTorConstructibleIntegral` on L. K belongs to the whole bounded constructible
  integral category. The supplied integral operations are completed, and the datum's
  normalization retains the finite reduction and strict proper/open constructions.
- The rational conjunct specializes to the named rational stage, tensor and exchange.
  The common-stage conjunct specializes to the named algebraically closed stage,
  tensor and exchange. Their L domain is the entire bounded constructible category,
  exactly the field-stage definition of finite Tor amplitude. The generic predicate
  argument is instantiated with the full-domain predicate in these two cases.
  No extra lattice, retract, finite-Tor requirement on K, or choice of finite coefficient
  field is imposed. The datum records rationalization and the actual finite-stage
  inclusions, their identity and composition normalizations and the operation-map
  comparison squares; arbitrary common-stage morphisms and denominators remain included.

Dependency declarations read and used:

- `Sheaf.Paper.SixFunctorOperationDatum`: `SixFunctorOperationDatum`, together with
  its public `SixFunctorPushStage`, `SixFunctorHigherOperations`, `SixFunctorCommonStages`,
  `SixFunctorExchangeData.projectionComponent` and their normalization fields from
  `Sheaf.Paper.SixFunctorOperationDatumStages`.
- `WeilConjectures.Compactification.Refinement` and its public framework:
  `Compactification`, `Compactification.Refinement`; the definition is the proper
  morphism fixing the open, with no Cartesian-square condition.
- `Sheaf.Paper.CompactificationCoherence`: `compactificationOriginCandidate`,
  `compactification_coherence`, specifically its common-refinement normalization.
- `Sheaf.Paper.RefinementComparisonIsomorphism`: `RefinementFiniteLevelOrigin`,
  `refinementFiniteLevelFixedObject`, `refinementComparisonIsomorphism`.
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`: `Scheme.FixedEtaleOriginWitness`.
  The finite comparison uses its dependency's already recorded retained witness
  category, which transports the same pair through the coefficient equivalence.
  An additional independent fixed witness is neither necessary nor assumed.
- `Sheaf.Paper.ExchangeFunctoriality`: `exchangeFunctoriality`, especially the
  completed/transported compactification comparison domain conventions of clause (4).
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`: `ExchangeProjectionStage.projection`,
  `compactificationProjectionFromData`, and the coefficient adjunction/comparison/cocycle
  structures used by the operation datum.
- `Sheaf.Paper.FiniteTorAmplitude`: `finiteTorConstructible`,
  `finiteTorConstructibleIntegral`, `finiteTorFieldCoefficientCategory`. The current
  record's `finiteTorConstructibleEtale` in `FiniteTorAmplitudeSites` is the ordinary
  etale presentation; it is also imported. The same owning node's public intrinsic
  pro-etale and integral interfaces are used here because those are the present
  node's categories. No dependency record is overwritten just to change presentations.
- `def-weil-scheme-morphism-properties` is a convention node: the indicated Mathlib
  `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`, `IsOpenImmersion`, `IsProper`
  are used directly.

The module imports every recorded project proof-dependency module (including the
proper/open tensor, system realization, normalization and boundedness lemmas); the two
Mathlib geometry leaves have no project module record. Proof-only imports are nonpublic.

Edge cases checked: n=1 is included and n=0 is excluded exactly by the node; identity
refinement, equal compactifications and identity morphism are included; d and both
refinement arrows are arbitrary; noncartesian refinements are included; empty schemes
and zero complexes are not excluded; K need not have finite Tor at finite coefficients;
only L has the additional finite-Tor condition there and integrally. Common-stage
identity fields and arbitrary enlargements remain in the supplied stage category.
Site coefficient and scheme universes retain the recorded `u+1` and `u` conventions.
All universes and variables are explicit (`autoImplicit` and `relaxedAutoImplicit` false).

Searches before writing:

- `msearch.py leanfinder`: "The derived projection transformation for compactly
  supported direct image agrees for two compactifications under the refinement
  comparison" returned 8 unrelated uniform-space/Stone-Cech/compactly-supported-map
  declarations, including `AbstractCompletion.compare_comp_eq_compare`; no match.
- `msearch.py loogle`: `CategoryTheory.Adjunction.rightAdjointProjectionMap` returned
  no hits (unknown identifier in the remote Mathlib index). The project's declaration
  exists and was read in its upstream `ProjectionMap` module; it supplies the PF
  construction, not this comparison theorem.
- `msearch.py grep`: `projectionMapOfCompactification_comparison|compactificationProjectionFromData|projection.*refinement`
  in `CategoryTheory` returned no hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for projection/compactification
  comparison found the ordinary-etale theorem
  `Etale.projectionMapOfCompactification_rightDerivedLowerShriekOfCompactificationIso`
  in upstream `LowerShriekProjectionExchange`. Its complete signature was read: it
  covers ordinary finite etale coefficients only, not the witnessed pro-etale,
  completed, rational and common-stage clauses. It cannot attach this whole node.
  `ProjectionComparisonEtaleOrigin` instead compares two sites for one compactification;
  it does not compare c₁ with c₂. `ShriekTensorComposition` is also ordinary finite etale.
- The search for this item id in `lean/WeilConjectures` returned no hit.

No statement dispute or statement correction. Compilation and delivery checks are
recorded below after they complete.

Validation: `scompile.py` compiled both sandbox and named module cleanly (31.7 s and
16.1 s on the successful full-import check). The delivery dry run compiled the module
again and printed `OK (dry run): commit 940ec5d8bb passes the preflight and compiles;
nothing pushed`. An earlier attempt timed out rebuilding the recorded
`ExchangeFunctoriality` dependency; retrying unchanged against the current server
succeeded. All compilation used the prescribed wrapper and default 60-second limit.

## Second reading by NJ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
