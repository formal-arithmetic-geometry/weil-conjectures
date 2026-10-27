## Worker report

Stated `WeilConjectures.IntegralSystemRealization.projectionIntegralCoherenceRealization`
in `Sheaf.SixFunctors.ProjectionIntegralCoherenceRealization`. There are two theorem clauses with proof `sorry`. Six typed helpers in this same module
name the specified identity, composition and refinement maps and their concrete
coherence routes. They contain real data, and are recorded in `lean.declarations`.
Only the item's `lean` field changes.
The source is the current main-20261015 projection-formula proof, its reference to
projection coherence, and the item's five-step realization assembly. The proof plan
is carried in the declaration docstring.

The statement uses the dependency's typed expression calculus, rather than a second
operation or coefficient-system definition. Its two inputs are indexed by an arbitrary
`I : Type u` with `[Finite I]` and `Nat.card I = 2`; the distinguished input `iL` is L,
and the other input is K. This is a universe-correct presentation of the ordered pair
(K,L): one can label either index as L. It does not quantify over extra input objects.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Fixed finite-field datum and algebraic closure | `D : FiniteFieldDatum.{u}`; the base is `Spec (CommRingCat.of D.k)` |
| Prime l different from p | `l : ℕ`, `[Fact l.Prime]`, `_hl : l ≠ D.p` |
| Finite extension E of Q_l, R its integers, t its chosen uniformizer | `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]`; the resolution uses the recorded `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, `coefficientExtensionIdeal` |
| Positive coefficient levels A_n | `n : ℕ`, `_hn : 1 ≤ n`; `Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)` has codomain the recorded `coefficientExtensionRing l E n` |
| Operation datum with no projection-invertibility assumption | `o : Operations l E`, `ρ : Realizations l E D o`, the simultaneous operations and specified comparisons supplied by the realization dependency; no `IsIso` premise on projection maps |
| Schemes finite type over k, not necessarily separated over k | Expression indices are `Over (Spec (CommRingCat.of D.k))`; `ge : e.geometric`, `gt : t.geometric` impose finite type on all intermediate schemes without `IsSeparated` on structure morphisms |
| Separated finite-type f and g | Every pull/compact-support arrow, including f, g and their composites, is retained in the expressions; `Expression.geometric` imposes `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` on these arrows. The theorem quantifies over the source and target expressions of the displayed maps rather than binding f and g a second time independently of their expressions |
| K in D^b_c(X,R), L in D^b_ctf(Z,R) | `K : (e.domain l E o).FullSubcategory` includes `sfIntegralConstructible` for both inputs; `_hL : finiteTorConstructibleIntegral l E (X iL).left (K.obj iL)` imposes precisely the stated L domain |
| Small pro-etale strict semilinear systems, reduction R and total limit L | Imported `System`, `inputReduction`, `coefficientSequenceLimit`; all refer to the actual sequence-site and completed coefficient categories, not towers of unrelated derived arrows |
| Every intermediate system normalized, compatible etale origins, common cohomological and Tor bounds | `e.domain` and `ht : t.domain l E o K.obj` use `Expression.admissible` recursively, including the intermediate open-extension object inside each compact-support symbol; the `Good` predicate contains normalization, `LevelBounds` and retained `Origins`. `CanonicalPair.comp` also records geometric/admissible intermediate expressions in paths |
| Canonical simultaneous realization c_V | `ρ.comparison e ge` and `ρ.comparison t gt`, evaluated on the same family `K.obj`; the target domain witness only packages that same family |
| Every actual generating map m | `CanonicalPair ... e t s₁ r₁`, indexed by the actual system and integral arrows. `BasicPair` fixes units, counits, open and proper/open maps, and `compactProjection`; there is no constructor for an arbitrary arrow pair |
| c_T L(m) = m_int c_S | First conclusion is `(coefficientSequenceLimit ...).map s₁ ≫ c_T.hom = c_S.hom ≫ r₁` (Lean composition reads left to right) |
| Realized routes after conjugation | The route conclusion directly equates the two composites `c_S.inv ≫ L.map sᵢ ≫ c_T.hom` |
| Inverse factors when defined, including refinement inverses | The refinement route uses the inverse of the actual Γ on its two specified inputs, and structural inverse generators remain in `CanonicalPair`. The redundant general inversion-conjugation conclusion has been removed |
| Concrete coherence equations at integral coefficients | `ProjectionCoherenceRoutes` fixes both routes by explicit formulas, with no system-equality premise. The conclusion equates their conjugates `c_S.inv ≫ L.map s₁ ≫ c_T.hom` and `c_S.inv ≫ L.map s₂ ≫ c_T.hom`, and then asserts `r₁ = r₂` for the two specified `CanonicalPair` realizations |
| Projection composition for X → Y → Z | `ProjectionCoherenceRoutes.composition` fixes `PF_g ≫ g_!(PF_f) ≫ α_tensor ≫ (gf)_!(tensor pullComp.inv)` and `tensor(α_K, id) ≫ PF_gf`; `projectionSystemCompositor` expands α as proper image of Γ followed by `pushComp` and `openComp` |
| Proper/open Γ_Q projection square | `.properOpen` fixes `δ_i ≫ i_!(π_r) ≫ i_!r_*(tensor square.hom) ≫ Γ_tensor` and `tensor(Γ_M,id) ≫ π_p ≫ p_*(δ_k)`, with the exact normalized non-Cartesian Γ |
| Compact exchange compatibility | `.compactExchange` fixes the pullback of `compactProjection` followed by `compactExchange` and tensor/pullback comparisons, and the tensor comparison followed by exchange on M and `compactProjection` for the pulled-back compactification |
| Refinement projection equation | `.refinement` fixes `PF_c₁ ≫ θ_tensor` and `tensor(θ_M,id) ≫ PF_c₂`; `projectionSystemRefinement` is `pushComp.inv`, followed by proper image of `Γ.inv` and the normalized direct-image identity. It uses the actual `Compactification.Refinement`, without a Cartesian restriction |
| Identity equation | `.identity` fixes `compactProjection` for the actual identity compactification and the route using `projectionSystemSupportIdentity` and `projectionSystemPullIdentity`; these are built from the canonical bridge and the sectionwise `sId`, `jId`, `pId` |
| Pasting and nested associativity | `.vertical` and `.horizontal` display both Γ pasting equations with the direct-image/open compositors. `.threeCell` displays the two three-factor routes of lem-sf-three-cell-compositor. `.comp`, `.pull`, `.push`, `.shriek`, `.compactSupport`, `.tensor`, `.symm` and `.trans` retain their contextual composites, including the two routes of the nested compact-support associativity pentagon. Each is asserted equal after realization, rather than assumed equal |
| Canonical direct-image/limit comparison | Inherited from `ρ.realizationModel.push`, the right-adjoint conjugate of the canonical reduction/pullback comparison. `RealizationModel.ordinary.projections` fixes the ordinary comparison sectionwise by the actual limit projections, and `RealizationModel.model` fixes the derived comparison on K-flat resolutions. The theorem uses those existing `ρ.comparison`s, not newly chosen isomorphisms |
| Quotients have two-term finite-free resolutions | Second outer conjunct gives injectivity of multiplication by the actual `t^n`, `Function.Exact` of that multiplication and the actual quotient map, and surjectivity of the quotient map. This is `0 → R → R → A_n → 0`; the two nonzero resolving terms are R itself, free of rank one, in degrees -1 and 0 |
| No faithfulness of finite evaluation | No faithful-evaluation hypothesis, or implication from equality of evaluated arrows, occurs. Equalities are transported by `coefficientSequenceLimit.map` and endpoint conjugation |

Dependency declarations read and reused:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` (with its field,
  algebraic closure and coefficient conventions).
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, publicly exposing the underlying recorded
  coefficient ring, ideal, uniformizer and transition constructions from
  `Sheaf.NumberTheory.Padics.CoefficientExtension`.
- `Sheaf.Paper.SixFunctorOperationDatum`:
  `WeilConjectures.SixFunctorOperationDatum`; the theorem uses its operation-only
  simultaneous-system realization `Operations` and `Realizations`, as required by
  the item's realization dependency. No projection-invertible six-functor package is used.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`,
  `compactificationProjectionFromData`, and its counit-defined mate. The reused
  `BasicPair.compactProjection` indexes exactly this composite and its completed
  counterpart via `compactificationProjection` and `ringedCompactificationProjection`.
- `Sheaf.Paper.QcqsCompactSupportRealization`:
  `WeilConjectures.sfQcqsCompactSupportRealization`, the canonical comparison with the
  recorded integral compact-support functor, used by the realization dependency.
- `Sheaf.Paper.SfIntegralConstructible`:
  `WeilConjectures.sfIntegralConstructible`, as used inside `Expression.domain`.
- `Sheaf.Paper.FiniteTorAmplitudeSites` and its imported `FiniteTorAmplitude`:
  `finiteTorConstructibleEtale`, `finiteTorConstructibleIntegral`; the integral clause
  uses the latter, rather than substituting an etale or finite-level category.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `coefficientDerivedSystemEvaluationCalculus`, `CoefficientDerivedSystemCalculus`,
  with the recorded reduction/limit adjunction and simultaneous tensor calculus.
- `Sheaf.SixFunctors.IntegralCompactificationSystemRealization`:
  `integralCompactificationSystemRealization`, `Realizations`, `CanonicalPair`,
  `BasicPair`, `CanonicalIsoPair`, the actual projection maps, and the publicly imported
  expression-domain and canonical-bridge interfaces. These are the central interfaces.

Stated proof dependencies are imported without `public`:
`Sheaf.SixFunctors.ProperOpenProjectionMate` (in particular its system theorem
`properOpenProjectionMateSystems`), `Sheaf.SixFunctors.AmbientProperOpenPasting`
(`ambientProperOpenPasting`), and
`Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison`
(`CategoryTheory.ringedTowerPushforwardLimitComparison`). The remaining proof nodes
`lem-sf-projection-compatible-triangle-assembly`, `lem-sf-projection-refinement-descent`
and `lem-sf-three-cell-compositor` have no recorded modules in the read DAG;
their eventual imports are left to the maintainer's proof-import bookkeeping. They
are not missing statement notions: the actual maps, contexts and equality-transport
statement use the already recorded realization calculus.

Edge cases checked before delivery:

- Identity/length-zero paths use `CanonicalPair.identity`; conjugation yields identity.
- Structural inverses and inverse refinement factors have the correctly reversed endpoints;
  the theorem concludes their integral invertibility from system invertibility.
- Nested compact-support expressions are genuine expression constructors, not flattened
  replacement functors; finite paths require all intermediate admissibility data.
- Empty schemes, empty opens, and zero input objects are not excluded. The index set is
  a presentation of two input slots, not the underlying points of a scheme; those slots
  may contain zero objects on empty schemes.
- Nonseparated finite-type schemes are allowed: structure maps have no separatedness premise.
- Level n=1 is present, and no level n=0 is required. The resolution differential is the
  chosen actual uniformizer raised to n, not a merely assumed regular element.
- The input index universe agrees with the scheme universe. Abstract two-element indexing
  avoids elaboration problems from a fixed small index universe; no site universes change.
- Every declaration binder and universe is explicit (`autoImplicit false`).

Searches for an existing statement (2026-10-22; wrapper results in searches.jsonl):

- LeanFinder: "Integral realization of semilinear systems intertwines canonical projection
  formula maps and transports equality of composite paths". Eight results concern module
  presentations, ordinary adic completion and direct limits; no specified derived-system
  projection coherence realization.
- Loogle: `"DerivedCategory", "limit"`: zero hits.
- Mathlib grep through msearch: `realization.*projection|projection.*coherence`: zero hits.
- LeanSearch: "Derived inverse limit realizes strict semilinear coefficient system projection
  formula maps and preserves their coherence equations". Eight results concern ordinary
  inverse/direct limits and generic limit-projection lemmas; no exact statement.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for integral/coherence/realization patterns,
  plus the node id, found the known realization interfaces and compactification bridge,
  not the concrete integral route equalities added in this repair. Exact declaration-name search (including the upstream name index)
  found no clash. The dependency's `Realizations.coherence` gives the primitive square;
  it does not assert the projection-composition, Γ projection, refinement and identity
  equations stated by the repaired theorem. The earlier report incorrectly claimed
  that a conditional equality-transport assertion supplied those equations.

No statement correction, disputed statement, new node or dependency repair was needed.
The repaired module is validated through the prescribed scompile.py and deliver2.py
checks. The repaired packet passed deliver2.py --no-push (preflight and per-file
compilation), producing dry-run commit eabdaf5bfd7. No errors or unexpected warnings
remain. The postponed proofs are `projectionIntegralCoherenceRealization` and
`projectionIntegralAssociativityPentagon`, both clauses of this DAG node.


## Repair of returned head 9a5c4f9dc5ad

H3/H5: removed the implication whose premises were two commuting realization squares
and an equality `s₁ = s₂`. Replaced it with concrete equation families. The new
`ProjectionCoherenceRoutes` is a syntactic index of specified pairs of routes: its
constructors contain formulas in `compactificationProjection`,
`compactificationExchange`, `properOpen.gamma`, `pullComp`, `pushComp`, `openComp`
and their functor contexts. It has no constructor accepting equality of system maps.
The theorem asserts equality of the realized routes themselves and of their
`CanonicalPair` integral maps. Thus these are no longer consequences merely of the
`ρ.coherence` assumption. The primitive intertwining and resolution clauses remain; the redundant general
conjugation and inversion conclusions have been removed.

The helper definitions belong to this node's construction of its route expressions;
they introduce no second operation datum, coefficient category, projection map,
proper/open map or realization isomorphism. The refinement helper takes inverse
witnesses only for the specific Γ factors it inverts, and does not assert their
invertibility for arbitrary inputs. The domain and finite-Tor hypotheses of the
original theorem are retained.

Additional searches run during repair: msearch Mathlib grep
`ProjectionCoherenceRoutes|projectionSystemCompositor|projectionSystemRefinement`
returned zero hits; `rg` with these names and `projectionIntegralCoherenceRealization`
in WeilConjectures, Sheaf and the upstream-name index found no existing declaration.
The exact system source equations were read in the four DAG nodes
lem-sf-projection-compatible-triangle-assembly, lem-sf-proper-open-projection-mate,
lem-sf-projection-refinement-descent, lem-sf-three-cell-compositor and the
ProperOpenCoherence vertical/horizontal fields. The source proof of the blueprint
unit points to prop-sf-pf-coherence for precisely these composition/refinement/exchange
identities. No DAG statement correction is required.

Further edge cases: the identity compactification has both arrows equal to the
identity; the explicit identity route has source `F_id M ⊗ N` and target
`F_id (M ⊗ P_id N)`. Refinements need not be Cartesian. Raw binary and three-cell
comparisons are never inverted. Their contextual equations continue to cover empty
schemes and zero objects. Uniformizer resolutions retain n ≥ 1.


The second declaration `projectionIntegralAssociativityPentagon` explicitly states
`r01 ≫ r12 ≫ r24 = r03 ≫ r34` for the five `CanonicalPair` integral edges through
five parenthesized expressions. Its route-index witness names the concrete contextual
three-cell/pasting routes, and contains no equality of system arrows. Every vertex
has its geometric and admissible witness; the same two inputs and finite-Tor input L
are retained. This states the pentagon as an integral composite equality, with no
additional invertibility of any raw edge.

Compilation diagnosis: unrestricted backward definitional equality spent the file
budget unfolding coefficient-system categories. Restoring respect for transparency
throughout, with the existing permissive setting scoped only to the raw binary
compositor definition, resolved that cost. Generated size/injectivity declarations
are disabled as in the upstream expression calculus. The 60-second limit is unchanged.

Final self-check: the primary `lean.statement` is verbatim, all eight public
declarations are recorded, both proof bodies are `sorry`, all Lean lines have at most
100 characters, and only `lean` differs from the current shared node. No equality of
system maps is an assumption of either theorem.

## Second reading by N6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
