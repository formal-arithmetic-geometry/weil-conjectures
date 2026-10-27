## Worker report

The module `Sheaf.Paper.ProetaleSupportedModelCoinduction` states
`AlgebraicGeometry.ProEtale.proetale_supported_model_coinduction`, with proof `sorry`.
No definitions or auxiliary theorems are introduced. The node's statement and six-step
proof plan are unchanged. The existing definition node `def-sfb-supported-model-hull`
is added to `stmt_deps`, since it owns the exact hull and support-chain constructions
already spelled out in the statement. No new nodes or dependency repairs are needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The fixed p-adic algebraic closure is the
  existing `PadicAlgCl ℓ`; `PadicAlgCl.FiniteIntermediateField ℓ` specifies finite
  subextensions inside that closure. The finite ring and subextension serve only to
  specify an allowed coefficient, so the five-way `hΛ` encodes them existentially,
  just as in the recorded parent `supportedModelHull_proetale_descent` interface.
- `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}`, with `[MonObj Λ]` and
  `[IsCommMonObj Λ]`, is the commutative condensed ring. The first disjunct of `hΛ`
  specifies a discrete finite commutative topological ring A killed by a power of ℓ:
  `Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0)`. The other disjuncts are precisely
  `continuousMapRingObj ℤ_[ℓ]`, `padicIntegersRingObj ℓ E`,
  `continuousMapRingObj ℚ_[ℓ]`, and `continuousMapRingObj E`. Their standard topologies
  are the induced p-adic topologies; all continuous maps on profinite sets are used.
  Each `Nonempty (Mon.mk Λ ≅ Mon.mk ...)` retains both addition and multiplication.
  Finite A may be represented in `Type 0` without losing any finite ring isomorphism
  class. Neither algebraic-closure coefficient is admitted by the five-way hypothesis.
  The broader `IsLocalizingAdmissibleCoefficient` includes a sixth coefficient, so
  using it alone here would be incorrect; its existing ring constructions are used.
- Schemes are `U V : Scheme.{u}`, with `CompactSpace` and `QuasiSeparatedSpace` on
  both. This is exactly qcqs, with no Noetherian or finite-type assumption.
- `(b : U ⟶ V) [WeaklyEtale b]` represents an object `Scheme.ProEt.mk b` of the small
  pro-etale site. `[QuasiCompact b] [QuasiSeparated b]` gives the two additional
  morphism hypotheses. There is no surjectivity, affineness, weak contractibility,
  properness, or cohomological-dimension condition.
- The site is `Scheme.ProEt.topology`; its object and morphism universes are the
  established `u + 1` and `u`, with abelian values in `u + 1`. The hull's product and
  strict filtered-colimit index types are `Type (u + 1)`. The existing derived-category
  instances are used; no artificial equality between site universes is imposed.
- `condensedRingObj Λ W` is the actual pulled-back coefficient Λ_W. `L` is an
  internal module over it in `Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) ...`.
  The ambient `DerivedCategory` in the hull and derived pushforward is the ordinary
  uncompleted localization at quasi-isomorphisms. The imported `condensedModuleSections`
  gives the stated actual abelian-group-valued module sections convention; the result
  asserts membership of the derived object itself, so has no sections term in its type.
- `(p : ScalarModelSupportChain U W)` ranges over every finite support chain.
  `nil` is the empty chain. `openStep` requires an open immersion and quasi-compactness;
  `closedStep` requires a closed immersion and compactness of the complementary open.
  There is no extra condition on W; its qcqs property follows along such a chain.
- `(p.extension Λ).obj L` uses exactly the ordinary open lower shriek and closed lower
  star in their order along the chain; its empty-chain branch is the identity functor.
- `hL : HasFiniteConstantLocalModel Λ W L` is the recorded internal-module local-model
  declaration retained in `sk-def-sfb-constructible`'s `lean.declarations` and publicly
  imported by its recorded module `SectionwiseFiniteConstantLocalModel`. It quantifies
  over a pro-etale cover and finitely presented modules on the condensed point, pulled
  to each cover member. A finite presentation on the point is a finite scalar matrix,
  hence gives Λ_W tensor the discrete constant finitely presented scalar module.
  The scalar module may vary with the cover member. The primary sectionwise companion
  `HasFiniteScalarConstantLocalModel` is for a different module encoding and is not
  substituted for the already provided internal-module predicate.
- `supportedModelHull Λ V` is exactly G_V. `IsSupportedModelHullClass` requires
  `P.IsTriangulated` (zero, all integer shifts, distinguished-triangle extensions),
  `P.IsClosedUnderIsomorphisms`, the retract relation `i ≫ p = 𝟙 K`, all small derived
  products by limiting cones, all strict small filtered diagrams of complexes with a
  common termwise lower bound by colimiting cocones, and all supported local models
  in degree zero. `supportedModelHull` intersects these classes by universal
  quantification. Products use the ambient derived category. Complex colimits are
  termwise module-sheaf colimits, and `DerivedCategory.Q` is the localization.
- `(DerivedCategory.singleFunctor _ 0).obj ((p.extension Λ).obj L)` is `(JL)[0]`.
  Applying `(CondensedRing.moduleObjectDerivedPushforward Λ b).obj` gives the actual
  total right derived functor of the coefficient-compatible module direct image,
  defined as `(CondensedRing.lowerStar Λ b).rightDerivedFunctor`. The conclusion is
  membership of this exact object in the exact target hull, for the explicit supported
  generators only. No completion or solidification occurs.

Dependency declarations read and used:

- `Sheaf.Paper.SupportedModelHull`: `ScalarModelSupportChain`,
  `ScalarModelSupportChain.extension`, `IsSupportedModelHullClass`, `supportedModelHull`.
- `Sheaf.Paper.SectionwiseFiniteConstantLocalModel`, publicly importing
  `Sheaf.Paper.FiniteConstantRingedLocalModel` and the original
  `Sheaf.Paper.CondensedConstantConstructibility`: `HasFiniteConstantLocalModel`.
  Both the sectionwise companion and original internal predicate signatures were read.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `CondensedRing.moduleObjectDerivedPushforward`; the body derives the full actual
  `CondensedRing.lowerStar` from
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`.
- `Sheaf.Paper.CondensedQcqsPushforwardContinuity`: `condensedModuleSections`.
- `Sheaf.Paper.LocalizingAdmissibleCoefficients`: coefficient construction conventions;
  its broader admissibility predicate was checked and deliberately not used as hΛ.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`:
  `CondensedRing.openImmersionLowerShriek`, used by the actual chain extension.
- Mathlib: `Scheme`, `Scheme.Hom`, `IsOpenImmersion`, `IsClosedImmersion`,
  `QuasiCompact`, `QuasiSeparated`, `WeaklyEtale`, `Scheme.ProEt`, `Scheme.ProEt.topology`,
  `Scheme.smallEtaleTopology`, `ObjectProperty.IsTriangulated`, `DerivedCategory`,
  `DerivedCategory.Q`, `DerivedCategory.singleFunctor`, categorical limit/colimit
  cones and cocones, `IsFiltered`. The size and scheme-conventions nodes are conventions,
  not definitions requiring replacement declarations.
- `WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale`: the recorded
  pro-affine-etale/weakly-etale interface for `sk-def-pe-morphisms`.

All already stated proof dependencies' modules are imported without `public`:
ring-sheaf base-change mates, internal module operations transport, augmented Cech
pushforward model, qcqs finite-family geometry, finite-product injective resolutions,
weakly-etale localization, short-exact-complex triangles, and derived products.
The three new stage-1 route lemmas (etale coinduction, conditional ind-etale continuity,
weakly-etale ind-etale Cech refinement) have no recorded Lean module yet; no fictitious
import or assumption of those conclusions was added. Qcqs permanence is likewise
not recorded as a Lean module. The full six proof steps and all dependency ids are
included in the theorem docstring verbatim from the DAG, wrapped to the line limit.

Edge cases checked before writing: `nil` gives J = identity; no nonempty scheme or
cover-index hypothesis excludes the empty scheme. The zero model is allowed by the
finite-presentation local-model predicate. The finite ring clause allows the zero
ring, including n = 0 when all its elements vanish. No nontriviality of the coefficient
or model was added. The hull definition includes the empty product, all integer shifts,
retracts in the correct composition order, filtered categories with nonemptiness,
and one termwise lower bound shared by the entire strict diagram. A nonsurjective
quasi-compact open immersion is a valid b. Noetherianity, finite type and a uniform
cohomological-dimension bound were checked absent from the signature.

Searches for a matching statement (2026-10-25):

- `msearch.py leanfinder`: "Derived pushforward along a quasi compact quasi separated
  weakly etale scheme map of a supported finite scalar local model belongs to the
  supported model hull". Eight hits, on qcqs scheme geometry and ideal-sheaf supports;
  no coinduction/hull theorem. Named hits include
  `AlgebraicGeometry.exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated` and
  `AlgebraicGeometry.Scheme.IdealSheafData.support_map`.
- `msearch.py loogle`: `AlgebraicGeometry.ProEtale.supportedModelHull,
  AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward`.
  Zero hits (unknown project identifier `supportedModelHull` in the Mathlib index).
- `msearch.py grep`: `supportedModelHull|ScalarModelSupportChain|supported.model.coinduction`.
  Zero Mathlib hits.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the node id and proposed declaration name: the only node-id hit is the parent
  descent proof docstring, which explicitly calls this coinduction obligation unstated.
  No existing theorem matched. Concept searches for support chains and supported hulls
  found `SupportedModelHull.lean`, which is reused, and the parent descent module,
  which states a distinct conclusion about arbitrary local hull membership.
- DAG search for the support-chain/hull notion found `def-sfb-supported-model-hull`;
  its declaration is used and its id added, rather than creating another definition.

Source and repair-note check: read the current blueprint's refinement paragraph, the
node's full current statement/proof, and its resolved stage-1 maintenance note. That
note removes the obsolete all-continuous algebraic-closure case and requests retaining
the five coefficients and general qcqs site arrow; this delivery follows it. The
node explicitly labels the generator theorem agent-formulated with an exact reference
WANTED; it is not misattributed to HRS Corollary 4.7 or Lemma 5.3.
No statement correction or STATEMENT-DISPUTED flag is needed.

Validation: `scompile.py NL lem-sfb-proetale-supported-model-coinduction` compiled this
module separately on the server in sandbox and library mode (7.5 s and 11.1 s), with
no errors or warnings. `set_option autoImplicit false` is explicit; all variables and
universes are bound, all lines have at most 100 characters, and the single proof is
`sorry`. Delivery preflight is run using `deliver2.py --no-push` before the push.

## Second reading by NL

Independent second reading by the maintainer review (cc review service, delivery 80bdfeee),
replacing the worker's self-declared non-independent note. Read against the node statement,
`def-sfb-supported-model-hull` (`Sheaf.Paper.SupportedModelHull`), the recorded
`sk-def-sfb-constructible`, `sk-def-sfb-module-derived-pushpull`,
`def-sfb-module-open-lower-shriek`, `def-sfb-module-lower-star`, `sk-def-pe-morphisms`
declarations, and the landed parent `supportedModelHull_proetale_descent`.

Node list and Lean rendering:

- prime ℓ, closure, finite E, finite A killed by ℓ^n; Λ ∈ {A, Z_ℓ, O_E, Q_ℓ, E} with
  all-continuous condensed rings: `(ℓ : ℕ) [Fact ℓ.Prime]`, `Λ` commutative condensed ring,
  five-way `hΛ` with ring isomorphisms `Mon.mk Λ ≅ Mon.mk (...)`. Byte-identical to the
  landed parent's hΛ; the removed all-continuous closure coefficient is absent. Correct.
- Λ_V, A_V = Mod_{Λ_V}, ordinary D(A_V): `condensedRingObj Λ X`, `Mod (Sheaf (ProEt.topology X)
  Ab.{u+1}) ...`, Mathlib `DerivedCategory`. Correct.
- U, V qcqs: `[CompactSpace] [QuasiSeparatedSpace]` on both. Correct, nothing stronger.
- b object of V_proét, qc, qs: `[WeaklyEtale b] [QuasiCompact b] [QuasiSeparated b]`
  (Scheme.ProEt V = weakly étale V-schemes). No surjectivity/contractibility. Correct.
- support chain W → ... → U, open qc / closed with qc complement, J composite, identity
  for the empty chain: `ScalarModelSupportChain U W` and `p.extension Λ`
  (open `openImmersionLowerShriek`, closed `lowerStar`, `nil` ↦ `𝟭`). Correct.
- finite scalar local model L on W: `HasFiniteConstantLocalModel Λ W L` (pro-étale cover,
  per-member finitely presented Λ-module pulled back from the point) — the same predicate
  the hull uses for its generators. Correct.
- G_V: `supportedModelHull Λ V` = intersection of classes satisfying
  `IsSupportedModelHullClass` (triangulated, replete, retracts i ≫ p = 𝟙, small products,
  strict filtered colimits with common lower bound, generators in degree 0). Matches node.
- conclusion Rb_*((JL)[0]) ∈ G_V: `moduleObjectDerivedPushforward Λ b` =
  `(lowerStar Λ b).rightDerivedFunctor` applied to `singleFunctor _ 0` of `(p.extension Λ).obj L`.
  Actual uncompleted derived direct image, explicit generators only. Correct.

Edge cases: empty chain (`nil`), empty U/V/W (no nonemptiness hypothesis), zero ring A
(n arbitrary), zero model (finitely presented zero module) all covered. No Noetherian,
finite-type or cd hypothesis. Universes: schemes `u`, site/abelian values `u+1` as in the
hull node; A in `Type` loses no finite ring isomorphism class (same as parent).

One definition per notion: hull, chains, extension, local model, derived pushforward and
coefficients are all the recorded owners; no new declaration. Statement field verbatim
equal to the file signature; stmt_deps change is only the added owner
`def-sfb-supported-model-hull`. Proof `sorry`; docstrings carry the source place,
`(blueprint: ...)`, and the six proof steps.

Verdict: the Lean statement says exactly what the node says. No mismatch; nothing changed
in Lean.
