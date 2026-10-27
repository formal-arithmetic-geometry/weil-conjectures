## Worker report

The module `Sheaf.Paper.AdicRoosRealizationReductions` states
`WeilConjectures.AdicRoos.realization_reductions`, with proof `sorry`.
The five helper definitions contain real data and belong to this realization
statement; they neither choose cones nor introduce another scalar extension.
No new node, dependency repair, or statement correction is needed.

Hypotheses and objects, in the order of the node:

- The global finite-field datum is `D : FiniteFieldDatum.{d}`, the prime is
  `l : ℕ` with `[Fact l.Prime]`, and `hl : l ≠ D.p`. The extension is
  `E : Type u` with its field, `ℚ_[l]`-algebra and finite-dimensional instances.
  `W : Scheme.{t}` retains independent scheme and coefficient universes.
- `completedIntegralDerivedCategory l E W D hl` is D(R) for the actual inverse
  limit of finite constant coefficient sheaves. `normalizedDVRDerived l E W n`
  is D(B_(n+1)). The positive exponent n+1 convention covers every paper level.
  The small pro-etale site has object universe t+1 and morphism universe t;
  coefficients and modules have universe max u (t+1).
- `scalarReductionDerivedExtension` is the recorded canonical derived tensor;
  `normalizedDVRResCompleted` is the recorded exact derived restriction along
  the same completed projection. These restrictions agree definitionally with
  `scalarReductionDerivedRestriction`; this identification was compiler checked.
- `adjunction` selects the normalized adjunction from
  `derivedScalarExtensionRestrictionAdjunction`, whose unit is induced by the
  completed coefficient projection. This is a choice from a universal property,
  not a choice of an unspecified mathematical object.
- `P` and `_hcomplete : IsDerivedComplete ... P` are precisely the ordinary
  unbounded object and its augmented reduction Roos-triangle condition. The
  currently recorded `IntegralOnSlice.IsComplete` publicly reexports this
  global predicate through `IsDerivedCompleteUnrestricted`; no new completeness
  notion is defined here.
- `S` is an object of D(strict R-module towers). `Sfinite`, `Siso`, and `bS`
  are the specified finite S_n, evaluation identifications, and quotient-linear
  isomorphisms red_n(P) ≅ S_n. `_hbS` identifies every evaluated transition with
  its canonical reduction transition, transported through bS. Thus S is the
  strict reduction tower with the prescribed quotient-compatible identification,
  rather than an unrelated tower having only isomorphic objects at each level.
  The canonical transition is `quotientUnit`: transpose η_n through the m-th
  scalar adjunction and the canonical composite-restriction isomorphism. This
  is the adjoint form of the canonical scalar associator, including m=n.
  The recorded `canonicalIntegralReductionTower` is imported; the displayed
  condition uses its intrinsic derived scalar-unit description, equivalent to
  its K-flat x↦1⊗x augmentation and id⊗quotient transition.
- `T : NormalizedDVRTower ...` supplies T_n, all finite quotient transitions,
  identity and cocycle, their invertible adjoints, the coherent strict derived
  tower, and its actual evaluation identifications.
- `G : S ⟶ T.tower`, `g n : Sfinite n ≅ T.M n`, and `_hG` express exactly the
  prescribed restriction-linear evaluation of the derived strict-tower map.
- `RF`, `η`, `_hRF`, products, `p`, `δ`, `_hroos` and `_hnatural` unpack the
  total right derived inverse-limit functor and its natural Roos triangles from
  `ringedStrictTowerHomotopyLimitIndependentCoefficients`. They are the chosen
  functor/triangle data the statement instructs us to use. The localization Q
  instances are written explicitly as `HasDerivedCategory.standard`, with no
  extra size equality or mathematical hypothesis. `evaluated` is the canonical
  derived evaluation tower using `normalizedDVRTowerTransition`; it does not
  choose arbitrary transitions. `RF.obj S` and `RF.obj T.tower` are L_S and L_T.

Conclusions, clause by clause:

- `IsIso (RF.map G)` states that F = R lim G is invertible.
- `∃ e : P ≅ RF.obj S` gives the required isomorphism to L_S. The first
  universal clause is e followed by p S, the n-th product projection, and Siso;
  its right side is exactly cS_n = η_(n,P) followed by Res_n(bS_n).
- `projection RF p T n` is p T.tower followed by the n-th product projection
  and T.evaluationIso. It is the actual pT_n in D(R).
- `reduction RF p T n` is defined by the inverse Hom bijection of `adjunction`
  applied to that very projection, and is therefore the requested bT_n.
  `∀ n, IsIso (reduction ...)` is the isomorphism clause for every bT_n.
- `e.hom ≫ RF.map G` is gamma. The next universal clause is its required
  projection identity in D(R), with Res_n(g_n) following cS_n.
- The next clause is red_n(gamma) followed by bT_n = bS_n followed by g_n,
  in D(B_n). No faithfulness of derived restriction is assumed or used.
- The final clause, for EVERY m≥n, is
  bT_m followed by tau_(m,n) = quotientUnit(L_T) followed by Res_(m,n)(bT_n),
  an equality in D(B_m). Transposing it through finite scalar extension gives
  exactly alpha_(m,n) followed by L_(m,n)(bT_m) = bT_n followed by a_(m,n).
  The composite-unit normalization fixes this equivalence. Since T carries
  tau_refl and tau_comp, the all-pairs equation includes identity and iterated
  quotient normalization. No arbitrary finite tensor functor or associator is
  substituted for the canonical one.
- There is no uniqueness, boundedness, constructibility, stratification, or
  common integral-model clause or hypothesis.

Dependency declarations read and used:

- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: the constant quotient
  cone and `integralConstantToCompletionOfUniverses`; its imports provide the
  existing completion and coefficient projections, not a discrete constant ring.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and its topology.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `scalarReductionDerivedExtension`, `scalarReductionDerivedRestriction`,
  `derivedScalarExtensionRestrictionAdjunction`, and their normalized units.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategory`, underlying all the recorded exact restrictions
  and evaluations; `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.Paper.DerivedCompleteOnSlices`: the recorded completeness definition
  and its global reexport `IsDerivedComplete` from `Sheaf.Paper.DerivedComplete`.
- `Sheaf.Paper.IntegralReductionTowerCanonical`: the canonical augmented
  reduction tower and its K-flat realization; the intrinsic reduction transition
  here is the scalar-adjunction formulation of those same maps.
- `Sheaf.Paper.NormalizedDVRTower`: `NormalizedDVRTower`,
  `normalizedDVRResCompleted`, `normalizedDVRResCompletedComp`,
  `normalizedDVRRes`, `normalizedDVRTowerEvaluation`,
  `normalizedDVRTowerTransition`, and `normalizedDVRDerivedTowers`.
- `Sheaf.Paper.CompletedDerivedInverseLimit`: `Scheme.CompletedDerivedInverseLimit`
  reexports the Roos property, not a purported canonical cone functor.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `IsDerivedLimitTriangle`, and Mathlib's triangulated structure/triangle criterion.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `ringedStrictTowerHomotopyLimitIndependentCoefficients`, whose total derived
  limit and natural Roos data are explicitly bound in the theorem.
- Proof import `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`:
  `SheafOfModules.SuccessiveDerivedQuotient.successive_derived_quotient_normalization`.

Edge cases checked: level zero in Lean is exponent one, not the forbidden exponent
zero; m=n uses the canonical restriction identity, and all nonconsecutive quotients
are included. The zero object and empty scheme impose no nonzero/support condition.
Neither B_2→B_1 nor any other quotient is assumed flat. Unbounded objects and complexes
are admitted. S is not required to have any finiteness condition or a chosen common
integral model. Independence of t,u,d was retained and compiled. No arbitrary inverse
map is assumed and restriction is never asserted faithful.

Searches for existing statements (all on 2026-10-22):

- `msearch.py ... leanfinder "Roos realization of derived complete complex with
  prescribed quotient linear reductions"`: eight hits, ordinary adic completion
  and local cohomology; no derived sheaf-tower realization statement.
- `msearch.py ... loogle "CategoryTheory.Pretriangulated.isIso₁_of_isIso₂₃"`:
  the generic triangle isomorphism criterion, only one ingredient.
- `msearch.py ... grep "Roos|homotopyLimit|derived.*[Ll]imit.*[Ii]so"`: zero hits.
- `msearch.py ... leansearch "Derived inverse limit projections scalar extension
  restriction adjunction complete reduction tower"`: eight hits, ordinary
  module extension/restriction adjunctions and scalar restriction; no match.
- `rg` in `lean/WeilConjectures`, `dag/lean_names_upstream.json`, and
  `lean/Sheaf` for Roos, realization, normalized towers and completeness found
  generic derived-limit/triangulated lemmas, reduction tower constructions,
  completion models and more specialized realization statements, none stating
  this full realization theorem with its prescribed quotient-linear reductions.
- Searching the exact node id under `lean/WeilConjectures` found no declaration.

Validation: prescribed `scompile.py Q14 lem-pur-adic-roos-realization-reductions`
compiled the delivered module in sandbox and library modes, with no errors or
unexpected warnings (39.4 s and 26.1 s). Initial probes were repaired and removed.

## Second reading by Q14

A second pass by the dispatched worker compared the final file with the node; no
other agent was started, as the dispatch explicitly prohibits it. Independent
review belongs to the maintainer. This pass found and removed an unnecessary
`NormalizedDVRTower` structure on S: the final S is an arbitrary coherent strict
reduction tower, equipped only with the finite reductions and their prescribed
compatibility. It also checked the order of every composition: e then F, unit then
Res(bS) then Res(g), and red(gamma) then bT. The final normalization uses tau before
finite adjunction, preserving its quotient-linear meaning even for nonflat maps.
All hypotheses, both equalities, all-pairs quotient normalization, and the explicit
absence of uniqueness and finiteness assumptions match the node. No node fault or
STATEMENT-DISPUTED issue was found. The statement and helper bodies were reread
against the source blueprint final sentence and the node's five-step proof.
