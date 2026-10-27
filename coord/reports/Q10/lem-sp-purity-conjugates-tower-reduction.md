## Worker report

This delivery states `lem-sp-purity-conjugates-tower-reduction` in
`Sheaf.Paper.PurityConjugatesTowerReduction`. The two postponed theorems are
`AlgebraicGeometry.ProEtale.SpPurityReduction.pullbackTower_bounds` and
`AlgebraicGeometry.ProEtale.SpPurityReduction.purity_conjugates_tower_reduction`.
The four helper definitions contain actual composites and no postponed data.
The node statement and its dependency lists are unchanged.

Hypotheses and conventions:

- `l`, `[Fact l.Prime]`, `E`, `[Field E]`, `[Algebra (Padic l) E]` and
  `[FiniteDimensional (Padic l) E]` are the specified finite coefficient extension.
  `[b : SpTowerShriek.Base l E]` retains the actual valuation-ring quotient,
  ramification exponent, unit equation, and equality `Base.ideals` with the
  uniformizer-power quotient. `SpTowerShriek.R l E n` means the paper's R_(n+1),
  so every positive exponent, including exponent one, occurs.
- `D : FiniteFieldDatum`, `[CharP D.k D.p]`, and `hne : l ≠ D.p` give the finite
  field, its chosen algebraic closure, and the distinct coefficient prime.
- `X.Over`, `Y.Over`, and `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` on
  their structure maps express separated finite-type schemes over D.k.
  `IsNoetherian X/Y` and quasi-compactness of f are the redundant Noetherian
  consequences already used by the finite-level interfaces; they exclude no
  scheme in the statement.
- `f = j ≫ p`, with open immersion j and proper p, displays an arbitrary Nagata
  compactification, using `SpTowerGamma.factorization j p`. This is auxiliary
  compactification data for the prescribed compact-support adjunction, not an
  affine-space factorization. Every separated finite-type f in the node has one.
  `(j ≫ p).IsOver` says f is a k-morphism. `d : ℕ` and
  `[SmoothOfRelativeDimension d (j ≫ p)]` give the exact pure relative dimension.
- `o`, `q` are the existing section-preserving ordinary derived calculus and
  scalar coordinates. `SpTowerCalculus.C` is the full UNNORMALIZED uniform
  constructible finite-Tor subcategory. `hF`, `G`, `adj`, `lv` are precisely the
  compact-support restriction, right adjoint, and finite evaluations supplied by
  `det-sp-tower-gluing`. No different right adjoint or coefficient map is chosen.
- `w` is the existing strict Tate tower. `roots`, `unitsX`, `cc`, `tc`, `gc` retain
  its generator-normalized root realization and the canonical site, tensor and
  pullback coordinate comparisons. They are the existing constrained coordinate
  records, not arbitrary endpoint isomorphisms. Their section, adjunction and
  K-flat-representative normalizations fix every comparison used in the formulas.
- `K : SpTowerCalculus.C l E b q Y` is the given tower. There is no
  `IsSpNormalizedTower` hypothesis, no flatness hypothesis on any quotient, and
  no invertibility hypothesis on an input reduction.

Conclusions, clause by clause:

1. `pullbackTower` is the actual functor `SpTowerGamma.source` (derived pullback
   followed by the ordered product of d positively shifted Tate root lines),
   carried back by the specified strict-tower realization. This is P=f* K(d)[2d].
   `pullbackTower_bounds` first asserts `spConstructibleTorTowers ... P`.
2. For every common Tor interval `[a,z]`, expressed by
   `∀ n, HasProEtaleTorAmplitude ... K_n a z`, its second clause asserts both
   `SpTowerCalculus.cohomologicalInterval` and `HasProEtaleTorAmplitude` of P_n
   in `[a-2*d,z-2*d]`, uniformly in n. This includes the degree-zero coefficient
   unit test that supplies the cohomological bound.
3. The main theorem supplies `gamma n : P_n ≅ (GK)_n`. Its first conjunct asserts
   that the source and target evaluation comparisons are invertible and pins
   gamma to a finite `alpha` satisfying `FiniteSmoothPurity.OrientationNormalized`.
   The displayed equation uses exactly `FiniteSmoothPurity.gamma` followed by
   `SpTowerGamma.finiteRightComparison` (uniqueness of right adjoints preserving
   the compact-support counit). Thus gamma is the specified inverse diagonal
   orientation/tensor-counit transpose, rather than an arbitrary family making
   the desired reduction square true. `sourceComparison` and `targetComparison`
   are explicit canonical composites; their data are not assumed.
4. For every `m n : ℕ` and `h : m ≤ n`, the first reduction conjunct is exactly
   `lv.reduction`, written out: after the fixed finite evaluation comparisons,
   the actual reduction of GK is `SpTowerGluing.coefficientMate` followed by
   `(lv.right m).map` of the ACTUAL `SpTowerCalculus.reduction` of K. The mate is
   the inverse compact-support coefficient comparison and actual adjunction
   counit, transposed under the target finite adjunction. It is not defined
   using purity.
5. The second reduction conjunct is
   `scalar.map (gamma n).hom ≫ rhoGK = rhoP ≫ (gamma m).hom`.
   Lean's composition order is left to right; this is precisely the node's
   displayed purity square.
6. The third conjunct is
   `rhoGK = scalar.map (gamma n).inv ≫ rhoP ≫ (gamma m).hom`, the asserted
   conjugacy. The finite purity comparisons are isomorphisms, while rhoK need
   not be one.
7. The final conjunct spells out the pullback-reduction formula with canonical
   coefficient comparisons. `e : CoefficientLineComparison` is fixed on root
   powers and every scalar/root generator, and its derived isomorphism is the
   actual scalar-single counit. The ordinary etale morphism `r` is tied by an
   explicit equality to the actual rhoK through `reductionSiteScalarIso` and
   the retained origins. It is not a freely chosen substitute for rhoK.
   The final equation says `scalar.map sourceComparison_n ≫ rhoP` equals the
   canonical site/scalar comparison, followed by
   `pullbackTwistComparison.hom ≫ puritySource.map r`, followed by
   `sourceComparison_m`. This is exactly rhoP=H_m(rhoK) after the canonical
   pullback, twist, shift and coefficient identifications in the node.
8. Every intrinsic scalar operation is `scalarExtensionFunctor` for the actual
   quotient `SpTowerCalculus.quotient l E h`, with target-ring action. The lifted
   ordinary etale comparison uses `RingHom.ulift` of that SAME quotient.

Dependency declarations used (including their imported modules):

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and
  `Sheaf.Paper.SmoothPurityCoefficientTowers`: the finite coefficient extension,
  `spEllIdeal`, `spCoefficientTowers`; `SpTowerShriek.R` and `Base.ideals` retain
  these exact quotients.
- Mathlib `AlgebraicGeometry.Morphisms.Smooth`, `FiniteType`, `Separated` and
  `Over`: `SmoothOfRelativeDimension`, `LocallyOfFiniteType`, `QuasiCompact`,
  `IsSeparated`, `IsOpenImmersion`, `IsProper`, scheme-over-base instances.
- Mathlib `Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`.
- `Sheaf.Paper.SmoothPurityNormalizedTowers`: `spConstructibleTorTowers`,
  `spDerivedCoefficientEvaluation`, `spFiniteConstructibleTorCategory`.
- `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`,
  `Sheaf.Paper.CoefficientTowerShriekInterfaces`: exact evaluation,
  `SpTowerCalculus.Coordinates`, `C`, `reduction`, `quotient`, `cohomologicalInterval`.
- `Sheaf.Paper.SmoothPurityTowerShriekLevels`: `Base`, `Operations`, `pull`,
  `tensor`, `Ev`; its tensor is the existing ordinary derived tensor, not a
  newly defined operation.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted` and
  `Sheaf.Paper.SmoothPurityTowerChartAdmissibility`: the actual coefficient
  twists and `SpChartAdmissibility.Twists`.
- `Sheaf.Paper.SmoothPurityTowerGluing`: `support`, `Levels`, `level`,
  `coefficientMate`, actual reduction and counit normalization fields.
- `Sheaf.Paper.DerivedPullbackTensorHom`,
  `Sheaf.Paper.DerivedPullbackTensorIso`: canonical finite derived pullback and
  tensor/reduction comparisons (`WeilConjectures.derivedPullbackTensorIso`).
- `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`: `scalarExtensionFunctor`.
- `Sheaf.SecSmoothPurity.ReductionExceptional`: `reductionSite`,
  `reductionSiteScalarIso`, `ReductionExceptionalRealization`.
- `Sheaf.Paper.SmoothPurityMap`, `Sheaf.Paper.FiniteSmoothPurityMaps`:
  `WeilConjectures.PurityFiniteSetting.smoothPurityMap`, and its ordinary finite
  inverse-orientation/tensor-transpose presentation
  `FiniteSmoothPurity.OrientationNormalized`, `line`, `puritySource`, `gamma`.
- `Sheaf.Paper.FiniteSmoothCoefficientArrows`: `CoefficientLineComparison`,
  `pullbackTwistComparison`, `ordinaryScalar`.
- `Sheaf.SecSmoothPurity.ReductionCompatibilities`,
  `Sheaf.SecSmoothPurity.FiniteGeneralRing`: finite coefficient-purity
  compatibility and natural finite smooth purity (proof tools).
- `Sheaf.Paper.SmoothPurityTowerGamma`: ONLY `source`, `orderedLine`,
  `inputWord`, `targetWord`, `coefficientWord`, `factorization`,
  `finiteRightComparison` and their canonical coordinate definitions.
  Neither `tower_gamma`, `Purity`, `FiniteLevels` nor any normalized-tower
  conclusion is used. These existing definitions are reused to obey one
  definition per notion. The later tower_gamma proof cites this item; its
  proof import of this module must therefore be split from its existing
  canonical word definitions when stage 3 fills that proof. There is no use
  of that later theorem in this statement or either proposed proof.
- Proof-only imports: `Sheaf.Paper.PullbackTorAmplitude`,
  `Sheaf.Paper.TwistPreservesFiniteness`,
  `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations`.
  `lem-sp-finite-orientation-reduction` is cited by the node's proof and is not
  yet given a usable recorded Lean declaration; no fabricated declaration is
  imported, and the orientation normalization is displayed explicitly here.

Edge cases checked against the definitions: exponent one is index zero (no
O_E/ell^0 level is introduced); `m=n` is allowed and the quotient and root power
are the identity; relative dimension zero uses the actual coefficient unit and
zero shift; empty X/Y and zero K are allowed. Arbitrary zero/noninvertible tower
transitions remain allowed. Ramified E uses the recorded positive ramification
and equality of ideals, never assumes ell is a uniformizer. Nonflat quotient
Z/ell^2 -> Z/ell is allowed, and tensor/scalar operations remain derived.
The shift sign was checked directly: H^i(C[2d])=H^(i+2d)(C).

Searches performed for an existing statement:

- msearch.py leanfinder: “Exceptional pullback tower reductions are conjugate by
  finite smooth purity to shifted twisted pullback reduction maps”. Eight
  unrelated scheme-pullback or module-conjugation results; no tower statement.
- msearch.py loogle: `"smoothPurityMap"`. Zero hits.
- msearch.py grep: `purity.*reduction|exceptional.*reduction|smoothPurity`.
  Zero Mathlib hits.
- rg in lean/WeilConjectures for the same expression: finite/generic smooth
  purity and other purity constructions, no actual tower-reduction conjugacy.
- grep -rn of the item id in lean/WeilConjectures: no hits.
- rg in lean/Sheaf for purity conjugacy: no existing theorem. The proof
  docstring of SmoothPurityTowerGamma names this item; its canonical word
  definitions supply the reusable source/target normalizations.
- rg of the new namespace and theorem name in lean/Sheaf,
  lean/WeilConjectures and dag/lean_names_upstream.json: no collision.

No statement correction, no new independent notion, and no definition data
containing sorry. Both postponed proofs include the natural-language proof
steps and node/source references in their docstrings.

## Second reading by Q10

(Written by the maintainer's independent reader, NT-cc review of delivery
e16975ff, 2026-10-25. The delivered section said that no independent reading
was made. That is fault H11. This section replaces it. The Lean and the records
are unchanged.)

Node list against the Lean (`Sheaf.Paper.PurityConjugatesTowerReduction`):

- k0 finite, k its algebraic closure, ℓ ≠ p: `D : FiniteFieldDatum` (D.k is the
  closure), `[CharP D.k D.p]`, `hne : l ≠ D.p`. OK.
- E/Q_ℓ finite, O_E, ϖ_E, ℓ = uϖ^e, R_n = O_E/ℓ^n: `[Field E] [Algebra (Padic l) E]
  [FiniteDimensional ..]`, `[b : SpTowerShriek.Base l E]`. `SpTowerShriek.R l E n`
  is the paper's R_{n+1}, so every positive level occurs. OK.
- X, Y separated finite type over k: `X.Over`, `IsSeparated`, `LocallyOfFiniteType`,
  `QuasiCompact` on the structure maps. `IsNoetherian X/Y` and `QuasiCompact (j ≫ p)`
  follow from these, so they exclude nothing. OK.
- f smooth separated of pure relative dimension d ≥ 0: `f = j ≫ p` with
  `IsOpenImmersion j` and `IsProper p` (any Nagata compactification, which exists
  for every such f). `[SmoothOfRelativeDimension d (j ≫ p)]` with `d : ℕ`;
  `(j ≫ p).IsOver`. OK.
- C_T, F ⊣ G with finite units, counits and evaluations: `SpTowerCalculus.C`, which is
  the unnormalized uniform ctf subcategory. `hF`, `G`, `adj`, `lv` are exactly the
  `det-sp-tower-gluing` interface (`SpTowerGluing.support`, `Levels`), the same as in
  the landed `tower_gamma`. OK.
- Twists and coordinates: `w : SpChartAdmissibility.Twists`. `roots`, `cc`, `tc`, `gc`
  are pinned structures: RootLines by sections (Kummer and root projection),
  CoefficientCoordinates by `unit_sections` and `line_sections`, and tensor and
  geometric coordinates by their K-flat normalizations. A universal quantifier over
  them is therefore not a free choice. `unitsX` is a consequence of ℓ ≠ p. OK.
- K ∈ C_Y, with no normalization, flatness or invertibility hypothesis on ρ^K. OK.
- P = f^*K(d)[2d]: `pullbackTower` is `realization.inverse` of `SpTowerGamma.source`,
  which is the pullback tensored with `orderedLine d` = unit ⊗ (Λ(1)[2])^{⊗d}. OK.
- "P ∈ C_X; interval [a-2d, b-2d]": `pullbackTower_bounds`, first conjunct
  `spConstructibleTorTowers`. Second conjunct: for all a ≤ z with a common Tor
  amplitude of K_n in [a,z], it gives both the cohomological interval and the Tor
  amplitude of P_n in [a-2d, z-2d]. The sign checks: H^i(C[2d]) = H^{i+2d}(C).
  `a ≤ z` only drops the empty interval, where K = 0. OK.
- ρ^P = f^*_{R_m}(ρ^K)(d)[2d] under the canonical identifications: this is the last
  conjunct. `e : CoefficientLineComparison` is unique (roots by `roots_power` through
  the mono ι, sheafIso by its generators, derivedIso by `derived_normalization`).
  `r` is tied to the actual ρ^K through `originIso` and `reductionSiteScalarIso`.
  Any two such r have the same site image, and so they give the same right-hand
  side. The equation is j-conjugated H_m(ρ^K). The directions of both
  `reductionSiteScalarIso` uses agree. OK.
- ρ^GK = f^!(ρ^K) ∘ c(K_n): the first reduction conjunct. It is `Levels.reduction`
  verbatim, with `coefficientMate` (the counit transpose c_{n,m}, not defined from
  purity). OK.
- γ_{f,R_n}(K_n): `gamma n` exists and is pinned. `sourceComparison` and
  `targetComparison` are explicit composites, and both are asserted IsIso. The
  equation `source ≫ gamma = reductionSite.map (FiniteSmoothPurity.gamma alpha ≫
  finiteRightComparison.inv) ≫ target` holds with `alpha` OrientationNormalized
  (inverse diagonal orientation with the Kummer-normalized bundle adjoint). This is
  the pin used by the landed `tower_gamma.FiniteLevels`. OK.
- Purity square: `scalar.map γ_n ≫ ρ^GK = ρ^P ≫ γ_m`. This is the node's
  ρ^GK∘(γ_n)_{R_m} = γ_m∘ρ^P, written in diagrammatic order. OK.
- Conjugacy: `ρ^GK = scalar.map γ_n.inv ≫ ρ^P ≫ γ_m`. This is
  γ_m∘ρ^P∘((γ_n)_{R_m})^{-1}. ρ^K is not inverted. OK.
- Scalar extension with its target-ring structure, including nonflat quotients:
  `scalarExtensionFunctor (SpTowerCalculus.quotient l E h)`, with no flatness
  hypothesis. OK.

Edge cases: m = n (identity quotient); d = 0 (unit line, zero shift); empty X or Y;
K = 0; zero or noninvertible transitions; ramified E (handled by `Base.ideals`);
the nonflat Z/ℓ² → Z/ℓ.

Advisories for the maintainer, not delivery faults:

- M1: the statement uses plain composites of the `det-sp-tower-gamma` module
  (`source`, `orderedLine`, `inputWord`, `targetWord`, `coefficientWord`,
  `factorization`, `finiteRightComparison`). That node's proof cites this item, so
  the stage-3 back-import is left out under stages/2 §3 rule 7, as the worker report
  lists. These helpers should move to a definition-node module.
- M2: owners that are used but not cited: def-sp-p1-{coefficient-coordinates,
  tensor-derived-coordinates, geometric-coordinates, level-words},
  def-sp-coordinate-right-comparisons, def-sp-chart-tate-tower-data,
  def-sp-coefficient-tower-shriek-interfaces, def-pur-finite-smooth-canonical-maps,
  def-pur-finite-smooth-coefficient-arrows, def-pur-finite-ring-section-data and
  def-weil-proetale-tor-amplitude. The det-sp-tower-shriek-levels and
  det-sp-reduction-exceptional definitions are reached through the cited
  det-sp-tower-gluing, det-sp-reduction-compatibilities and det-sp-finite-general-ring.

Searches: a grep for `purity.*reduction|exceptional.*reduction` in lean/Sheaf and
lean/WeilConjectures found only tower_gamma, which states no reduction conjugacy.
The node's duplicate candidates (tower-reduction-transpose,
compact-support-tower-reduction) state other things.

## Validation

The formatted module passed scompile.py on 2026-10-25 in both sandbox and
library-module modes, with no errors or warnings. The prescribed deliver2.py
--no-push dry run printed OK: preflight and per-file compilation passed. All
compiles used the prescribed wrapper against the live published library.
