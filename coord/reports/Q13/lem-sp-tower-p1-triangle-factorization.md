## Worker report

The delivery states `AlgebraicGeometry.ProEtale.SpTowerP1.towerP1TriangleFactorization`
in `Sheaf.Paper.TowerP1TriangleFactorization`. All theorem proofs are `sorry`.
Definitions contain actual composites of the recorded functors, maps and normalized
isomorphisms. The item statement and its dependencies are unchanged. A dependency
module exposes the shifted Tate line's membership in the already recorded domain.

Source read: the current `literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md`, especially
“Reduction of the triangle identities”. Its first paragraph is exactly the
reduction asserted by this node; the subsequent degree-zero levelwise argument
normalizes the scalars and is deliberately not asserted here.

Hypotheses and objects, clause by clause:

- A prime ell is `(l : ℕ) [Fact l.Prime]`; a finite coefficient extension is
  `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`.
  The existing `Padic.coefficientExtensionIntegers` supplies its ring of integers.
- The arbitrary scheme and invertibility are `{S : Scheme.{u}}` and
  `{hS : IsUnit (l : Γ(S, ⊤))}`. There is no base-field, Noetherian,
  constructibility, finite-Tor, normalization or compact-base assumption.
- `Presentation l E S hS` supplies the actual tower calculus and normalized
  classes. `SpTowerShriek.R/B/tau` are the existing constant quotients and
  quotient transitions, indexed by n : Nat for the exponent n+1. No level zero
  is inserted. `SpTowerShriek.D` is the ordinary module-system localization.
- `C l E p.classes.base T` is the existing full subcategory: one uniform
  bounded-below tower bound, and an existing retained `Origin` at every level.
  It imposes neither cartesian reductions nor transition-compatible choices of
  etale antecedents. `FixedEtaleOriginWitness` is the recorded retained pair.
- The existing `ProjectiveLine S`, `diagonalSurface S`, `diagonalImmersion S`
  and `Etale.projectiveLineDiagonalProjection S a` give P, W, Delta and p_i.
  The Boolean false is p1 and true is p2.
- `p.classes`, `p.delta`, `p.trace`, and `line` give the actual signed Kummer
  diagonal and shifted Tate line, and inverse-splitting trace. The traces for
  the projections are defined as the canonical base changes of that splitting
  trace: inverse exchange at T, pulled trace, coefficient-unit identification.
  This is the inverse-exchange expression of the specified base-changed
  splitting, not a freely supplied trace or a map with only levelwise properties.
- `p.F` and `p.G` are exactly Rq_* and q^*(-)(1)[2]. `d : Maps l E p` retains
  the specified invertible projection/exchange words and closure of the domains;
  `h : EtaleOriginComparisonsWithLine l E p d` retains the comparison node's
  full interface and the Tate-line specialization explained below.
- `eta l E d` and `epsilon l E d` are imported without alteration: their
  definitions use the diagonal source, inverse supported projection, delta,
  twist projection, inverse exchange, and inverse q projection plus trace,
  respectively. Neither is chosen from an adjunction F ⊣ G.

Conclusions and the expanded words:

- The first conjunct is `F.map (eta M) ≫ epsilon (left.obj M) =
  F.map (scalarContraction M.obj (diagonalScalar h false))`.
- The second is `eta (rightRestricted.obj K) ≫ G.map (epsilon K) =
  scalarContraction (G.obj K.obj) (diagonalScalar h true)`.
- `diagonalScalar h a` is exactly `sourceUnitAt a A_P ≫ push_i.map delta ≫
  projectionTrace h a`. Thus alpha_i occurs on its source. The coefficient
  endomorphism is not replaced by 1, nor by an arbitrary scalar.
- `scalarContraction` is right-unitor inverse, tensor map `(id,c_i)`, right
  unitor. This makes both tensor-unit identifications in the statement explicit.
- The third conjunct identifies the first triangle with F applied to
  `expandedContraction h false M`. This is the expanded R(qp1) word in the
  nested Rq_* Rp1_* coordinates, using the canonical composite adjunction.
- The fourth identifies the second triangle with the analogous p2 word on
  `rightRestricted.obj K`. The comparison p1*GK = p2*GK is the recorded
  pullback square through qp1 = qp2, not an unspecified isomorphism.
- The final two conjuncts, for p1 on M and p2 on GK, are the source-factor equations
  `diagonalInsertion h a M = diagonalTensorFactor p a M.obj ≫
  outsideProjection p a M.obj T_W`. It records precisely that inverse
  projection of the first diagonal arrow has factor `id tensor push_i(delta)`,
  with `id tensor alpha_i` and the unit source retained. Inverse projections
  are defined by reversing the actual specified factors, using only the
  comparison node's isomorphism assertions.
- `TensorData.symmetry` is the imported signed derived tensor symmetry. Both
  outside-first projection and its inverse use that same symmetry. The
  line1/line2 identifications use the actual square, normalized root restriction,
  and canonical shift comparisons. The proof docstring retains the even-shift
  sign calculation and the frame-independent rank-one self-symmetry argument.

Recorded dependency declarations used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`, importing the recorded coefficient
  constructions from `Sheaf.NumberTheory.Padics.CoefficientExtension`.
- `Sheaf.Paper.SmoothPurityCoefficientTowers`,
  `AlgebraicGeometry.ProEtale.spCoefficientTowers`, `spCoefficientRings`,
  `spCoefficientReduction` and `spEllIdeal`.
- `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`,
  `AlgebraicGeometry.ProEtale.SpCoefficientTowersAbelian`,
  `sp_coefficient_towers_abelian` and the existing system realizations.
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`,
  `AlgebraicGeometry.Scheme.FixedEtaleOriginWitness`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`,
  `AlgebraicGeometry.ProjectiveSpace` and `ProjectiveLine`.
- `Sheaf.Paper.SmoothPurityTowerClasses`,
  `AlgebraicGeometry.ProEtale.TowerClasses`, with the recorded `SpTowerClasses`
  Chern, line, supported class and `Projective.trace` constructions.
- `Sheaf.Paper.TowerP1EtaleOriginComparisons`,
  `AlgebraicGeometry.ProEtale.SpTowerP1.towerP1EtaleOriginComparisons`,
  `EtaleOriginComparisons`, and its imported `Presentation`, `Maps`, `C`,
  `sourceUnitAt`, `exchangeSwap`, `eta`, `epsilon`, `left`, `rightRestricted`.
- `Sheaf.Paper.SemilinearDerivedSections`,
  `WeilConjectures.SemilinearSections.semilinearDerivedSections` and its
  actual system tensor, derived adjunction and normalized mate operations.

Stated proof modules are imported: RingedProjectionTensorComposition,
RingedExchangeTensorCoherence, ProjectionMateExact, ProEtaleTateTwistsOfUniverses,
TowerClassTwisting, Mathlib.Algebra.Homology.BifunctorShift and
Mathlib.CategoryTheory.Adjunction.Mates (also the basic adjunct/counit identity).
The kernel-scalar-normalization node has no Lean record; no module for that
unstated proof lemma is invented or imported. Its trace-base-change calculation
is retained in the proof plan, without assuming or asserting its scalar = 1 clause.

Edge cases checked before writing: empty S; M=0 or K=0; arbitrary non-Noetherian
and non-quasi-compact S; ramified coefficient extensions; ell=2; odd degrees of
M or K. All retain the canonical composites. Shifting a degree-zero line by 2
is bounded below at -2; root-site origins exist independently at each positive
level. The signed swap gives (-1)^(2j)=1 even for odd j. No nonzero coefficient,
nonempty scheme, chosen basis or separate universe equality is imposed. The
shared universe u may be enlarged to contain both E and S, as in the recorded
presentation; the small pro-etale site retains object universe u+1 and morphism
universe u.

Searches run:

- msearch.py leanfinder, “Factor the two projective line diagonal unit counit
  triangle composites as tensor with the diagonal trace scalar in the derived
  category of coefficient towers”: eight unrelated representation, condensed
  projectivity, coalgebra and Tor hits; none states this theorem.
- msearch.py loogle, `CategoryTheory.Adjunction,
  CategoryTheory.MonoidalCategory.tensorHom`: zero hits; tensorHom is not a
  known identifier. The actual tensor functor `.map (Prod.mkHom ...)` is used.
- msearch.py grep, `triangle.*scalar|scalar.*triangle|diagonal.*contraction`,
  CategoryTheory: zero hits.
- rg in lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json,
  `triangleFactorization|triangle_factorization|TriangleFactorization|
  lem-sp-tower-p1-triangle-factorization|scalarContraction|kernelScalar`: no
  existing statement. Further source inspection found the reusable `sourceUnitAt`
  and `exchangeSwap` helpers in TowerP1ProjectiveCoordinates, which are used.
- Exact-id grep in lean/WeilConjectures returned no declaration. A final name-clash
  rg for every new public helper returned only unrelated diagonalScalarExtension
  names in other namespaces.
- Related P1 adjunction and counit-scalar modules were read/searched: their
  statements give an adjunction or a different finite/rational scalar result,
  not the present pre-normalization identities of actual ordinary tower maps.

No statement correction, new definition node or STATEMENT-DISPUTED flag.

## Dependency modules

`lem-sp-tower-p1-etale-origin-comparisons` is repaired under §1(B), changing
only lean. Its existing interface supplies comparison isomorphisms on C+ but
cannot be specialized to its own shifted Tate line because the line's domain
membership is not exposed. `Sheaf.Paper.TowerP1ComparisonsWithLine` publicly
reexports it, extends the same Prop structure by `line_domain`, and states
`forall Presentation, exists Maps, EtaleOriginComparisonsWithLine`. Thus all
old geometry, isomorphism, boundedness, naturality and normalized level clauses
remain. Its only extra exposed fact is the degree-zero Tate line shifted by two
with its finite etale-root origins, already used in Steps 3--5 of the node's
proof. No domain restriction or replacement of its canonical maps is made.

## Second reading by Q13

The delivered section was a self-check by the author ("the maintainer supplies the independent
review"), so it did not count as a second reading (H11). The maintainer's reviewer wrote this
section, reading the item node, its eight stmt_deps and the side-live declarations
`SmoothPurityTowerP1Adjunction`, `TowerP1ProjectiveCoordinates` and
`TowerP1EtaleOriginComparisons`. The Lean is unchanged.

Node clauses, the Lean that renders each one, and the verdict:

- ℓ, E/Q_ℓ finite, O_E, and S with ℓ invertible. Lean: `l`, `[Fact l.Prime]`, `E`,
  `[FiniteDimensional (Padic l) E]`, `{S : Scheme.{u}}` and `hS`. Verdict: exact. There is no
  extra hypothesis. The shared universe u is the one of the recorded `Presentation`.
- A_T, the towers, D(Tow), and C⁺(T). Lean: `SpTowerShriek.D` and
  `C l E p.classes.base T`, i.e. ∃ lower bound plus `Origin` at every level n. Verdict: exact.
  This is the recorded domain.
- P, W, q, p_i, Δ. Lean: `ProjectiveLine S`, `diagonalSurface S` (the pullback of q along q),
  `diagonalImmersion S` (`pullback.diagonal`), and `projectiveLineDiagonalProjection S a`.
  `a = false` is `fst`, which is p₁; `a = true` is `snd`, which is p₂. Verdict: exact.
- The twist, δ_•, t_q, F and G. Lean: `line … ⟦2⟧`, `p.delta`, `p.trace`, `p.F` = Rq_*, and
  `p.G` = q^*(−)⊗A_P(1)[2]. Verdict: exact.
- t_i. Lean: `projectionTrace a`. For p₁: `push_fst(line2Iso⁻¹) ≫ (exchangeSwap at T)⁻¹ ≫
  q^*(t_q) ≫ qUnitIso`. For p₂: `push_snd(line1Iso⁻¹) ≫ (exchange at T)⁻¹ ≫ q^*(t_q) ≫
  qUnitIso`. Here `exchangeSwap` is v_T : LRT → U b T, and `exchange` is
  u_T : LRT → V a T. So t₁v_T = Lt_q and t₂u_T = Lt_q, up to the specified line comparisons.
  This is the base-changed splitting trace of the parent's step 2 and of the
  kernel-scalar-normalization clause. Verdict: accepted, and the report discloses it.
  TowerClasses records no splitting for P¹_P → P. The construction is canonical: the inverse of
  an exchange that the comparisons node asserts invertible. It is not an arbitrary map.
  Advisory A1 below covers this.
- α_i and c_i. Lean: α_i = `sourceUnitAt a` at the unit; it is the p_i unit, then the Δ unit,
  then the diagonalPull iso for p_iΔ=1. Lean: `diagonalScalar a` = α_i ≫ p_{i*}(δ) ≫ t_i.
  Verdict: exact.
- η and ε. Lean: `eta`/`epsilon` of the recorded comparisons node, unchanged. η: source unit →
  inverse diagonal projection with p₁^*M → δ⊗1 → braid → line2Iso → inverse p₂ projection →
  inverse exchange. ε: braid → projectionQ⁻¹ → braid → 1⊗t_q → unitor. Verdict: these are the
  node's composites.
- First identity, ε_{FM}∘F(η_M) = F(1_M⊗c₁). Lean: conjunct 1. In Lean's diagrammatic order
  this is `F.map (eta M) ≫ epsilon (left.obj M)`. The right-hand side
  `scalarContraction M c₁` = ρ⁻¹ ≫ (1⊗c₁) ≫ ρ uses the unit identification M⊗A_P ≃ M.
  Verdict: exact.
- Second identity, G(ε_K)∘η_{GK} = 1_{GK}⊗c₂. Lean: conjunct 2, the same check. Verdict: exact.
- The expanded first composite. Lean: conjunct 3 with `expandedContraction false M`, which is
  the p₁ word: α source, inverse diagonal projection, δ⊗1, outside-first inverse projection,
  1⊗t₁, unitor. Verdict: exact. F of it is the R(qp₁) word written in nested Rq_*Rp_{1*}
  coordinates.
- The second equality with M = GK, the identifications p₁^*M ≃ p₂^*M, and contraction by t₂.
  Lean: conjunct 4, the p₂ word on GK. Verdict: exact.
- "Its first arrow has the factor 1_M⊗Rp_{1*}(δ_•), including α₁ on its source", and the
  analogue for p₂. Lean: conjuncts 5 and 6, `diagonalInsertion = diagonalTensorFactor ≫
  outsideProjection`. Verdict: exact.
- Consistency check. Inside each word, `outsideProjection ≫ outsideLineProjectionInverse` is
  the identity: the braid, the projection and the braid cancel. So conjuncts 3/4 combined with
  5/6 give 1/2. The conjuncts are not inconsistent.
- No assertion c_i = 1 and no F ⊣ G. Verdict: none occurs as a hypothesis or as a conclusion.

Hypotheses:

- `d : Maps l E p`. Its only data field, `projectionQ`, is pinned by `projectionQ_eq`.
- `h : EtaleOriginComparisonsWithLine p d`. This is the comparisons theorem's own conclusion
  (∀ p ∃ d). The hypothesis is therefore no stronger than the cited node.

Dependency module (§1(B), H13):

- `line_domain` says that A_P(1)[2] lies in C⁺(P). The node implies this: G(A_S) ≅ A_P(1)[2],
  and A_S lies in C⁺(S). It is needed to invert v_T and u_T at T.
- The old structure is kept whole through `extends`. Only the `lean` field of the dependency
  node changed, and it has a note.
- The only stmt_dep citers are this item and lem-sp-tower-p1-single-level-triangles, which has
  no Lean yet. The new module publicly imports the old one.

Edge cases:

- Empty S, M = 0 or K = 0, ℓ = 2, odd degrees: none of them is excluded. The sign of the even
  shift and the self-symmetry of the rank-one line are covered by the proof docstring (step 6).

Records:

- The item and the dependency `lean.statement` are verbatim.
- Every listed declaration exists, no line exceeds 100 characters, and every proof is `sorry`.
  The definitions are composites of recorded maps, not hollow.
- The docstrings carry the source and blueprint id, and the main docstring has the nine steps.
- A grep of side-live finds no duplicate of the new helper names.

Advisories:

- A1. t_i is the base-changed t_q by construction. A later Lean statement of
  lem-sp-tower-p1-kernel-scalar-normalization must state its trace-base-change clause against
  an independently built P¹_P → P splitting trace; otherwise that clause would be definitional.
- A2. `sourceUnitAt` and `exchangeSwap` are owned by def-sp-p1-projective-coordinates, which
  is not in stmt_deps. `Presentation`, `Maps`, `eta` and `epsilon` are owned by the parent
  det-sp-tower-p1-adjunction. Citing the parent would make a cycle, so these are reached only
  through the cited comparisons node.
- A3. The dependency record now lists only the new module's two declarations.
  `EtaleOriginComparisons`, `etaTransformation` and the other old declarations remain in the
  old module, which is imported publicly.
