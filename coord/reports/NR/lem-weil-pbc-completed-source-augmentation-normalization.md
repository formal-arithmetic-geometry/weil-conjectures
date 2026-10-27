## Worker report

The module `Sheaf.Paper.CompletedSourceAugmentationNormalization` states
`AlgebraicGeometry.Scheme.completedSourceAugmentationNormalization`, with one `sorry`.
It states all four equations of the node as a conjunction, using the actual imported
strict-tower constructions. There are no new definitions, dependency modules, or
statement corrections. The item's existing fields are preserved and only `lean` is added.

The previous worker's stale-dispatch diagnosis concerned the stage-1 split. The live
node has `status: split` and an NQ stage-1 PASS, but has no `lean` record. That is the
stage-2 task specified by this dispatch. There is no released repair note for this item.

Hypotheses and objects, clause by clause:

- The commutative ring is `{A : Type (t + 1)} [CommRing A]`. The parameter
  `d : AdicCoefficientDatum A` contains `ideal`, `noetherian`, `finitelyGenerated`,
  `quotientTorsion`, `quotientPerfect`, and `quotientFinite`. Thus it contains exactly
  the Noetherian, finitely generated ideal, additive torsion residue, finite quotient,
  and perfect quotient hypotheses. No completeness of the coefficient ring is added.
  Natural index `n` denotes positive quotient exponent `n + 1`, including exponent one.
- `{X' X Y' Y : Scheme.{t}}` and the four explicitly typed morphisms introduce every
  corner. `sq : ChosenCartesianSquare g' f' f g` includes square commutativity, the
  chosen pullback isomorphism and its projection equations. `[IsProper f]` is precisely
  the properness hypothesis.
- `d.completedRing T` is the existing inverse limit of the function coefficient
  sheaves. `d.derived T` is its ordinary unbounded module derived category.
  `completedReductionTower T d` takes values in the derived category of strict
  towers, not towers in a derived category. The pro-etale object universe remains
  `t + 1`, with morphism universe `t`; no universe equality is imposed.
- `K : d.derived X` and `(d.push f).obj K` are K and C. `_hK` and `_hC` explicitly
  assume `d.TowerComplete` for each. This predicate is invertibility of the specified
  quotient completion unit, using the published equivalence with intrinsic derived
  completeness. Neither of these hypotheses is silently omitted.
- `_W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
  ((d.reduction X n).obj K)` retains the bounded-below etale antecedent and its
  actual comparison isomorphism at each quotient. The witness's `complex` and `iso`
  fields include the canonical function-to-constant coefficient transport. The
  transitions are the fixed strict quotient transitions, not newly chosen transitions
  between antecedents. As in the recorded strict-normalization and base-change-map
  interfaces, no common lower bound or additional cross-level witness choice is imposed.
- E0 is `(d.pull g').obj K`; M is `(d.pull g).obj ((d.push f).obj K)`;
  N is `(d.push f').obj ((d.pull g').obj K)`. The arrow e is
  `(d.integralExchange sq).app K`, the actual general ringed exchange specialized
  to the coherent completed coefficient isomorphisms.
- R at T is `completedReductionTower T d`; Delta is `d.derivedConstantTower T`;
  the quotient augmentation i is `(completedReductionAugmentation d T).app V`;
  F is `completedRlim T (d.completedRing T)`; lambda is
  `(d.constantRlimAdjunction T).unit.app V`. Their prescribed composite u is exactly
  `d.completionUnit T V`, by its definition. These are reused, not redefined.
- S is `(d.completedPull g).obj ((d.push f).obj K)`, definitionally F of the pulled
  reduction tower. Gamma is `d.ordinaryToCompleted g ((d.push f).obj K)`. This
  construction uses the inverse constant/pullback comparison followed by the pulled
  quotient augmentation under F, preceded by lambda, exactly as specified.
- Tau is `(d.reductionTowerPullbackIso g).app ((d.push f).obj K)`; j is its hom
  mapped by F. This is the existing K-flat-normalized strict comparison, not an
  arbitrary isomorphism between the two tower objects.
- B and D are the targets of `exchangeRealizationH` and `exchangeRealizationHPrime`,
  respectively, definitionally corners 1 and 3 of `d.fourTowerCorners`. The actual
  strict exchange is `d.towerV' sq K`. H and H prime are the named imported
  projection-formula realizations, including the specified pullback/reduction factors.
- The first conjunct is `gamma ≫ F.map tau.hom = d.completionUnit Y' M`.
  Since `≫` composes left to right, this is precisely `j gamma = u_M`.
- The second conjunct is `F.map towerH.hom = F.map tau.hom ≫ F.map H.hom`.
  The left side is the source comparison s of `completedBaseChangeMap`: the
  preliminary identification of S with F(A) is definitional. This is `s = F(H) j`.
- The third conjunct is `u_M ≫ F.map (R.map e) = e ≫ u_N`, precisely
  `F(R(e)) u_M = u_N e`. It concerns the specified completion units.
- The fourth conjunct is `gamma ≫ F.map towerH.hom ≫ F.map towerV' =
  e ≫ u_N ≫ F.map HPrime.hom`, precisely `F(v') s gamma = F(H') u_N e`.
  No faithfulness of derived evaluation or invertibility of e, v', or gamma is assumed.
  All four clauses are equalities of morphisms in the ordinary derived category.

Dependency declarations read and used:

- `Sheaf.Paper.AdicCoefficientDatum`: `AdicCoefficientDatum`,
  `completedReductionTower`, its module/tower/derived-category constructions, and
  `AdicCoefficientDatum.derived`, `.reduction`, `.completedRing`. The inherited datum
  fields were read in `CompleteCoefficientDatum` and `CompletedAdicCoefficientDatum`.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: `AlgebraicGeometry.ChosenCartesianSquare`.
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`: the recorded fixed-scalar pair
  is publicly retained alongside `RingedEtaleOriginWitness.FiniteEtaleOriginWitness`
  (the latter's full name is `AlgebraicGeometry.Scheme.FiniteEtaleOriginWitness`).
  The finite ringed presentation is the one already used by the two tower dependencies.
- `Sheaf.Paper.CondensedAmbientExchange`: its public imports retain the general
  `AlgebraicGeometry.Scheme.proEtaleAmbientRingedExchange`, defined in
  `Sheaf.AlgebraicGeometry.ProEtaleAmbientRingedExchange`. The existing abbreviation
  `AdicCoefficientDatum.integralExchange` in `Sheaf.Paper.FourCorners` is exactly its
  specialization to the four completed coefficient sheaves and their coherence.
  The condensed-only specialization is not substituted for this general construction.
- `Sheaf.Paper.CompletedRlimFunctor`: `completedRlim`, `completedRlim_computation`.
- `Sheaf.Paper.CompletedBaseChangeMap`: `AdicCoefficientDatum.completedBaseChangeMap`
  and `.completedExchange`, whose first factor is F of `.towerH`.
- `Sheaf.Paper.PbcQbarCompletedPullback`: publicly retains the strict-tower and adic
  interfaces of this node, including `Sheaf.Paper.CompletedPullback` declarations
  `AdicCoefficientDatum.completedPull`, `.ordinaryToCompleted`, `.completionUnit`,
  `.TowerComplete`, `.constantRlimAdjunction`, and `completedReductionAugmentation`.
  Its Qbar-specific declaration is not used for general A. These public reexports
  compiled together without ambiguity, so no dependency rebinding was needed.
- `Sheaf.Paper.ReductionPullbackDerivedTower`:
  `CategoryTheory.StrictReduction.reductionPullbackDerivedTower`, with the
  representative normalization and strict augmentation equation. The adic instance
  already supplied in `Sheaf.Paper.CompletedDirectImageLimits` is
  `AdicCoefficientDatum.reductionTowerPullbackIso`; its unique normalized
  representative formula was inspected.
- `Sheaf.Paper.StrictTowerExchangeMateNormalization`: `exchangeRealizationH`,
  `exchangeRealizationHPrime`, `strictTowerExchangeMateNormalization` and the actual
  strict exchange `AdicCoefficientDatum.towerV'` retained from `CompletedTowerCorners`.
- Proof-only import `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`:
  `proEtale_profinite_coefficient_inverse_image`. The other stated proof
  dependencies are already public statement imports, so are not imported twice.

Source inspection: `literature/stacks-project/sites-cohomology.tex`,
`remark-base-change` (Tag 07A7), constructs e by the derived pullback square followed
by the counit and adjunction. The strict-augmentation refinement is the five-step
proof of this DAG node; it is not attributed as an extra assertion of Stacks.
The theorem docstring carries all five steps with their named dependencies.

Edge cases checked mathematically before writing: K zero (all equations are equations
of zero morphisms); empty schemes (the same canonical site and tower functors apply);
g or f identity (the canonical constant/pullback comparisons and their units remain
in the formulas); zero coefficient ring or unit ideal (all quotient and completed
module categories are zero); zero ideal when permitted by the datum (the strict
quotient tower is constant); the first quotient exponent one; arbitrary unbounded K
and individually bounded-below witnesses with no uniform lower bound. None is excluded
by a binder, nonemptiness assumption, nonzero-ring hypothesis or index-universe choice.

Searches for an existing complete statement:

- `msearch.py leanfinder`, query `Derived pullback reduction strict tower comparison
  preserves quotient augmentation and the source completion unit of base change`:
  eight hits, including `RingHom.IsStableUnderBaseChange.pullback_fst_appTop`,
  `KaehlerDifferential.isBaseChange`, and `Limits.pullbackComparison_comp_fst`.
  These concern ordinary algebra or categorical pullbacks, not these four strict
  completed-coefficient source-augmentation equations.
- `msearch.py loogle`, query `"completionUnit", "naturality"`: zero hits.
- `msearch.py grep`, query `completedSourceAugmentation|ordinaryToCompleted.*reduction|
  augmentation.*normalization`: zero Mathlib hits.
- `msearch.py leansearch`, query `Naturality of the completion unit and preservation
  of the source quotient augmentation by strict derived tower base change`: eight
  uniform-space completion hits, including `UniformSpaceCat.completionHom` and
  `UniformSpace.Completion.coeRingHom`; none is the derived-tower statement.
- `rg` in Mathlib's `CategoryTheory` for `strictTower|augmentation.*completion`:
  no match. Project and upstream searches for `completedSourceAugmentation` and
  the exact node id: no existing declaration of this node.
- Concept searches in `lean/Sheaf/Paper/Completed*.lean` found the reusable public
  definitions above, the private lemma `ordinaryToCompleted_reduction` in
  `CompletedExchangeUnit`, and the public theorem `completedExchange_unit`. The
  private lemma gives only the first clause; the public theorem concerns the entire
  base-change composite after the inverse direct-image/Rlim comparison and does not
  state this node's four-clause normalization. Neither is an exact existing match.

Validation: `scompile.py NR lem-weil-pbc-completed-source-augmentation-normalization`
compiled the delivered module in sandbox and library modes against the published
server library, both clean (2.2 seconds each). All variables and universes are explicit,
`autoImplicit` is disabled, and every Lean line has at most 100 characters.
There is no disputed statement or node fault. The original dependency records are
usable through their retained general interfaces and remain unchanged.

## Second reading by NR

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
