## Worker report

The module `Sheaf.Paper.PurSequenceKFlatComparisonShifts` states
`WeilConjectures.purSequenceKFlatComparisonShifts`. Its proof is `sorry`; no mathematics
is proved in this stage. The other six declarations are fully written records or
functions spelling out the comparison equations. No definition contains `sorry`.
The natural-language statement, proof, and proof dependencies are unchanged.

Hypotheses and objects, clause by clause:

- The finite-field datum is `F : FiniteFieldDatum.{t}`. Its fixed algebraic closure
  is `F.k`; the characteristic exclusion is `hl : l ≠ F.p`.
- The prime coefficient is `l : ℕ` with `[Fact l.Prime]`. The finite extension is
  `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`,
  `[FiniteDimensional ℚ_[l] E]`. The existing coefficient-extension construction
  fixes the valuation ring, uniformizer and all actual quotient rings.
- `W : Scheme.{t}`, `[W.Over (Spec (.of F.k))]`,
  `[LocallyOfFiniteType (W ↘ Spec (.of F.k))]` and
  `[QuasiCompact (W ↘ Spec (.of F.k))]` express precisely finite type over k.
- The site is the existing `Scheme.ProEt.topology W`, with object universe t+1,
  morphism universe t and coefficient/module universe max u (t+1). These remain
  independent: no equality of site and coefficient universes is imposed.
- The completed ring is `completedIntegralCommRingSheafUnrestricted l E W`;
  the sequence ring and strict module category are the recorded
  `coefficientSequenceCommRingSheaf` and `coefficientSequenceModules`. Lean level n
  is the source's positive exponent n+1, so the first quotient is included.
- `DerivedCategory (scalarReductionSource l E W)` and
  `coefficientSequenceDerived l E W` are the existing ordinary unbounded derived
  categories. The shifts are the standard integer cochain shifts.
- `S : CoefficientDerivedSystemCalculus l E W` and
  `hS : CoefficientDerivedSystemCoherence l E W S` are the supplied calculus and
  its coherence. Its reduction is `S.reduction`; the recorded total limit is
  `coefficientSequenceLimit l E W`. The theorem does not change the limit.
- `O : PurSequenceOrdinaryAdjoints l E W` is the existing presentation of the
  supplied p and its ordinary module pullback. Its `p`, `constant`, and `quotient`
  fields specify exactly the constant-system inverse image and completion
  projections cA→B. Its ordinary adjunction, `tensor`, `tensor_transition`, and
  `transpose` characterize the canonical sheafified scalar-extension model.
  This is a presentation of the projection in the node, not a new arbitrary
  pullback hypothesis. No derived pair or comparison is assumed in O.

Conclusion, clause by clause:

- `PurSequenceKFlatComparison.L`, `.ε`, and `.universal` give the universal
  left-derived pullback, with its natural counit. `.α : L ≅ S.reduction` is the
  natural isomorphism on all of D(A). `.comparison` is the universal comparison
  of the identity ordinary model; `.reductionUniversal` and `.unique` fix the
  normalization, rather than allowing an unrelated natural isomorphism.
- `.representative` gives the same strict complex `O.pullback` applied termwise
  to each K-flat Q with flat terms. `CoefficientReductionPresentation` specifies
  its canonical finite-evaluation square and actual quotient-transition square.
  The chain comparison is `NatIso.mapHomologicalComplex (O.tensor n) (.up ℤ)`:
  every degree is the existing ordinary scalar extension, with no independent
  finite resolution or transition choice.
- `PurSequenceKFlatResolutionComparison.pullback` and `.reduction` apply to every
  complex P and every supplied quasi-isomorphism q:Q→P with Q K-flat and flat
  terms. `.pullback_formula` and `.reduction_formula` are exactly inverse L(Qq)
  followed by the counit, and inverse reduction(Qq) followed by its counit.
  `.comparison` is a_q = alpha_P followed by b_q.
- `.maps` gives both squares for v:Q→Q' and h:P→P' with v q'=q h. It does not
  require v or h to be quasi-isomorphisms. `.same_comparison` identifies the
  comparisons between two representatives for both functors; `.three` is their
  three-resolution cocycle. The reduction cocycle follows from that equality.
- `.finite_evaluation` spells out b_q after evaluation: S's finite comparison,
  inverse of derived extension applied to Qq, then the canonical K-flat finite
  model. Together with `.comparison` this is also the finite comparison for
  a_q. The transition formulas remain those in the representative presentation.
- The theorem's second conjunct says for every such q and every r:ℤ that Q[r]
  remains K-flat, all its terms remain flat, and q[r] is a quasi-isomorphism.
  Neither P nor Q is assumed bounded or complete.
- `purSequenceTensorRight` is just currying the recorded `coefficientTotalTensor`;
  it defines no second tensor. `purSequenceShiftSection` is the existing
  `CochainComplex.shiftFunctorObjXIso` on underlying sections.
- The final conjunct supplies a coherent `CommShift ℤ` structure for tensoring
  with each arbitrary T. `PurSequenceTensorShiftFormula` says its degree-k map
  on the actual (p,q) pure-tensor generator is `(r*p).negOnePow` times the same
  generator in degree k+r. This is exactly multiplication by (-1)^(rp) on
  T^p tensor Q^(q+r), including the reindexing isomorphisms on both sides.
  Being an isomorphism of cochain complexes includes the differential equation.
- `CommShift` gives naturality in Q. The final displayed equation gives naturality
  also for every chain map T→T'. Zero and addition are the explicit axioms of
  `Functor.CommShift`; addition with s=-r supplies inverse-shift coherence.
- `PurSequenceKFlatShiftComparison.left_shift`, `.reduction_shift`, and
  `.finite_shift` are the specified coherent derived shifts. `.comparison` is
  alpha's shift square on every derived input, hence on every derived morphism.
  `.left_resolution` and `.finite_resolution` fix these structures on exactly
  the shifted representative, not just after forgetting it.
- `.left_terms` and `.finite_terms` identify the ordinary shift components with
  the identity on the reindexed pullback/scalar-extension modules. Under O.tensor
  these are Q^(i+r) tensor B_n. `.left_differential` and `.finite_differential`
  explicitly give r.negOnePow times d_Q tensor 1. `.quotient_shifts` is the
  chain-level commuting square for every actual quotient transition n≤m,
  including composite and identity transitions. The natural shift isomorphisms
  themselves give the squares on maps of resolutions.
- There is no flatness assumption on the completion projections, no boundedness,
  no completeness of P, and no normalized-system hypothesis.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and its
  inherited field/algebra instances, used for the global base.
- `Sheaf.Paper.CoefficientRingedSequenceSite`: `coefficientSequenceCommRingSheaf`,
  `coefficientSequenceModules`, `coefficientSequenceDerived`,
  `coefficientSequenceEvaluation`, `coefficientSequenceDerivedEvaluation`, and
  the exact ordinary quotient-system transitions.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`, exactness of the existing sheaf tensor functor.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`, tested against every acyclic
  complex using the existing sheafified total tensor.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor` and
  `mapBifunctorShift₂Iso`, whose generator formula gives the expected sign.
- `Sheaf.Paper.SequenceSiteCompletionProjection`:
  `CategoryTheory.RingedToposMorphismOfUniverses`, with independent site and
  coefficient sizes, as used by the recorded ordinary projection presentation.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `DerivedCategory.Q`; `Functor.IsLeftDerivedFunctor` for the universal pair.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `CoefficientDerivedSystemCalculus`, `CoefficientDerivedSystemCoherence`,
  `CoefficientReductionPresentation`, `coefficientFiniteReductionModel`,
  and `coefficientOrdinaryQuotient` with their full representative/transition
  normalizations.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings` publicly exports
  `SheafOfModules.DerivedChangeOfRingsCochainModel`, retaining the generic sheaf
  interface. The specialized finite extension and counit already in the calculus
  are used, rather than constructing another extension functor.
- Two already landed definition nodes are added to stmt_deps:
  `def-pur-sequence-adjoint-resolution-data` supplies `PurSequenceOrdinaryAdjoints`
  and `purSequenceShiftIso` from `Sheaf.Paper.PurSequenceAdjointResolutionData`;
  `def-coef-ringed-tensor-hom-model` supplies `coefficientTotalTensor` and
  `coefficientTensorGenerator` from `Sheaf.Paper.CoefficientRingedTensorHomModel`.
  Neither addition creates a dependency cycle.
- Proof-only imports include the independent-universe ringed derived pullback
  theorem and the independent-coefficient K-flat resolution theorem.
  `lem-sp-strict-coefficient-tensor-descent` has no Lean record on the read base;
  it is a proof dependency only, so no unrecorded module is imported for it.

Edge cases checked against the formulas: r=0 gives identity; r=1 and p odd gives
minus the tensor generator; negative r has the same parity convention; r+s and
s=-r give the expected products of signs. The zero complex and empty W make
all section equations the unique zero maps. n=0 is exponent 1. m=n makes the
transition the identity. Arbitrarily unbounded T,Q are permitted because the
tensor is the direct-sum total, not a product total. Non-flat quotient maps and
non-normalized input systems remain allowed. Two unrelated resolutions are
compared through their canonical derived isomorphisms, without requiring a
chain map between them; a third gives the cocycle.

Searches actually made:

- msearch LeanFinder: “Universal left derived comparison between quotient
  sequence projection pullback and strict K-flat reduction, with coherent cochain
  shifts”. Eight generic derived-localization/fraction candidates returned,
  including `mapDerivedCategoryFactors`, `left_fac`, `right_fac`; no exact match.
- msearch Loogle: `CochainComplex.mapBifunctorShift₂Iso,
  CategoryTheory.Functor.leftDerivedUnique`. Zero hits.
- msearch grep in Mathlib/Algebra/Homology:
  `mapBifunctorShift|leftDerivedUnique|CommShift`. Returned the canonical
  bifunctor shifts and generic additive-functor shifts. Their full signatures and
  generator formulas were read; they supply infrastructure, not this comparison.
- msearch LeanSearch: “A left derived pullback along a quotient ringed sequence
  projection agrees with simultaneous reduction and its coherent cochain shifts”.
  Eight generic left-derived/projective-resolution/fraction results returned;
  none states the strict-system comparison.
- rg in the upstream and project source: the exact node id has no declaration;
  `KFlatComparison|kflatComparison|sequenceKFlat|SequenceKFlat` finds only distinct
  normalized DVR reduction and constant-scalar comparison interfaces.
  Broader sequence/comparison and K-flat searches found the parent
  `PurSequenceAdjointResolutionShifts` and its data. Its left part is similar,
  but it does not state this theorem's explicit tensor-shift generator formula.
  Its existing ordinary-projection and shift-reading helpers are reused.
- The old example CompactObject module is withdrawn on the read base. Its node
  points to `WeilConjectures.CategoryTheory.CompactObject`; that live module and
  its source/docstring conventions were read instead.

Validation: scompile.py compiled this module in sandbox and library positions.
The first compile reported four unused structure-parameter names; these were
renamed with underscores. The second compile is clean (21.7 s sandbox,
17.1 s library). The prescribed deliver2.py --no-push dry run also passed preflight and
compilation (dry-run commit b09eaef651d).

No statement correction, disputed statement, new node, or dependency-module
repair was needed. The worker uses only the designated sandbox; shared sources
are read-only.

## Second reading by Q155

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
