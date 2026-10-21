## Worker report

Item: lem-pur-normalized-tensor-constraint-transport. New module:
`Sheaf.Paper.NormalizedTensorConstraintTransport`, namespace
`WeilConjectures.NormalizedTensorTransport`.
The sole postponed theorem is `normalizedTensorConstraintTransport`; its proof is
`sorry`. All other declarations contain actual data. The theorem docstring carries
all eleven proof steps, including the independent quotient-associator roof.
No mathematical statement correction, dependency module, or new DAG node was needed.
The returned packet's statement-dependency ownership is repaired below.

### Hypotheses and context

- Prime ell: `(l : ℕ) [Fact l.Prime]`.
- Finite coefficient field: `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. The recorded Padic coefficient construction chooses
  its integers and uniformizer; all finite coefficients and quotient maps are the
  existing ones. No new ring or choice of uniformizer is introduced.
- Arbitrary scheme with ell invertible: `(W : Scheme.{t})` and
  `_hl : ∀ w : W, IsUnit (l : W.presheaf.stalk w)`.
- The finite rings B_n, completed R_W, ordinary unbounded derived system category,
  actual quotient transitions, reduction and total limit are the existing
  `coefficientSequenceDerived l E W`, `coefficientSequenceDerivedTransition`,
  `S.reduction`, `S.adjunction`, and `coefficientSequenceLimit l E W`.
  Here `S : CoefficientDerivedSystemReduction l E W`; its reductionModel,
  reductionEvaluation, counit_projection and unit_projection fix their models and
  scalar-extension adjunction normalizations, rather than leaving arbitrary functors.
- The tensor is `S.systemClosed.tensor`, normalized on simultaneous K-flat models
  by `S.systemTensorModel`. `σ` and `C : RingedDerivedTensorCoherence ...` present its
  canonical symmetry, associator and action unitors with the already recorded
  pure-tensor representative equations. They are the canonical tensor-model data
  of the node, not additional flatness, boundedness or finiteness hypotheses on inputs.
- `r` is the primitive tensor realization of
  lem-pur-completed-primitive-counit-comparison. The theorem binds
  `ρ : PrimitiveCounit.RoosRealization l E W` and
  `_hr : PrimitiveCounit.TensorModel l E W S ρ r`. Thus r is required to realize
  the actual strict quotient tensor towers through the prescribed Roos comparison.
  An arbitrary natural isomorphism would not meet this hypothesis.
- `(A N H : coefficientSequenceDerived l E W)` are arbitrary, with the three
  `IsNormalizedCoefficientSequence` hypotheses. This predicate uses invertibility
  of the actual transition adjuncts under the finite coefficient adjunctions.
  No canonical-unit-transition hypothesis replaces these arbitrary normalized inputs.
- The four final typeclass hypotheses are precisely invertibility of beta_P,
  beta_Q, gamma_P and gamma_Q, as the node explicitly assumes in its last paragraph.
  The inner contraction needed to form the quotient associator is supplied in the
  conclusion as `∃ _i : IsIso (contraction ... (L N) (L H))`; it is not assumed.

### Clause-by-clause rendering

1. The finite expression grammar is imported from
   `Sheaf.Paper.CompletedOperationExpressions`. `Kind.expressions W` gives precisely
   the four pairs, with inputs 0=A, 1=N, 2=H at the single location W. The syntax is
   reused, not redeclared. The theorem's four pairs treat these named systems as
   input leaves, exactly as the node says. Arbitrary pullback subexpressions in the
   preceding context are not an extra constraint pair in this lemma: once such a
   system is supplied as A, N or H it is simply a named normalized input here.
2. `unit` is the recorded ringed sequence coefficient sheaf in degree zero. It
   contains all actual quotient transitions. `systemSource`, `systemTarget` and
   `systemMap` render the four displayed pairs and arrows. Reassociation is the
   monoidal associator; leftAction/rightAction use C.unitIso with the corresponding
   action unitor; symmetry is `σ.braiding A N`.
3. The displayed total-complex formulas are the existing
   `C.associator_model`, `C.leftUnitor_model`, `C.rightUnitor_model` and
   `C.symmetry_model`. These quantify over actual K-flat complexes of modules on
   the sequence site and their sheafified homogeneous generators. In particular
   the symmetry coefficient is `(p * q).negOnePow`, and both actions multiply the
   degree-zero ring section. Using these recorded representative equations avoids
   asserting a second, unrelated constraint structure. All such cochain maps are
   maps on the sequence site, so they retain the horizontal quotient equations
   before localization, including on flat-term K-flat representatives.
4. The scalar-extension compatibility is that of the recorded
   `CategoryTheory.CochainPullback.cochainPullbackTensorCoherence`, imported for
   proof step 3. Applying naturality to the arbitrary input adjuncts gives the
   transition square. The last universally quantified clause explicitly retains
   the actual semilinear transition equation for every `h : n ≤ m`, not just
   consecutive or strictly decreasing levels. Transposing that square under the
   recorded coefficient adjunction gives the stated adjunct square.
5. `completedSource` and `completedTarget` expand K_P and K_Q using the actual
   `integralCompletedTensor`, including nested parentheses and the unit L(U).
   `betaSource` and `betaTarget` expand the node's recursion using exactly
   `PrimitiveCounit.tensorBeta`; the two source associator comparisons are composed
   after tensoring the inner beta with the identity. Unit and input beta are
   identities. No recursion comparison is supplied arbitrarily.
6. `gammaSource` and `gammaTarget` are literally `S.reduction.map beta` followed
   by the counit at the corresponding whole system, as specified.
7. `contraction K J` is literally `R(r_(K,J))` followed by
   `e_(T(RK,RJ))`. `quotientAssociator` is the independently defined roof
   `r_left >> L(T(d_AN,1) >> a_0 >> T(1,d_NH^-1)) >> r_right^-1`.
   `quotientMap` uses this roof for reassociation, `r >> L(sigma_0) >> r^-1`
   for symmetry, and `r >> L(T(e_U,e_A) >> lambda)` or the right counterpart
   for actions. These are the node's actual quotient constructions, defined
   before the theorem and without using beta-conjugation as their definition.
8. The first equality of the theorem is exactly
   `quotientMap = betaSource >> L.map systemMap.hom >> inv betaTarget`.
9. The second equality is exactly
   `R.map quotientMap >> gammaTarget = gammaSource >> systemMap.hom`.
   It is an equality in the ordinary derived category of whole systems.
10. The third equality spells out the whole-system counit naturality used in the
    node: `R.map (L.map a) >> e_target = e_source >> a`.
11. The last equality is the actual quotient-transition square for systemMap at
    every m>=n, including identities. The gamma equality and every factor in it
    are whole-system maps, so their transition equations hold simultaneously as
    well; equality is never inferred from faithfulness of separate evaluations.
12. The arrow has the natural canonical total-complex normalization because its
    system factors are the monoidal constraints, whose data include naturality,
    and its completed factors are natural r, counit and tensor. Inverting the
    isomorphic inner contraction retains that naturality. No scalar rescaling of
    the unit is permitted: the unit factors are the actual counit e_U and the
    action maps fixed by C. `S.counit_projection` fixes e_U as the adjunct of the
    actual limit projection, hence z tensor b maps to b p_n(z).

### Dependency declarations used and read

- def-weil-l-adic-coefficient-extension:
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`, importing the original integers,
  uniformizer and finite coefficient quotients.
- def-weil-scheme-morphism-properties is explicitly a convention node with no
  declaration. The module uses `AlgebraicGeometry.Scheme` and its presheaf stalks.
- def-weil-completed-integral-coefficients:
  `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`,
  `integralConstantToCompletionOfUniverses` and its imported completed coefficient
  sheaves. The constant ring is not substituted for its completion.
- lem-coef-semilinear-derived-sections:
  `Sheaf.Paper.SemilinearDerivedSections`,
  `WeilConjectures.SemilinearSections.semilinearDerivedSections` and its recorded
  whole-system calculus. No category of towers of independently derived objects
  replaces the sequence-site module category.
- def-coef-normalized-dvr-tower:
  `Sheaf.Paper.NormalizedDVRTower`, `NormalizedDVRTower`, `normalizedDVRRes` and
  the actual finite quotient maps. The modern whole-system predicate is the
  already available `IsNormalizedCoefficientSequence` from the sequence-site
  interface used by the evaluation calculus. We do not add its older auxiliary
  finite-field parameter to arbitrary W.
- def-weil-integral-reduction-tower:
  `Sheaf.Paper.IntegralReductionTowerCanonical`, `canonicalIntegralReductionTower`,
  with its actual quotient maps and reduction units, as retained in S.reductionModel.
- lem-weil-pbc-ringed-strict-tower-homotopy-limit:
  `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`,
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`, underlying
  the recorded total limit; object and morphism universes stay independent.
- lem-coef-derived-system-evaluation-calculus:
  `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`,
  `CoefficientDerivedSystemReduction`, its counit and tensor models;
  `coefficientDerivedSystemEvaluationCalculus` supplies the canonical context.
- lem-coef-normalized-dvr-effectivity:
  `Sheaf.Paper.NormalizedDVREffectivity`, `normalizedDVRTower_effectivity`, used by
  the proof plan for the canonical counit, not an arbitrary object isomorphism.
- def-pur-integral-derived-operations:
  `Sheaf.Paper.IntegralDerivedOperationsOnSlices` and its imported
  `integralCompletedTensor`; the global quotient/Roos completed tensor is the
  exact one used by PrimitiveCounit.TensorModel, not a fresh completed tensor.
- def-pur-completed-operation-expressions:
  `Sheaf.Paper.CompletedOperationExpressions`, `CompletedOperations.Expression`.
- lem-pur-cochain-pullback-tensor-coherence:
  `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`,
  `CategoryTheory.CochainPullback.cochainPullbackTensorCoherence`.
- def-pc-kflat-complex:
  `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`,
  `CochainComplex.IsKFlatIndependentCoefficients`, in the existing TensorModel and C.
- def-pc-flat-sheaf-modules:
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`, `SheafOfModules.IsFlatOnSite`,
  in the primitive good-representative model.
- lem-pur-completed-primitive-counit-comparison:
  `Sheaf.Paper.CompletedPrimitiveCounitComparison`,
  `PrimitiveCounit.tensorBeta`, `RoosRealization`, `TensorModel` and the theorem
  `completedPrimitiveCounitComparison`; these supply the primitive normalization.
- def-pc-tensor-complex-sheaves:
  `Mathlib.Algebra.Homology.BifunctorShift`, `CochainComplex.mapBifunctor`, via
  the existing `coefficientTotalTensor` and C's representative equations.
- def-zl-ringed-derived-closed-symmetric-monoidal-data:
  `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`,
  `CategoryTheory.RingedDerivedTensorCoherence` and
  `CategoryTheory.ringedTensorUnitComplex`. The landed existing:true definition
  node owns these plain definitions, which type the free parameter C and the
  degree-zero unit. It is the statement dependency.
- lem-sf-ringed-derived-closed-symmetric-monoidal:
  the same module, `CategoryTheory.ringedDerived_closed_symmetric_monoidal`.
  This remains a proof dependency only. The statement does not use its conclusion
  or choose data from its existential assertion.
- Proof-only imports additionally retain IntegralOperationsWellDefined and
  StrictRoosComparison. The proof dependency lem-pur-normalized-operation-system-models
  has no recorded Lean declaration in the read DAG, so its nonexistent module is not
  imported; its role in the proof is named in the docstring. It is not required
  to type this statement.

### Edge cases checked before writing

Zero inputs and the empty scheme do not require nonzero or nonempty hypotheses.
The theorem has no boundedness, constructibility, Tor-amplitude or finite-rank
condition. Repeated systems, including A=N=H=U, are permitted. The coefficient
exponent one is n=0 in Lean. The transition clause allows m=n and arbitrary gaps,
and actual sequence composition retains the quotient cocycle. The signed swap
uses all integer degrees, including negative degrees, and has the expected value
in characteristic two. Unit coefficients have degree zero. Independent t and u
retain small-site object size t+1, morphism size t and coefficient size max u (t+1).
The general syntax allows empty scheme/input index sets; this local four-pair
statement uses three named inputs, without any assertion that general index sets
are nonempty. No field datum or special geometric base is added to W.

### Searches and sources

- `msearch.py ... leanfinder` with query "Canonical tensor associator and unitors
  and Koszul symmetry transported through reduction and derived limit of normalized
  coefficient systems": 8 hits, including graded tensor symmetry and algebra
  presentations, no whole-system completed constraint transport theorem.
- `msearch.py ... leansearch` with query "Derived tensor associator unitors signed
  symmetry compatible with normalized adic reduction and limit adjunction": 8 hits,
  including Adjunction.derivedη, Limits.instLaxMonoidalFunctorLim, and ordinary
  HomologicalComplex.rightUnitor', no match for the statement.
- `msearch.py ... loogle "HomologicalComplex.associator"`: one hit, the total
  complex associator, an ingredient only.
- `msearch.py ... grep "associator|leftUnitor|rightUnitor|braiding"
  Algebra/Homology/Monoidal.lean`: five lines, the standard complex constraints,
  no coefficient-system realization statement.
- `rg` of the two project source trees for normalizedTensor, NormalizedTensor,
  tensorConstraint and TensorConstraint, and the exact item id: no exact existing
  statement. Nearby IntegralCoherenceTower and CompletedOperationTowerSubstitution
  were read. The latter's StructuralLaw merely characterizes a transported map;
  it does not identify the independently constructed quotient associator roof,
  which this item explicitly requires. It is also the node's downstream citer,
  so this module does not import it to obtain its helper definitions.
- Read the local Stacks proofs at sites-cohomology.tex lemma-pullback-tensor-product
  (07A4) and sites-modules.tex lemma-tensor-product-pullback (03EL). Read the current
  blueprint coefficient-twist unit and the node's eleven-step refinement. Those
  sources justify the canonical total tensor and scalar contraction conventions.
- Read the recorded Mathlib mapBifunctor signature/docstring using
  `scompile.py --source Mathlib.Algebra.Homology.BifunctorShift`, since the named
  local Mathlib checkout path was unavailable. No alternate local compilation used.

### Validation

The prescribed scompile.py checked the sandbox and installed module independently
against the live server library in about 8 seconds each, with no warnings or errors
on the clean run. Only the statement's proof is postponed. The node signature is
extracted verbatim from the module; all eighteen declarations are recorded. There
are no unbound variables, private helpers, file-local notation, or local instances.
The required deliver2.py --no-push dry run returned OK: commit ab684575a62
passed the server preflight and per-file compilation; nothing was pushed by that run.

## Second reading by NK

No second worker was started: this dispatcher brief expressly forbids delegation.
The maintainer's independent review is the independent reading. During the final
self-audit I matched all four pairs, checked the domains and codomains of the
quotient roof, verified the direction of every beta/gamma equality, and confirmed
that symmetry reverses the input pair of the final realization. I also checked
that the quotient arrow definitions do not refer to beta conjugation.

## Returned delivery repair (2026-10-21)

The independent review of immutable head f15676c75687 returned H2: the
statement used plain definitions owned by
`def-zl-ringed-derived-closed-symmetric-monoidal-data`, while the packet cited
`lem-sf-ringed-derived-closed-symmetric-monoidal` in stmt_deps. Replaced that
statement dependency by the landed existing:true definition node, retained the
theorem in proof_deps, and corrected lean.note and this report. No Lean source,
mathematical statement, proof plan, or other node field changed. This repairs the
returned delivery rather than re-pushing the unchanged packet.

The saved packet's initial dry run passed as 6866e742178, but still carried H2.
Compared the saved node with the current read-only main node: before this repair
only lean and the added theorem in stmt_deps differed. After repair only lean
and the addition of the owning definition node differ. The delivery wrapper
rebases the packet on the current server base without direct Git commands.

Read the owning definition node's lean record and the full signatures and
docstrings of RingedDerivedTensorCoherence and ringedTensorUnitComplex in its
recorded module. The structure parameter C and degree-zero unit use these
definitions directly; no .choose or existence-theorem application occurs in the
statement module. The theorem remains available through the same module for
the eleven-step proof plan. The review's advisories require no statement change:
transition and counit clauses are naturality, the inner contraction isomorphism
is a conclusion justified by proof step 4, and proof-only imports are retained
under stages/2-statements.md section 3 rule 7.

Repair validation: scompile.py compiled both the sandbox and library module
cleanly (7.8 and 7.6 seconds), without warnings or errors. The verbatim signature,
single sorry, unchanged proof_deps and exact node delta passed the self-check.
The repaired deliver2.py --no-push returned OK at commit 67898166009, passing
server preflight and per-file compilation.
