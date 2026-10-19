## Worker report

This delivery states `WeilConjectures.IntegralTowerLimit.integralTowerLimitComparison`
in `Sheaf.Paper.IntegralTowerLimitComparison`. Its only postponed proof is that
named theorem. All helper definitions have real bodies; structures package the
hypotheses and conclusions of this same node, rather than introduce independent
mathematical notions. The DAG statement, its dependency lists, and its proof plan
are unchanged.

Sources read: Stacks `sites-cohomology.tex`, labels
`lemma-derived-limit-is-ok` (Tag 0941, lines 5067 onward) and
`lemma-pullback-tensor-product` (Tag 07A4, lines 3684 onward); the item's six proof
steps; the current blueprint's `sk-def-purity-conv/_section.md` and
`def-weil-frobenius-coefficient-twists.md` (order 2232). The result is the agent-extracted
supporting lemma described by the node, not a claim that Stacks 07A4 directly states
all its integral conclusions.

Hypothesis and conclusion correspondence:

- Prime ell, finite extension E/Q_ell: `(l : ℕ) [Fact l.Prime] (E : Type u)
  [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. These are section binders
  retained by every relevant declaration. The existing coefficient rings use the
  chosen `Padic.coefficientExtensionUniformizer` and its power ideals; no second
  ring or uniformizer is defined.
- Scheme morphism and invertibility: `{X Y : Scheme.{t}}`, `(f : X ⟶ Y)`, `_hlX`
  and `_hlY` assert that l is a unit in every residue field. There is no finite-field,
  boundedness, constructibility, properness or finiteness assumption on f.
- B_n, R, Res and total derived limit: the existing `coefficientSequenceModules`,
  `coefficientSequenceRestriction`, and `coefficientSequenceLimit` use the actual
  small pro-etale site, finite quotient sheaves, completed inverse-limit ring and
  restriction along its projections. The index n : ℕ denotes positive exponent
  n+1, including exponent 1; it does not introduce an exponent-zero case.
- The coherent reduction R and coherent counit e are `(M.calculus false).reduction`
  and `(M.calculus false).adjunction.counit`. `M` is a presentation from the recorded
  `CompletedOperations.Models` interface, whose reduction adjunction, Roos
  normalization, K-flat tensor normalization and pullback normalization are fixed
  by its fields. The theorem additionally requires
  `_hM : CompletedOperations.ComparisonLaws.{t, u, 0, 0} l E M`, exactly the laws
  supplied with the model by `completedOperationTowerSubstitution`. In particular,
  bare `Models` data is not asserted to entail those laws. This is the existing
  canonical substitution package, supplied for schemes with l invertible.
- `Input.T`, `.U`, `.V` are ordinary unbounded cochain complexes of the existing
  ringed-sequence module category. This is precisely strict semilinear quotient
  towers, by `coefficientSequenceModules`; the module presheaf restrictions include
  the transition maps and their identity/composition laws.
- `Input.goodT`, `.goodU`, `.goodV` apply `Good` to each tower. `Good` evaluates at
  every n, asserts `CochainComplex.IsKFlatIndependentCoefficients`, and asserts
  `SheafOfModules.IsFlatOnSite` for each integer-degree term. These are the recorded
  K-flat and flat-sheaf predicates, without a private replacement.
- `Input.normalizedT`, `.normalizedU`, `.normalizedV` are
  `IsNormalizedCoefficientSequence` of each localized whole system. This is the
  existing universal tensor-restriction criterion for the actual quotient
  transitions, rather than normalization of an unrelated tower or equality only
  after forgetting coherence. It is the whole-system presentation used by the
  substitution dependency, which avoids the old `NormalizedDVRTower` interface's
  auxiliary finite-field datum.
- `pullback` is the recorded exact `integralComparisonSequencePullback` applied
  termwise to complexes, hence F_f(T)_n = f_n^* T_n. `total` is the recorded
  `coefficientTotalTensor` on the sequence site. Its evaluation is the signed
  direct-sum total tensor of U_n and V_n, through `coefficientEvaluationTensorIso`.
  Both operations retain their induced quotient transitions.
- `Input.c` is an actual chain isomorphism from `pullback.obj T` to
  `total.obj (U,V)`. An `Iso` supplies its strict inverse and both inverse equations.
  Both maps are morphisms in the whole system category, so every transition square
  is required, including longer quotients and the identity quotient.
- `source` is completed pullback of L_Y(T); `target` is the recorded
  `IntegralOnSlice.completedTensor` of L_X(U), L_X(V). Neither is an arbitrary
  object supplied by a hypothesis.
- `Realization.a` and `.b` have exactly the orientation S ≅ L_X(F_f(T)) and
  P ≅ L_X(W) used in the proof. `.a_formula` fixes a to
  `CompletedOperations.pullbackComparison` followed by the exact functor's
  `mapDerivedCategoryFactors.hom`; `.b_formula` fixes b to
  `CompletedOperations.tensorComparison` followed by the inverse of the
  representative-normalized `CoefficientTensorModels.iso`. Those two comparison
  functions are the existing coherent-counit composites. These equations prohibit
  arbitrary replacement isomorphisms. `.kflatU` and `.kflatV` are conclusions,
  justified by evaluation detecting acyclicity and commuting with total tensor;
  they are not additional whole-system K-flat assumptions on the inputs.
- `comparison r` is the actual isomorphism
  `r.a ≪≫ L_X.mapIso (DerivedCategory.Q.mapIso A.c) ≪≫ r.b.symm`.
  Its hom and inv are thus exactly b^-1 L(c) a and a^-1 L(c^-1) b in the node's
  right-to-left convention. `Laws` explicitly records both inverse equations.
- `sourceReduction` and `targetReduction` are R(a) followed by e_A and R(b)
  followed by e_D. `Laws` asserts these are isomorphisms and gives both equations
  `R(mu) ≫ r_P = r_S ≫ Q(c.hom)` and
  `R(nu) ≫ r_S = r_P ≫ Q(c.inv)` in the derived category of WHOLE coefficient
  systems. Thus the reduction identity retains every quotient transition; it does
  not infer equality of coherent maps from equality of evaluations.
- `Diagram` contains t,u,v and the actual strict square
  F(t) ≫ c' = c ≫ T(u,v). `sourceMap` and `targetMap` are precisely completed
  pullback of L(t) and completed tensor of L(u), L(v). `Laws` quantifies over every
  such diagram and every canonically specified target realization, asserting
  naturality of a, naturality of b, the forward comparison square, and the inverse
  comparison square.
- Finally, the last implication in `Laws` asserts that simultaneous
  `QuasiIso d.t`, `QuasiIso d.u`, `QuasiIso d.v` give isomorphisms of the completed
  source and target. Together with the preceding square, this identifies the two
  comparison maps after those isomorphisms. These are the canonical resolution
  identifications: their component operations are the recorded normalized descents
  in `integralOperationsWellDefined`, and `.a_formula`/`.b_formula` pin their
  substitution comparisons before localization. No independent arbitrary maps are
  substituted for the canonical resolution maps.

Dependency declarations and source modules read:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, reexporting the coefficient constructions.
- `def-weil-scheme-morphism-properties` is a convention record with no declaration;
  schemes, morphisms and residue fields use their Mathlib declarations.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `WeilConjectures.integralConstantToCompletionOfUniverses` and its unchanged
  unrestricted completion and finite quotient projections.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`.
- `Sheaf.Paper.IntegralReductionTowerCanonical`:
  `WeilConjectures.canonicalIntegralReductionTower`, its canonical augmentation maps.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`:
  `WeilConjectures.IntegralOnSlice.completedTensor` at `none`; the original
  `integralDerivedPullback` and its K-flat comparison are reexported.
- `Sheaf.Paper.NormalizedDVRTower`: `WeilConjectures.NormalizedDVRTower` and its
  universal normalization condition; the current whole-system equivalent
  `IsNormalizedCoefficientSequence` is reexported by the substitution module.
- `Sheaf.Algebra.Homology.KFlat`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`, as used
  by the canonical `coefficientTotalTensor`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `AlgebraicGeometry.Scheme.proEtaleSheafInverseImage` and its coefficient module
  inverse image; the exact whole-sequence version is
  `integralComparisonSequencePullback` in the substitution import closure.
- `Sheaf.Paper.CompletedOperationTowerSubstitution`:
  `WeilConjectures.CompletedOperations.Models`, `.pullbackComparison`,
  `.tensorComparison`, and `.completedOperationTowerSubstitution`. Its public
  `IntegralComparisonRealizationModels` and `CoefDerivedSystemEvaluationCalculus`
  imports provide the representative characterizations, actual total-limit functor
  and reduction adjunction used here. No copy of those notions is introduced.
- `Sheaf.Paper.NormalizedDVREffectivity`:
  `WeilConjectures.normalizedDVRTower_effectivity`; the whole-system counit version
  is used through the substitution interface.
- `Sheaf.Paper.IntegralOperationsWellDefined`:
  `WeilConjectures.integralOperationsWellDefined` and the normalized representative
  comparisons reexported by the integral operation definitions.
- Proof dependency `lem-coef-semilinear-derived-sections`:
  `Sheaf.Paper.SemilinearDerivedSections`,
  `WeilConjectures.SemilinearSections.semilinearDerivedSections` (publicly imported
  by the substitution module).
- Proof dependency `def-weil-derived-tensor`:
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`,
  `AlgebraicGeometry.ProEtale.derivedTensor`. This fixed-ring sheaf presentation
  is read via `scompile.py --source`; the whole ringed-sequence model used in the
  signature is the substitution dependency's canonical intrinsic tensor.

Edge cases checked before writing: the first quotient exponent is 1; identity
quotient arrows and longer quotient composites are retained by the presheaf laws;
zero inputs and empty schemes are allowed; f may be an identity; c and its inverse
are actual strict maps; no degree bounds are imposed; different site and coefficient
universes t,u use coefficient size max u (t+1), with pro-etale objects in t+1 and
morphisms in t. The two-scheme Bool index is only bookkeeping for the existing
substitution model and places no restriction on X or Y.

Searches, with exact service outputs saved in sandbox `searches.jsonl`:

- `msearch.py ... leanfinder "strict normalized coefficient tower isomorphism induces
  derived limit isomorphism compatible with completed pullback tensor and coherent
  reduction"`: eight hits, chiefly `AdicCompletion.ofTensorProduct*`,
  `AdicCompletion.tensor_map_id_left_eq_map` and scheme pullback tensor congruence;
  none states normalized sheaf-system limit transport with coherent reduction.
- `msearch.py ... loogle "CategoryTheory.Functor.mapIso"`: twelve generic functor/iso
  identities; these supply the elementary functorial part, not this entire statement.
- `msearch.py ... grep "derived.*limit|normalized.*tower|completed.*tensor"
  CategoryTheory`: two pointwise derived-functor colimit/limit helper hits, no match.
- `msearch.py ... leansearch "canonical comparison derived inverse limit strict
  quotient systems completed pullback tensor naturality"`: eight ordinary
  `InverseSystem`, direct-limit tensor and `HasLimit.isoOfNatIso` hits, no match.
- `rg` in the specified upstream `WeilConjectures`, side `lean/Sheaf` and
  `dag/lean_names_upstream.json`, using the node id, `integralTowerLimitComparison`,
  `IntegralTowerLimit`, and strict-tower comparison patterns: no declaration of
  this result; existing completed/substitution machinery was found and reused.
  The current upstream Tensor module was missing from the old checkout, so its
  full live source was obtained with the prescribed `scompile.py --source` command.

No statement correction, disputed claim, new node or dependency repair is needed.
Compilation and the delivery dry run are performed using the prescribed wrappers;
the only expected warning is the main theorem's postponed proof.

## Second reading by Q54

The dispatcher forbids starting other agents and assigns independent delivery
review to the maintainer. Accordingly this section records the worker's explicit
final rereading, without claiming an independent worker review. I reopened the
node and the module and matched every binder and conclusion as above. In particular
I checked the orientation of a and b, both inverse maps, coherent (rather than
merely evaluated) reduction equations, the two substitution naturality squares,
the forward and inverse diagram squares, and the quasi-isomorphism consequence.
The first compiler pass exposed that the exact-pullback localization comparison
needed `.hom`, not `.inv`; that orientation was corrected after reading its full
Mathlib signature. All arrows in `Realization` are fixed by equations, and no
unjustified inference from bare model data is made: the existing `ComparisonLaws`
premise is now explicit. The auxiliary whole-system K-flat assertions
are conclusions from the original levelwise hypotheses. No natural-language
statement or dependency was changed.


## Repair of return L (immutable head 61b1d28044a6)

The returned version quantified over an arbitrary `CompletedOperations.Models`
without `ComparisonLaws`, a substantively stronger interface than the DAG's
canonical-substitution statement. The maintainer requested either using the
constructed model with its laws or explicitly assuming those laws. This repair
uses the latter option: `integralTowerLimitComparison` now binds
`_hM : CompletedOperations.ComparisonLaws.{t, u, 0, 0} l E M`. The theorem's
node record contains the updated signature verbatim, and its docstring explicitly
requires this package. No helper or canonical comparison arrow was replaced.

Reopened the full `Models`, `ComparisonLaws`, and
`completedOperationTowerSubstitution` declarations in
`Sheaf.Paper.CompletedOperationTowerSubstitution`. `Models` fixes presentations
and representative formulas; `ComparisonLaws.counit` gives coherent counit
invertibility on normalized systems, `.normalized` gives preservation of
normalization, `.invertible` gives substitution and reduction isomorphisms, and
`.naturality` gives the system naturality squares. Those are now premises rather
than conclusions claimed for arbitrary model data. Their availability follows
from the existing dependency theorem, which produces a model and those laws
simultaneously under exactly the scheme invertibility hypotheses already present.

The scheme-index universe is 0 because `sites X Y` is Bool-indexed. The
input-expression universe is 0 because pullback and binary tensor involve only
finite input sets. The independent site and coefficient universes t and u and
the small pro-etale site sizes are unchanged. Empty schemes, identity f, zero
complexes, every positive quotient exponent, and unbounded inputs remain allowed.
The helper definitions, `Realization` formulas, both coherent reduction equations,
and all diagram and quasi-isomorphism clauses are unchanged.

The saved packet was dry-run before modification as requested. Its mechanical
checks do not resolve return L's mathematical interface issue; this is a concrete
repair of that issue, not an unchanged re-push. Compared saved and current shared
node records: every field outside `lean` agrees. The delivery wrapper refreshes
the current base and creates the delivery commit. No DAG statement correction,
new node, or dependency-module repair is needed.

Validation after repair: `scompile.py Q54
lem-pur-integral-tower-limit-comparison` compiled the delivered module in sandbox
and library modes with exit code 0 and no diagnostics. The source self-check
confirmed the verbatim signature, unchanged non-`lean` node fields, the explicit
model-law binder, exactly one postponed theorem, and every Lean line at most
100 characters. The final dry run and delivery use the prescribed wrapper.
