## Worker report

Delivered module: `Sheaf.SixFunctors.IntegralBasicRealization`.
Main declaration: `WeilConjectures.IntegralSystemRealization.integralBasicRealization`.
It states the primitive realization assertion with `sorry`; no mathematical theorem is
proved. `HasBasicRealizations` packages the assertion as an existential proposition.
All other declarations have complete bodies: they specialize existing domain predicates,
name the restricted functors, or spell out a clause of the asserted comparison.
There are no new independent notions or new DAG nodes, no dependency replacement modules,
and no change to the item's natural-language statement or proof.

The previous worker's stage-1 stale-assignment diagnosis does not describe this task:
the current item is split and reviewed at stage 1, has no Lean binding, and the prompt
explicitly assigns its stage-2 statement. The retained sandbox had no Lean/node/report
files. The current source and reviewed proof were used throughout.

Clause-by-clause correspondence:

1. The fixed finite-field datum is `D : FiniteFieldDatum.{u}`. It includes the prime,
positive exponent, finite base field and its algebraic closure `D.k`. The coefficient
prime is `l : ℕ` with `[Fact l.Prime]` and `_hl : l ≠ D.p`. The finite extension is
`E : Type u` with `[Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
Its valuation ring, uniformizer, finite quotients and all quotient maps are the
published Padic constructions; none is redefined. Natural index `n` denotes the
positive exponent `n+1`, so coefficient exponent zero is never substituted for one.

2. Each scheme is over `Spec (.of D.k)`, with `LocallyOfFiniteType` and `QuasiCompact`
on its structure morphism. Arrows are over that same base. Pullback arrows have
`IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact`; proper arrows have `IsProper`;
open arrows have `IsOpenImmersion` and `QuasiCompact`. The site's object universe is
`u+1` and its morphism universe is `u`; they have not been identified. The common
scheme/coefficient size parameter is the existing Operations/domain interface.

3. `System`, `Integral`, `calculus`, `Operations.push`, `Operations.shriek` and
`calculus.systemClosed.tensor` are the dependency's actual derived system operations.
`calculus.reduction`, `coefficientSequenceLimit` and `calculus.adjunction` are the
actual reduction/limit adjunction, including its actual unit and counit.
There is no replacement by a list of finite derived objects.

4. `basicUnaryDomain` is the one-input specialization of `Expression.domain`:
`sfIntegralConstructible` on the integral input, `Good` on its actual reduction,
and `Good` on the primitive system output. `basicTensorDomain` imposes these
conditions on BOTH integral inputs and both reductions, and on their tensor output.
`basicSupportDomain` additionally imposes `Good` on the intermediate open extension.
`Good` retains normalization, compatible etale-origin witnesses, finite-level
constructibility and common finite cohomological and Tor intervals. For finitely
many intermediate systems, their finite intervals may be enlarged to a single
common interval. The geometry is bound separately on each primitive assertion.
These are domain specializations, not copies of the underlying notions.

5. Each comparison is a natural isomorphism between functors from the corresponding
full input subcategory. `basicUnarySource` is exactly inclusion, reduction, the
system operation, then total limit. `basicUnaryTarget` is inclusion then the
specified integral operation. The two-input source uses the product of the actual
reduction functors. Thus naturality covers arbitrary derived input morphisms,
not just representative cochain maps or finite evaluations.

6. The pullback and tensor existential comparisons are constrained to be exactly
the restrictions of `(pullbackTensorIntegralPullbackModel l E v).symm` and
`(pullbackTensorIntegralTensorModel l E W).symm`. Their defining uniqueness theorems
pin their components on flat-term K-flat representatives to the strict full-tower
Roos comparisons. Those comparisons include the actual quotient transitions,
ordinary scalar-unit normalization and the right-derived Roos normalization.
This reuses the existing construction instead of choosing a different triangle map.

7. The proper comparison is fixed by `model.push`, the right-adjoint conjugate of
the whole-system representative-normalized `model.reductionPull`, followed by
proper image of the inverse ACTUAL reconstruction unit. `unit` proves that the
needed unit is invertible on the input domain; it is a conclusion, not an extra
hypothesis. `basicProperTower` additionally supplies the defining
`SfIntegralDirectImage` Roos witness and an identification of its vertex with
`ringedPush`. Under that identification every actual system-limit projection is
exactly the defining proper-image tower projection after direct-image evaluation
and reduction evaluation. In particular its transition is the recorded
`sfDirectImageTransition`, including the coefficient-restriction comparison.
The countable-product instance is supplied explicitly from the recorded theorem;
it is not an additional assumption.

8. `model.openReduction` is the inverse open-adjunction mate, defined in the
canonical bridge module using the actual completed-ring and system adjunctions.
It has direction `J R -> R j_!`; the whole-system map called `r_j` in the node is
its inverse. `_openReduction` asserts invertibility on the stated domain.
`openUnit` asserts invertibility of the actual unit at `j_!K`. `_open_spec` fixes
`d_J` to `L.map model.openReduction` followed by that inverse unit, exactly
`u_(j_!K)^(-1) L(r_j)^(-1)`. Because the reduction map is the actual adjunction mate,
this identifies the localized open adjunction as well as its object values; no
arbitrary evaluated arrow is lifted.

9. For a fixed `c : Compactification f`, the support conjunct gives a natural
isomorphism `d` from `L S_p J_j R` to the actual
`sfCompactSupportFiniteIntegralFunctor`, included in the ambient integral category.
`basicSupportInput` is just inclusion in the recorded integral constructible category.
The formula for `d.hom` is the direct proper comparison after open extension,
then total limit of the same inverse open reduction, then the inverse actual unit,
and finally the published `sfQcqsCompactSupportRealization`. Hence it uses the
recorded integral functor's action on morphisms, not a new action on its values.
The `hl : IsUnit (l : D.k)` binder is the proof argument of that recorded functor;
it is already implied by the fixed finite-field datum and `l ≠ D.p`.

10. The support comparison includes `tower`, an isomorphism of functors INTO THE
DERIVED CATEGORY OF STRICT COMPLETED-COEFFICIENT TOWERS. Its target `T` is constrained
to be literally the tower already used by the recorded compact-support action;
`e` is constrained by `HEq` to that tower's actual recorded evaluation family.
There is no new choice of a tower from unrelated evaluations. On every admitted input,
for EVERY `m n`
and `h : n ≤ m`, including equal indices, the transition equation is exactly
`compactSupportRestrictedTransition`: larger-level proper/open image of the quotient
map, followed by the specified restriction-of-scalars comparison and composition
of restrictions. `tower`'s evaluations are pinned to the actual open/proper
`supportEvaluation` and actual reduction evaluation. The last equation identifies
the scalar adjunct of the system-limit projection with the recorded finite
compact-support reduction of `d`. This retains the whole tower, its total limit
and its projections. No expression-tree or generator coherence is included.

Dependency declarations read and reused (module and main declaration):

- `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber`, `WeilConjectures.FiniteFieldDatum`.
- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`.
- `def-weil-scheme-morphism-properties`: a collector of existing Mathlib scheme/morphism notions; it fixes no separate notion. Its named properties are used directly.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`, `AlgebraicGeometry.Scheme.ProEt`.
- `lem-coef-derived-system-evaluation-calculus`: `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`, `WeilConjectures.coefficientDerivedSystemEvaluationCalculus`.
- `def-sf-integral-system-operations`: `Sheaf.SixFunctors.IntegralSystemOperations`, `WeilConjectures.IntegralSystemRealization.Operations`.
- `def-sf-integral-system-expression-domain`: `Sheaf.SixFunctors.IntegralSystemExpressionDomain`, `WeilConjectures.IntegralSystemRealization.Expression.domain`.
- `def-pur-integral-derived-operations`: `Sheaf.Paper.IntegralDerivedOperationsOnSlices`, `WeilConjectures.IntegralOnSlice.completedTensor`.
- `def-weil-derived-direct-image`: `Sheaf.Paper.SfDerivedDirectImage`, `WeilConjectures.SfIntegralDirectImage`.
- `lem-sf-integral-open-reduction-comparison`: `Sheaf.SixFunctors.IntegralOpenReductionComparison`, `WeilConjectures.IntegralOpenReduction.integralOpenReductionComparison`.
- `lem-weil-pbc-ringed-strict-tower-homotopy-limit`: `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`, `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`.
- `lem-pur-integral-operations-well-defined`: `Sheaf.Paper.IntegralOperationsWellDefined`, `WeilConjectures.integralOperationsWellDefined`.
- `def-weil-integral-rational-qbar-compact-support`: `Sheaf.Paper.QcqsCompactSupportRealization`, `WeilConjectures.sfQcqsCompactSupportRealization`.
- `lem-sf-compact-support-restriction-of-scalars`: `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction`, `AlgebraicGeometry.ProEtale.intrinsicCompactSupportRestriction`.
- `def-sf-integral-system-canonical-bridge`: `Sheaf.SixFunctors.IntegralSystemCanonicalBridge`, `WeilConjectures.IntegralSystemRealization.CanonicalBridge`.
- `def-pur-completed-pullback-tensor-comparison`: `Sheaf.Paper.CompletedPullbackTensorComparison`, `WeilConjectures.canonicalIntegralPullbackTensor`.
- `lem-weil-compact-support-reduction-tower-functor`: `Sheaf.Paper.CompactSupportReductionTower`, `WeilConjectures.exists_compactSupportReductionTower`.
- `def-weil-compact-support-finite-action`: `Sheaf.Paper.CompactSupportFiniteAction`, `WeilConjectures.SfCompactSupportFiniteRealizationSpec`.

In particular, the additional statement dependencies are already landed nodes:
`def-sf-integral-system-canonical-bridge` supplies the section-normalized
`RealizationModel`, its proper conjugate and its actual open reduction mate;
`def-pur-completed-pullback-tensor-comparison` supplies the exact normalized primitive
model isomorphisms; `lem-weil-compact-support-reduction-tower-functor` supplies the
recorded whole strict tower and transition recipe; and
`def-weil-compact-support-finite-action` supplies the already normalized actual
integral functor and its actual finite projection adjuncts. Their existing modules
are imported; none of their node files or declarations is changed.

All stated proof-dependency modules are imported with plain `import`, except where
already publicly required by a statement dependency. The two proof dependencies
`lem-pur-quotient-system-flat-models` and `lem-pur-flat-roos-functor-descent` have no
recorded Lean declaration yet; they occur in the proof docstring but there is no
module to import. Their needed construction is already exposed by the published
normalized primitive model interfaces, so no missing notion prevents this statement.

Edge cases checked:

- `n=0` means the first quotient, not R/t^0. The transition quantifier permits
  `m=n`, and uses the recorded identity/composition-compatible quotient maps.
- Zero complexes are allowed. No nonzero coefficient, nonempty open, positive
  Betti number or nonzero cohomology assumption is inserted.
- The empty open and empty schemes are allowed. All comparisons use actual open
  extension and actual adjunctions, so no generator in a nonexistent summand is
  requested and no choice of a point is made.
- Identity pullbacks, identity proper maps and identity open immersions are included.
- Tensor has two independent input slots and the domain bounds both; it does not
  identify the two inputs. No K-flatness assumption is added to derived inputs.
- Intermediate bounds and etale-origin witnesses are retained also at the open
  factor of compact support. No blanket stability theorem replaces that proviso.
- Natural isomorphisms lie in the recorded derived categories; no result is weakened
  to a per-cohomology or object-only identification.

Searches made:

- `msearch.py ... leanfinder`: “Natural realization isomorphisms from total derived
  limit of strict integral coefficient systems for pullback tensor proper direct
  image and compact support”. Eight general sheaf pullback/tensor comparison hits;
  none states this primitive integral package.
- `msearch.py ... loogle`: `Functor.isoWhiskerLeft, Functor.associator,
  NatIso.ofComponents`. No aggregate match; Loogle reports that its name index
  does not recognize the first identifier. Source inspection supplied the names.
- `msearch.py ... grep`: `integralBasicRealization|IntegralSystemRealization|completedPrimitive`.
  No Mathlib hit.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item ID,
  `integralBasicRealization` and `completedPrimitive` found the existing
  `CompletedPrimitiveCounitComparison` tensor/pullback result, not this node.
  Further source search found the exact quotient/Roos models in
  `CompletedPullbackTensorComparison` and the section/adjunction-normalized
  interfaces in `IntegralSystemCanonicalBridge`; these are reused.
- Source search of `IntegralCompactificationSystemRealization` found the larger
  `Realizations` package, which also asserts expression/generator coherence. It is
  not used as an existing match or as an assumption for this primitive theorem.
- The Mathlib small pro-etale site definition, the actual dependency declarations
  and their docstrings were read, including the generalized strict-tower limit
  signature and the actual open reduction comparison.

No STATEMENT-DISPUTED claim and no source-based statement correction are needed.
The stale example `CompactObject.lean` is now an intentionally withdrawn empty
module; current statement modules were followed for the required module header,
public imports, exposed section, source docstrings and explicit universes.

Validation: the delivered module passed `scompile.py` in sandbox and library module
modes under the ordinary 60-second per-file limit, with no errors or warnings.
The earlier large structure was changed to the same existential proposition to
avoid expensive generated recursors; this did not alter the mathematical assertion.
The report and node record were then checked against the final file.

## Second reading by Q117

This is the worker's explicit self-audit; the prompt reserves the independent
review for the maintainer and prohibits starting another agent.

I reread the current node, all final domain predicates, the normalized comparison
interfaces and the final module. The proper comparison now explicitly retains its
defining Roos witness and projection maps; compact support explicitly targets the
recorded integral functor, and carries a whole derived strict-tower isomorphism with
its prescribed evaluation family, all-pairs transitions and projection adjuncts.
The open inverse is the actual unit inverse, not a completion isomorphism selected
independently. Pullback/tensor equal the existing full strict Roos comparisons.
The geometry and intermediate-domain provisos are present on each primitive case.
The same prime, finite extension, quotient indexing, schemes and actual operations
occur in both statements. No expression or generator coherence, extra arbitrary
map, unbound universe or hollow definition is introduced. No mismatch remains.
