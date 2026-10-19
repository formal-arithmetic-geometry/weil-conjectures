## Worker report

The delivery states coherent substitution of normalized quotient systems into completed
integral tensor and pullback. `CompletedOperationTowerSubstitution.lean` has one postponed
theorem, `WeilConjectures.CompletedOperations.completedOperationTowerSubstitution`; its
complete twelve-step natural-language proof is in its docstring. All helper definitions
have real data. No mathematical statement is changed.

The statement is packaged as existence of compatible canonical presentations `Models`
and three sets of laws. This is a conclusion, not an additional hypothesis or an
assumption that the desired comparison exists. `Models` fixes the actual published
reduction/limit adjunction, the total-complex-normalized tensor and its structural maps,
the quotient-augmentation-normalized completion comparison, and pullback realization
normalized on every simultaneous K-flat quotient presentation. In particular there is
no arbitrary tensor, action, completion map, or unnormalized objectwise isomorphism.

Hypothesis and clause correspondence:

- Prime ell is `(l : ℕ) [Fact l.Prime]`; the finite extension is `(E : Type u)
  [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. The existing coefficient
  construction fixes the uniformizer and actual quotients. No new coefficient ring
  or independent choice of quotient maps is introduced.
- A family `W : S → Scheme.{t}` covers every scheme appearing in an expression.
  `_hl : ∀ a x, IsUnit (l : (W a).residueField x)` is precisely invertibility of ell
  on each scheme. Maps used by expressions are actual scheme morphisms. The site
  keeps object universe `t+1`, morphism universe `t`, and coefficients `max u (t+1)`.
- The finite rings, their completion, and all scalar maps are the recorded
  `integralCoefficientCommRingSheaf`, `coefficientSequenceCommRingSheaf`, and
  `scalarReductionSource`. A Lean level `n : ℕ` means exponent `n+1`, covering
  every positive exponent, including ramified quotients.
- Whole coherent systems are `coefficientSequenceDerived`, the ordinary unbounded
  derived category of module sheaves on the actual ringed sequence site. The
  published `IsNormalizedCoefficientSequence` tests the adjoints of the actual
  quotient transitions by the normalized tower's universal Hom criterion.
- `Models.calculus.reduction` is R; `coefficientSequenceLimit` is L, defined by
  restriction of the whole system and total right derived inverse limit. The
  calculus's `reductionModel`, `unit_projection`, and `counit_projection` pin the
  strict reductions and identify the counit with the adjoint of the actual
  total-limit projection. `ComparisonLaws.counit` asserts invertibility of this
  coherent counit on every normalized system, without a boundedness restriction.
- System T is `tensor`, from the existing K-flat-normalized closed tensor model.
  Its evaluations and finite tensor models are supplied by the calculus, with
  `Models.system_closed` identifying the same structure. System F is the published
  `integralComparisonDerivedSequencePullback`, the exact derived inverse image on
  the ringed sequence site, retaining its horizontal quotient transitions.
- The completed operations are exactly `IntegralOnSlice.completedTensor ... none`
  and `integralDerivedPullback`. `tensorRealization` composes the recorded ordinary
  tensor model, reduction's tensor comparison, and the completion comparison.
  `Models.completion_unit` fixes that comparison by the actual Roos augmentation;
  `Models.pullback` includes its full cochain/generator normalization and Roos model.
- `tensorComparison` is the tensor realization followed by L applied to
  `T.map (e_A,e_N)`; `pullbackComparison` is the pullback realization followed by L
  applied to `F.map e_C`. These are literal definitions of the specified arrows,
  rather than independently chosen isomorphisms after taking the limit.
- `Expression` has precisely input, unit, tensor, and pullback constructors, with
  the output scheme as its type index. Every term is finite; inputs may repeat,
  and neither available index type is restricted to be finite or nonempty.
  `unit` is the actual sequence coefficient sheaf in degree zero, with its
  quotient transitions. Its limit is the completed unit input.
- `systemValue` and `completedValue` are recursive functors with identical
  parentheses, using only these constructors and the recorded operations.
  `ComparisonLaws.normalized` says every system expression is normalized, hence
  includes the primitive tensor, inverse image and coefficient unit cases.
- `comparison` is beta: identity at inputs and units; applying the completed
  operation to the child comparisons, followed by the primitive comparison, at
  tensor and pullback nodes. `ComparisonLaws.invertible` asserts that beta and
  its coherent reduction are isomorphisms for all normalized inputs.
- `reductionComparison` is gamma = R(beta) followed by the actual coherent
  counit. It is a map in the derived system category. `ComparisonLaws.transitions`
  explicitly gives its square for every quotient `h : n ≤ m`, including identity
  and nonadjacent quotients. It asserts no faithfulness of evaluated morphisms.
- `StructuralMap` lists the associator, both action unitors, Koszul symmetry, and
  the pullback compositor, and allows their inverses, compositions and contexts.
  `structuralValue` uses the canonical total-complex-normalized
  `RingedSiteDualityModel`: its `associator_model`, `unit_model`, `symmetry_model`
  fix reassociation, scalar multiplication and `(-1)^(pq)` respectively.
  Pullback composition is `integralComparisonSystemComposition`, explicitly the
  localization of the finite ordinary adjunction-normalized composition map.
- `StructuralLaw` gives the unique canonical completed constraint c with
  `c ≫ beta_Q = beta_P ≫ L(alpha)` and the coherent reduction equation
  `R(c) ≫ gamma_Q = gamma_P ≫ alpha`. Thus the completed constraints are precisely
  limits of the specified system maps under the comparisons. This constructs
  them by their unique counit characterization, with no arbitrary lifting choice.
- `ComparisonLaws.naturality` gives the square for every morphism of every input.
  `Expression.substitute` performs simultaneous typed substitution.
  `systemSubstitution` and `completedSubstitution` are actual recursive evaluation
  isomorphisms, identities at leaves, tensor/pullback images at operation nodes.
  `SubstitutionLaw` says comparing after substitution equals comparing the inner
  expressions, then applying the outer completed expression and its comparison.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the imported coefficient extension
  ring, quotient ideal and uniformizer constructions.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` (reexported by the
  realization models): the completed coefficient sheaf, its independent-universe
  constant coefficient cone and actual projection maps.
- `Sheaf.Paper.NormalizedDVRTower`: `normalizedDVRRes`,
  `normalizedDVRQuotient`, `NormalizedDVRTower` and its normalization criterion.
  The full ringed sequence-site realization is used, as specified by the item's
  semilinear-section hypothesis; no auxiliary finite-field datum is added.
- `Sheaf.Paper.SemilinearDerivedSections`:
  `SemilinearSections.semilinearDerivedSections` and its normalized system calculus.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `CoefficientDerivedSystemCalculus`, reduction/tensor/evaluation models and the
  canonical reduction/total-limit adjunction and counit projections.
- `Sheaf.Paper.IntegralReductionTowerCanonical`: `canonicalIntegralReductionTower`
  and its unit/quotient transition normalization, retained as a proof import.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `ringedStrictTowerHomotopyLimitIndependentCoefficients`, retained for total limit.
- `Sheaf.Paper.NormalizedDVREffectivity`: `normalizedDVRTower_effectivity`, used by
  the proof plan to obtain invertibility of the canonical coherent counit.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`: `IntegralOnSlice.completedTensor`,
  `duality`, `completion`, `completionUnit` and the global representative comparison;
  its reexported `integralDerivedPullback` is the original quotient/Roos descent.
- `Sheaf.CategoryTheory.RingedSiteDualityMaps`: `RingedSiteDualityModel`,
  `ringedSiteDualityUnit`, and all its K-flat tensor structural normalizations.
- `Sheaf.Paper.IntegralComparisonSequenceSystems`:
  `integralComparisonDerivedSequencePullback` and
  `integralComparisonSystemComposition`; these have independent site/coefficient
  sizes and use the actual constant-section ring maps and adjunction mates.
- `Sheaf.Paper.IntegralComparisonRealizationModels`: `IntegralComparisonRoosModel`
  and `IntegralComparisonPullbackModel`, including their exact K-injective and
  every-K-flat-quotient-presentation normalizations.

The new statement dependencies cite the already landed coherent evaluation,
canonical duality, sequence-system and realization-model interfaces used above.
All available proof-dependency modules are imported; none of these imports closes
an import cycle with this new module.

Edge cases checked: zero systems and zero complexes; empty input index sets (unit
expressions still exist); empty scheme families; repeated input occurrences;
expressions with no operation symbols; nested tensors and pullbacks; identity
and composite scheme maps; exponent one and every larger positive quotient;
identity, consecutive and nonadjacent quotient transitions; arbitrary negative
cohomological degrees and the Koszul sign; coefficients ramified over Q_l;
independent site and coefficient universes. No flatness of the quotient ring maps
or tensor/inverse-limit interchange is assumed. No statement dispute was found.

Searches: msearch LeanSearch queried completed derived operations on normalized
systems and returned ordinary ring tensor/flatness/direct-limit results. Loogle
`"counit", "tensor"` returned generic monoidal adjunction/equivalence laws.
LeanFinder returned lax-monoidal limit and ordinary adic completion results.
Mathlib CategoryTheory grep `completed.*[Ss]ubstitut|normalized.*[Tt]ensor` returned
zero hits. Upstream node-id grep returned zero hits. Upstream and side searches
found no statement of this complete coherent substitution theorem. Existing
`CompletedPullbackTensorComparison` supplies related constructible/same-universe
comparisons, not this unrestricted finite-expression statement. Searches for the
new syntax are recorded verbatim in its node's `mathlib_searches`.

## Author check

This is an author check; the maintainer independently reviews the delivery. I reopened the node and both Lean
modules and checked each clause against the correspondence above. The finite
expression clause includes units, repeated leaves and arbitrary substitution;
normalization and coherent reduction are required for every expression. Structural
maps are the canonical total-complex maps, not arbitrary maps detected after
evaluation. Site universes remain independent. All data definitions are explicit;
the sole postponed proof is the item's theorem. The initial instance-selection
conflict was repaired without restricting those universes. Compile and delivery
validation results are recorded below after the final checks.

## New nodes

`def-pur-completed-operation-expressions` introduces only the finite typed syntax
and simultaneous substitution used by the item's final paragraph, from its proof
steps 7, 8 and 12 and blueprint coefficient-twist comparison, order 2232. Its
module is `Sheaf.Paper.CompletedOperationExpressions`. `Expression` has input,
coefficient-unit, binary tensor, and actual scheme-pullback constructors;
`Expression.substitute` recurses structurally and preserves output type. Searches
of the DAG, blueprint references, Mathlib, upstream and side sources found no
matching notion. Mathlib results concern polynomial substitution or fibre-product
carriers. The side `SfCbcExpression` only brackets composable compact-support
words; `PbcDistinguishedDiagramLifting.Expr` only describes shifted additive arrow
formulas. Neither supplies this syntax. Every search and its result is recorded
in the new definition node. There is no postponed theorem in its module.

## Validation

Both delivered modules compiled individually through `scompile.py`. The final
source has no errors or unexpected warnings. The required `deliver2.py --no-push`
dry run also compiled both files and passed the server preflight for the two
modules, two DAG records and report (dry-run commit `ffe2b706dc`). The only
postponed proof is the named item theorem.

## Second reading by Q45

Independent maintainer second reading of immutable delivery
c592c1883441ef7c770ff5860b792b22b27a26d5, performed on 2026-10-18. This
reading was not performed by the author. The original worker report above is
preserved. The placeholder formerly under this heading was the only landing
finding (H11); this complete replacement supplies the actual reading.

I read the item node, all fourteen statement-dependency records, both delivered
modules, their docstrings and declarations, and the source locations. The
hypothesis and conclusion checks are as follows.

1. Prime and finite extension: the section parameters l, Fact l.Prime, E, Field,
   Algebra and FiniteDimensional give exactly the coefficient datum. The actual
   chosen uniformizer and its quotient maps come from the existing coefficient
   construction. W ranges over arbitrary scheme families and _hl expresses
   invertibility at every residue field. No finite-field datum, qcqs assumption,
   constructibility, flat quotient, or boundedness assumption has been added.
2. Categories and normalization: coefficientSequenceDerived is D of module
   sheaves on the actual ringed sequence site. IsNormalizedCoefficientSequence
   uses the universal Hom criterion for the adjoint of its actual quotient
   transition. Under the tensor/restriction adjunction this is exactly the
   node's normalization condition, with no independent transition choices.
3. Reduction and limit: Models.calculus supplies the recorded reduction functor,
   its strict K-flat reductionModel, the actual reduction/total-limit adjunction,
   and its unit_projection and counit_projection equations. The specified L is
   coefficientSequenceLimit, exact scalar restriction followed by the total
   right-derived inverse limit, rather than a diagram of unrelated derived
   objects. ComparisonLaws.counit states effectivity of that system counit.
4. Tensor and inverse image: Models.system is a RingedSiteDualityModel and
   system_closed identifies its tensor with the calculus tensor. Its normalized
   total-complex models compute A_n tensor over B_n with N_n. The pullback is
   integralComparisonDerivedSequencePullback, the exact derived inverse image
   on the whole sequence site. Its actual adjunction-unit coefficient maps and
   quotient transitions are retained. ComparisonLaws.normalized includes
   primitive tensor, inverse image and coefficient units by taking the
   corresponding expressions and normalized leaves.
5. Completed operations: completedValue uses the published
   IntegralOnSlice.completedTensor and integralDerivedPullback. integral_closed,
   completion_unit, and the every-presentation normalization of Models.pullback
   identify these particular functors with their quotient/total-limit models.
   Models is existential conclusion data, not an added assumption that the
   desired comparison already exists.
6. Primitive comparisons: tensorComparison is tensorRealization followed by
   L applied to T(e_A,e_N); pullbackComparison is the normalized pullback
   realization followed by L applied to F(e_C). These are actual formulas for
   the arrows requested by the node. Their inner maps are maps of systems.
7. Finite expressions: Expression has exactly input, coefficient unit, binary
   tensor and scheme pullback constructors. systemValue and completedValue are
   recursive functors with matching parentheses. comparison is identity at
   leaves and uses the primitive counit comparisons at operation nodes.
   ComparisonLaws.invertible asserts the requested isomorphisms for every
   normalized family, not only for generators or constructible complexes.
8. Coherent reduction: reductionComparison is R(beta) followed by the counit.
   Its invertibility is asserted, and ComparisonLaws.transitions gives the
   square for every h : n <= m, including identities and nonadjacent indices.
   Equality of arbitrary derived system maps is never inferred from evaluations.
9. Structural arrows: structuralValue uses the system associator, the two
   action unitors, signed symmetry and the finite adjunction-normalized
   integralComparisonSystemComposition. RingedSiteDualityModel.models,
   associator_model, unit_model and symmetry_model pin these to total-complex
   reassociation, scalar action and (-1)^(pq). StructuralLaw uniquely specifies
   the completed constraints by beta_P ; L(alpha) ; beta_Q inverse and also
   asserts their coherent reduction equation. This is a canonical transport
   construction, not a choice of an arbitrary isomorphism. It includes inverses,
   composites and finite tensor/pullback contexts.
10. Naturality and substitution: ComparisonLaws.naturality quantifies over all
    morphisms of normalized inputs. Expression.substitute is genuine structural
    recursion. systemSubstitution and completedSubstitution are recursive
    evaluation isomorphisms, and SubstitutionLaw has precisely the two routes
    through inner comparisons and the outer comparison, in the correct order.

The dependency interfaces were checked in CoefficientExtensionFinite,
CompletedIntegralConstantMapOfUniverses, NormalizedDVRTower,
SemilinearDerivedSections, IntegralReductionTowerCanonical,
RingedStrictTowerHomotopyLimitIndependentCoefficients, NormalizedDVREffectivity,
IntegralDerivedOperationsOnSlices, CoefDerivedSystemEvaluationCalculus,
RingedSiteDualityMaps, IntegralComparisonSequenceSystems and
IntegralComparisonRealizationModels. The scheme-property record is an explicit
convention record. The fourteenth dependency is the delivered expression node.
In particular I inspected the projection-adjoint counit, simultaneous reduction
and tensor normalizations, Roos K-injective normalization, and pullback
normalization on every simultaneous quotient presentation, not merely names.

Source checks: Bhatt--Scholze Definition 3.4.10, printed p.22, defines completed
tensor; Lemma 6.5.9(4), printed pp.50-51, motivates completed inverse image.
Section 6.5 assumes qcqs schemes; the delivery explicitly labels its unrestricted
system-coherence claim as an agent refinement, whose argument is on ringed sites
and does not invoke the qcqs lemma for that generality. I also read Stacks
sites-cohomology.tex, labels lemma-K-flat-resolution (06YS),
lemma-tensor-product-K-flat (07A2), lemma-pullback-K-flat (0G7E),
lemma-pullback-tensor-product (07A4), and lemma-derived-limit-is-ok (0941).
The blueprint coefficient-twist source at order 2232 motivates the application;
it is not claimed to contain this finite-expression theorem verbatim.

Route pivot: the item's statement/proof dependencies have empty intersection
with origin/newtargets-dag:coord/route-pivot-dropped.txt. No repair note exists
for this item at that ref. The operative Lean interfaces use ordinary D(Tow),
K-flat resolutions and total right-derived limit. The old word 'enhanced' in
inherited DAG proof prose refers to the now-restated semilinear dependency;
no enhanced localization, Quillen rectification, straightening or operad
construction is used in this delivery.

Edge cases checked: empty input and scheme index types, units without inputs,
zero complexes/systems and the empty scheme; repeated inputs and leaf-only
expressions; identity and composite scheme maps; all positive quotient exponents
(Lean n=0 means exponent one), including ramified coefficients; identity and
nonconsecutive transitions; arbitrary negative cochain degrees and Koszul signs;
independent t,u,s,i,j. The actual site remains Type (t+1) with Category.{t};
coefficients/modules use max u (t+1). No silent universe equality is imposed.

Independent duplicate searches in Mathlib CategoryTheory, the upstream
WeilConjectures tree and the side Sheaf tree found no complete theorem or matching
expression syntax. CompletedPullbackTensorComparison and DerivedPullbackTensorIso
are related interfaces on constructible/same-universe objects; SfCbcExpression
is compact-support composition syntax. They are not duplicates of this item.
The new definition node records all three search kinds, has the required fields,
correct chapter/unit, empty proof fields, and cites only its scheme dependency.

Both lean.statement fields agree with the respective complete declaration
signatures modulo layout whitespace. The module and declaration source/blueprint
docstrings are present; the item docstring follows all twelve proof steps.
Definitions contain real recursive/composite data; the sole postponed theorem
has proof exactly `by sorry`. No local proof was filled, no global build was run,
and no project clone or live Lean source was edited. No statement_change is
needed and there is consequently no citer correction audit to perform.

Independent compiler reproduction: invoked
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q45 lem-pur-completed-operation-tower-substitution snapshot/lean/Sheaf/Paper/CompletedOperationExpressions.lean snapshot/lean/Sheaf/Paper/CompletedOperationTowerSubstitution.lean`.
Exit status 0, no errors or unexpected warnings. The installed wrapper used its
server-backed private side overlay (its implementation currently says server
only, despite the older local-wrapper description in the brief). It reported:
private expression overlay 25.9 s; preliminary expression 55.9 s; Sandbox0
23.1 s; library expression 7.6 s; Sandbox1 23.8 s; library substitution 28.8 s.
All invocations stayed below the per-file 60-second limit. The private overlay
was `/dev/shm/nt-tmp/nt-local-compile-3muvv3vn/.lbuild`. No direct SSH command,
project edit, delivery command, or global build was run by the reviewer.
The report-only correction does not change these compiled sources.
