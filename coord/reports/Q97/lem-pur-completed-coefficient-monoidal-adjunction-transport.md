## Worker report

Q97 states `lem-pur-completed-coefficient-monoidal-adjunction-transport` in
`Sheaf.Paper.CompletedCoefficientMonoidalAdjunctionTransport`, declaration
`WeilConjectures.CompletedCoefficientTransport.completedCoefficientMonoidalAdjunctionTransport`.
The theorem has one `sorry`. Its five definition modules contain real structures,
functors, morphisms and predicates, with no `sorry`, axiom or choice from an
unconstrained existence theorem. The item's statement and proof are unchanged.
The only other item-field change is adding the delivery's definition-node dependencies.

The previous worker's stage-1 reopening objection does not apply: the existing
PASS is a split review, and the live item had no Lean record. The explicit stage-2
exception in coord/brief-stage1.md permits stating this unchanged node. This packet repairs independent review of returned head 14a8da545e9b.

Hypotheses and objects:

- `l : ℕ`, `[Fact l.Prime]`, `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`,
  `[FiniteDimensional ℚ_[l] E]` are exactly the prime and finite extension.
  The valuation ring and uniformizer are the recorded
  `Padic.coefficientExtensionIntegers` and `coefficientExtensionUniformizer`.
  `constantUniformizer` is their actual constant section, using `toSheafify`.
- `W : S → Scheme.{t}` and `_hl : ∀ a x, IsUnit (l : (W a).residueField x)`
  permit every scheme and every morphism between the selected schemes. The
  family formulation states the simultaneous choices needed for composition.
  A particular f is obtained by selecting its source and target in the family;
  a composable pair is obtained by selecting three schemes. There is no
  separatedness, properness, smoothness or finite-type condition.
- The site is the original `Scheme.ProEt.topology`, object universe `t+1`,
  morphism universe `t`. Coefficient/module universe is `max u (t+1)`; derived
  morphism universe is `max u (t+1)+1`. No equality between `t` and `u` is used.
- `completed` is `completedIntegralCommRingSheafUnrestricted`; `constant` is
  `constantSheaf` of the lifted valuation ring. `DR` and `DA` are ordinary,
  unbounded `DerivedCategory` categories of the recorded module sheaves.
- `Site.U` is the dependency's `ExactImage` of the actual
  `SheafOfModules.restrictScalars (integralConstantToCompletionOfUniverses ...)`.
  Its factors compute termwise restriction on every complex.

Each clause of the result:

- `Site.completion` uses `PrincipalQuotientCompletion.Model` for constant
  coefficients: the actual quotient tower, signed Roos cone, universal derived
  counit, K-flat computation, actual quotient augmentation and natural unit.
  The R-side completion and unit are exactly `IntegralOnSlice.completion` and
  `completionUnit`. `Site.d` and `d_unit` identify them under U on *every*
  ambient R-object. `r_complete` identifies the unit-invertibility criterion
  with `IsDerivedCompleteUnrestricted`; `r_output`, `r_reflect`, `a_output`
  and `a_reflect` give the actual reflector properties. Thus the specialized
  reflector interface is not used by imposing an extra universe equality.
- The R tensor is exactly `IntegralOnSlice.completedTensor`; the constant
  tensor is `Site.closed.closed.tensor ⋙ Site.completion.completion`.
  `ReflectedTensor.tensor` and `unit` identify the complete-category tensor
  and coefficient unit with these ambient completed constructions.
- `TensorTransport.equivalence` has forward functor *equal* to the lift of U.
  Its monoidal structure and `braided` equation preserve both associators,
  both unitors, and symmetry. These structures are fixed by the actual units:
  the lax braided inclusions' tensor map is eta followed by the inverse tensor
  identification, and their coefficient map is eta followed by the inverse
  unit identification. No arbitrary completed monoidal structure is assumed.
- `TensorTransport.a` defines the specified a with the required direction,
  using the inverse strong tensorator and the two tensor identifications.
  `TensorTransport.representatives` fixes the balancing map on every local
  homogeneous generator and on all flat-term K-flat representatives. It uses
  the dependency's `CoefficientTensorModels.iso` and `ExactImage.factors`.
  `TowerBalancing` requires *one natural transformation of entire strict
  quotient towers*, invertible at each level, with the quotient augmentation
  equation. Naturality includes every transition. Its inverse is the finite
  reassociation/change-of-rings comparison of the node. No assertion that
  finite evaluations detect equality of ambient derived maps is made.
- `Transport.tensor_unit` is precisely the displayed balancing/completion-unit
  normalization: mu followed by U(eta^R) followed by a equals eta^A.
- `Arrow.image` is the existing `ComparisonData`, with source and target U
  records required equal to those in `Site`. Its structural map, finite
  projections, sectionwise coefficient comparisons, right derived universal
  units and K-injective formulas are retained. `Arrow.r` and `a` use the
  existing `DerivedAdjunction` with its representative Hom formula. Equalities
  `r_right`, `a_right`, `r_unit`, `a_unit` ensure the right images are the same
  recorded images. `Arrow.kappa` is literally that comparison transported
  along those equalities. It is not a new arbitrary isomorphism.
- The ordinary left adjoints are left adjoints to the actual ringed/constant
  module pushforwards. This is their canonical universal characterization;
  it does not assume exactness of ringed pullback. `exactA` records exactness
  of constant inverse image; `flatR` its R counterpart on good representatives.
- `Arrow.pullback` identifies completion of ordinary R pullback with the
  *specified* `integralDerivedPullback`. `PullbackNormalization` pins this
  comparison: the finite mates' ordinary adjoints send each local section to
  its actual reduction followed by `integralOperationsPullbackGenerator`.
  The Roos augmentation has this product component and zero shifted component.
  Its derived equation uses `integralDerivedPullbackComparison`, the universal
  ordinary derived comparison, and the actual R completion unit. Hence the
  finite maps and transitions are fixed before total limit.
- `Arrow.scalarUnit` is the ordinary adjunction mate of the sectionwise identity
  square. Under the ringed tensor-pullback adjunction this is x ↦ 1 tensor x.
  `scalarComplex` is the same mate on complexes. `Arrow.tau` is its derived
  mate using kappa; `Transport.scalar_normalization` imposes exactly its
  good-representative formula, as in the recorded ringed-counit presentation.
- `AdjunctionTransport.b` is natural with source completed constant pullback
  after U and target U after completed R pullback. `b_unit` is exactly
  eta^A followed by b = tau followed by U(eta^R). The normalized `Arrow.pullback`
  identifies its R endpoint with the node's quotient pullback.
- `PullTensor.representatives` fixes ordinary pullback tensorators by the
  tensor of the ordinary adjunction units on homogeneous generators. Its
  derived equation uses the existing normalized tensor models.
  `PullTensorTransport.r_unit` and `a_unit` say that the actual completion
  units are monoidal. Its `b` field is the monoidal naturality square for b,
  relative to those tensorators and the tensorators defining a.
- `valueRIdentification` recursively identifies the underlying `valueR` object with
  `CompletedOperations.completedValue`: identity on inputs, `r_tensor.unit` followed
  by `system_unit` on coefficient units, `r_tensor.tensor` followed by completed
  tensor of the recursive identifications on tensor vertices, and `Arrow.pullback`
  followed by specified derived pullback of the recursive identification on pullback
  vertices. This uses the recorded quotient operations, not an abstract tensor.
- `constantSystemComparison` applies ordinary constant tensor/inverse image to the
  recursive comparisons, then the representative-normalized balancing/scalar-unit
  map, the actual R completion unit, and the existing coherent-counit
  `tensorComparison`/`pullbackComparison`. It extends through constant completion
  by `reflectConstant`, the inverse of the actual reflector Hom bijection. Thus
  these maps use the same finite comparisons fixed by `TowerBalancing` and
  `PullbackNormalization`, with all quotient transitions. It never uses a/b at
  tensor or pullback vertices to define the comparison it is supposed to identify.
- `ExpressionSystemLaw` is an additional conclusion of the theorem: the ambient
  underlying `expressionTransport`, followed by U of `valueRIdentification` and
  `CompletedOperations.comparison`, equals that constant whole-system comparison.
  This links a/b iterations to the actual coherent system comparison. The unit
  branch uses the same normalized coefficient-unit map as the primitive tensor data.
- `ExpressionSystemStructuralLaw` is also an explicit conclusion: `structureR`,
  after the recursive ambient identifications, has both the total-limit square
  with `comparison` and the whole-system reduction square with `reductionComparison`.
  `Transport.system_comparison/substitution/structural` remain only with these new
  links. `composition_system` fixes the pullback compositor by its system square.
  `ExpressionSubstitutionLaw` and `ExpressionStructuralLaw` then state the a/b
  substitution and structural squares with all inverse/composite/tensor/pullback
  contexts. These last abstract squares alone are not presented as the system link.
- `r_preserves` and `a_preserves` permit the complete right adjoint restrictions.
  `AdjunctionTransport.r_hom` and `a_hom` specify the two completed adjunctions
  by the ordinary Hom equivalence after precomposition with eta. The two
  `_counit` fields give eta followed by epsilon^c = epsilon, including cases
  where eta on the ordinary pullback is not invertible.
- `ordinary_counit` is tau followed by U(epsilon_R) = Q_A(kappa) followed by
  epsilon_A on arbitrary ambient inputs. `counit` is precisely the node's
  completed counit identity on complete M. `hom` is equality of the inverse
  completed Hom bijections for every complete H,M and every right Hom arrow;
  `unit` is the corresponding actual unit identity. Full faithfulness is
  supplied by the complete equivalence, not assumed on ambient U.
- No complete-input condition is put on ordinary representative computations,
  d, the ordinary counit identity or the completion units. No bound,
  constructibility or Tor-amplitude binder appears anywhere.

Dependency declarations read and used (besides Mathlib CategoryTheory structures):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, valuation ring/uniformizer/quotients.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, its topology.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantRingOfUniverses`, `integralConstantToCompletionOfUniverses`;
  its coefficient dependencies provide the completed and finite ring sheaves.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`;
  Mathlib's `DerivedCategory`, `SheafOfModules.restrictScalars`.
- `Sheaf.Paper.WeilCompletedTensorReflector`: `Scheme.wfCompletionReflector`;
  `Sheaf.Paper.ConstantCompletionEquivalence`: `ConstantCompletion.equivalence`.
  The new statement keeps the original site and sizes and states the normalized
  quotient-completion realization; it does not assume a same-size API applies
  definitionally to all coefficient universes.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`: `IntegralOnSlice.D`,
  `completion`, `completionUnit`, `duality`, `completedTensor`;
  `Sheaf.Paper.IntegralDerivedOperations`: `integralDerivedPullback`,
  `integralDerivedPullbackComparison`; existing good complexes, finite
  reductions, pullback generators and Roos functors are used verbatim.
- `Sheaf.Paper.CompletedCoefficientPushforwardComparison` and its public
  `CompletedCoefficientPushforwardModels`: `ComparisonData`, `ExactImage`,
  `RightImage`, `Square`, `Mod`, actual structural maps and coefficient squares.
- `Sheaf.CategoryTheory.ReflectorAdjunctionUnitFormulas`:
  `exists_reflector_restricted_adjunction`, including its actual Hom formula.
- `Sheaf.Paper.CompletedOperationTowerSubstitution`:
  `completedOperationTowerSubstitution` as proof dependency; its existing definition
  ownership nodes below provide `Models`, `ComparisonLaws`,
  `SubstitutionLaw`, `StructuralLaw`, `comparison`, `structuralValue`.
- `Sheaf.CategoryTheory.RingedCoefficientRestrictionCounit`:
  `ringedCoefficientRestrictionCounit`; its public presentation module supplies
  `DerivedAdjunction`, reused rather than copied.
- `Sheaf.Algebra.Homology.PrincipalQuotientCompletionModel`: `Model`,
  `quotientTower`, `quotientMap`; `Sheaf.Paper.PrincipalKoszulStrictReplacement`:
  `uniformizer`; `Sheaf.CategoryTheory.RingedSiteDualityMaps`:
  `RingedSiteDualityModel`; `CoefficientTensorModels.iso` and
  `coefficientTensorGenerator`; independent-coefficient K-flatness and flatness.

Edge cases checked by reading the actual signatures and representative formulas:
zero objects and zero maps; empty schemes; f = identity; a composite with identity;
positive exponent one (Lean tower index 0); identity quotient transitions; coefficient
units; arbitrary complexes unbounded in both directions. Tensor signs remain those
of the recorded total-tensor symmetric models. Completion-unit cancellation uses
`a_reflect` into a complete target, never levelwise equality detection. The finite
extension and prime hypotheses give the recorded DVR; no auxiliary distinct prime
from the pushforward existence theorem is made a hypothesis of this theorem.
Empty families simply give empty families of model data.

Searches: `msearch.py` LeanFinder queries on restriction preserving completed tensor
and adjunction units/counits returned classical `AdicCompletion` and ordinary
`ModuleCat.ExtendRestrictScalarsAdj` statements, not this statement. Loogle
`CategoryTheory.Adjunction, CategoryTheory.MonoidalFunctor` returned zero hits
(the latter name is absent); Mathlib grep `completed.*tensor|completion.*adjunction`
in CategoryTheory returned zero hits. Additional LeanSearch on normalized transport
models returned classical finite-module completion statements; LeanFinder on
canonical quotient-tower transport models returned algebra-presentation tensor
models and classical completion. Grep for the four new structure names returned
zero Mathlib hits. Project-wide rg of both Lean trees found no existing transport
statement or these model structures. `blueprint_refs.py search 'completed coefficient
transport'` returned zero matches. Existing near matches were read and reused.
The corrected Loogle query `CategoryTheory.Functor.Monoidal,
CategoryTheory.Adjunction` returned twelve abstract monoidal-adjunction results,
including `IsMonoidal.instIsMonoidalCounit`; these do not state the coefficient
completion transport. Exact tool queries and returned declaration names are retained in the sandbox
`searches.jsonl` and copied into each new node's `mathlib_searches`.

There is no statement correction and no STATEMENT-DISPUTED flag.

## New nodes

`def-pur-completed-coefficient-tensor-transport-models` defines the reflected tensor,
site presentation and tensor transport model, its whole-tower balancing predicate,
and the actual a comparison. Its module is
`Sheaf.Paper.CompletedCoefficientTensorTransportModels`. Source: Stacks 099I and
099K and the item's steps 1--7. Searches above found no existing node or declaration
for this package; it reuses all constituent notions and their recorded interfaces.

`def-pur-completed-coefficient-adjunction-transport-models` defines ordinary and
derived arrow presentations, their normalized scalar mates, complete adjunction
transport, the representative-normalized pullback tensor model and ordinary pullback tensor model. The simultaneous `Transport` record is
owned by the family node described below. Its module is
`Sheaf.Paper.CompletedCoefficientAdjunctionTransportModels`. Source: Stacks 099I,
099K, 03D7 and 07A4, and the item's steps 5--11. It depends on the first new node
and the existing presentation/substitution nodes. The same three kinds of search,
plus DAG and both project-tree searches, found no existing such notion. These
are definitions of canonical normalized data; existence is asserted only by the
item theorem. Splitting the packages keeps all single-file compiles under 60 seconds.

`def-pur-completed-coefficient-transport-expressions` defines evaluation of the
existing operation expressions on both complete categories, their recursive
coefficient comparison, the substitution comparisons, the structural maps, and
both transport-law predicates. It reuses `CompletedOperations.Expression` and
`StructuralMap`; it introduces no second expression syntax. The module is
`Sheaf.Paper.CompletedCoefficientTransportExpressions`. The extra LeanSearch
query on recursive completed coefficient comparisons returned power-series
substitution statements; LeanFinder returned categorical/algebraic near matches;
Mathlib grep and project-tree rg found no expression transport declaration.
`blueprint_refs.py search 'coefficient transport expressions'` returned zero.
The source is the same final blueprint paragraph and the item's steps 6--7.

The compile checks use only the prescribed scompile.py and deliver2.py wrappers.
The repaired expression/system modules were split to keep their elaboration within
the 60 second per-file limit. Every delivered file is compiled separately.
The one postponed theorem remains `by sorry` as required for stage 2.

`def-pur-completed-coefficient-family-transport-models` owns
`Sheaf.Paper.CompletedCoefficientFamilyTransportModels`: the completed pullback
unit transformations, their monoidal transport, the canonical composition map,
and the simultaneous `Transport` structure. It is split from the per-arrow
adjunction module for compile cost; its statement explicitly lists the unit,
monoidal, system and composition data. The per-arrow node now owns `Arrow`,
`AdjunctionTransport` and ordinary representative `PullTensor` only.

`def-pur-completed-coefficient-system-transport` owns
`Sheaf.Paper.CompletedCoefficientSystemTransport`: `reflectConstant`,
`constantSystemComparison`, `ExpressionSystemLaw` and
`ExpressionSystemStructuralLaw`. Its statement specifies all recursion branches
and both system linkage predicates. Searches are the same recorded expression
searches and the new whole-system queries in searches.jsonl; none matches this
coefficient-transport linkage. Its source is the unchanged item's iterated-system
clause, proof steps 3--7 and the final blueprint paragraph.

`def-pur-completed-operation-model-data` is `existing: true` for
`CompletedOperations.Models`, `tensor`, `unit`, `tensorRealization`,
`tensorComparison` and `pullbackComparison` in
`Sheaf.Paper.NormalizedCompletedOperationModels`. The self-contained definition
statement lists the model fields and coherent-counit formulas; it makes no
existence assertion. These definitions were previously listed only under a
 theorem node. The new node gives them definition ownership without duplicating
any declaration or citing that existence theorem as a definition prerequisite.

`def-pur-completed-operation-comparison-data` is `existing: true` for
`StructuralMap` and the expression/system evaluations, recursive comparisons,
substitution isomorphisms and `ComparisonLaws`, `SubstitutionLaw`, `StructuralLaw`
in `Sheaf.Paper.CompletedOperationTowerSubstitution`. Its statement spells out
these constructions and predicates without claiming they hold. The new coefficient
adjunction and expression definitions cite it instead of the theorem node.

`def-pur-integral-operation-complex-models` is `existing: true` for
`integralOperationsTowerStep`, `integralOperationsRoos`,
`integralOperationsPullbackTowerFunctor` and `integralOperationsPullbackComplexFunctor`
in `Sheaf.Paper.IntegralOperationsWellDefined`. The statement fixes the actual
successor transition, strict finite pullback tower and Cone(1-s) shifted by -1,
without its well-definedness theorem. This also repairs the advisory missing
ownership citation for the pullback representative normalizations.

For these ownership nodes, current Mathlib searches were: LeanSearch, "Whole
coefficient system operation models and coherent recursive substitution comparison
laws" (power-series substitution results); LeanFinder, "Derived coefficient sequence
tensor pullback recursive comparison models" (stream/type-vector relation results);
Mathlib grep, "structure Models|def comparison|inductive StructuralMap" in
CategoryTheory (six monad/comonad comparison names). Source and DAG grep found the
exact listed Sheaf definitions under theorem ownership and no primary definition
node. Upstream WeilConjectures gave no match. blueprint_refs.py search "completed
operation model" returned zero. Therefore existing:true records reuse the exact
implementations, rather than introducing another notion or another module.

## Second reading by Q97

I reopened the item JSON, all six delivered Lean files, the new node statements,
and the existing definition signatures. No other agent was started, as the
explicit dispatch forbids it. The following is the worker's second reading;
the maintainer performs the independent review.

1. Coefficients and sites: `l`, its prime instance, finite E/ℚ_l and `_hl` match
   the first paragraph. The original small pro-etale site has object size t+1
   and morphism size t; u is independent. Empty schemes/families and identities
   are not excluded. The family formulation handles any composable pair.
2. Ambient categories: `DR`, `DA`, `Site.U` use ordinary unbounded module-sheaf
   derived categories and actual exact restriction. `Site.completion`, `d_unit`,
   the two reflector predicates and `r_complete` identify the actual Koszul/strict
   quotient completion units, with no complete-input assumption on `d_unit`.
3. Tensor clause: `TensorTransport.a` has U(completed R tensor) as source and
   completed A tensor as target. `representatives`, `TowerBalancing` and
   `UnitNormalization` fix the balancing formula and the single natural quotient
   tower map; `ReflectedTensor` fixes associator/unitors/symmetry by the actual
   unit. The inverse tensorator used in expressionTransport has the correct
   orientation. No field chooses an arbitrary isomorphism in place of the map.
4. Pullback clause: `Arrow.pullback`, `PullbackNormalization` and
   `TauNormalization` retain the reduced scalar-unit section formula and zero
   shifted Roos component. `b_unit` gives etaA followed by b = tau followed by
   U(etaR). `PullTensorTransport` asserts the actual tensor/pullback square.
5. Iterated clause (H3 repair): the previous copied system law fields did not
   connect e_P to beta_P. The new `valueRIdentification` supplies the missing
   recursive ambient identification, and `ExpressionSystemLaw` supplies precisely
   that missing equality, using the independent reflector construction of the
   constant comparison. `ExpressionSystemStructuralLaw` separately supplies the
   total-limit and coherent reduction squares. Both are conclusions of the one
   theorem alongside the abstract substitution/structural transport squares.
   The finite c maps are those normalized by the existing strict quotient-tower
   balancing and scalar-unit representative equations; no independent finite
   isomorphisms or equality-detection assumption has been substituted.
6. Adjunction clause: `Arrow.kappa` is the recorded `constantSquare` comparison.
   `r_hom`, `a_hom` specify the completed Hom bijections by precomposition with
   the actual completion unit. The two completed-counit normalization fields,
   ordinary counit identity, completed counit identity, inverse-Hom equality and
   unit equality retain their original directions. No bound, constructibility
   or Tor-amplitude premise appears in the theorem.
7. Definition ownership (H12/H2 repair): per-arrow/family/expression definitions
   cite new existing:true definition records for Models, recursive structural
   comparison data, and strict pullback/Roos complexes. They no longer cite the
   substitution theorem for plain definitions. The original theorem node remains
   an item dependency because its asserted substitution result is used in the
   proof. No existing theorem-node fields were changed.
8. Record and proof checks: the item differs from current source only in lean
   and added definition dependencies. Every new definition statement cites
   exactly its stmt_deps; all declarations are listed in their owning records.
   Every signature is copied verbatim from its owning source. There is exactly
   one sorry, on the item theorem; the five definition modules have real data.
   All Lean lines are at most 100 characters.

No statement correction was needed. The reviewed claim is unchanged.

Final verification: deliver2.py --no-push returned OK for commit ef260c7dfe1,
including server preflight and every per-file compile. No non-sorry warning remains.
