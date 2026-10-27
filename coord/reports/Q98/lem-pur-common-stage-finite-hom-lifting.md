## Worker report

Item: lem-pur-common-stage-finite-hom-lifting. The delivery states
`WeilConjectures.CommonStageFiniteHomLifting.finiteHomLifting` in
`Sheaf.Paper.CommonStageFiniteHomLifting`. Its sole postponed proof is `sorry`.
The node's statement, proof, dependency lists and other fields are unchanged.
No new DAG node or dependency repair is needed.

The three helper definitions contain real data. `residueInvertible` maps the
published inverse in the stalk into its residue field. `restrictionHom` is
`commonStageDerivedPullback.map`, conjugated only by its specified object equalities,
so its endpoints are the literal pairs in the node. `stageRestriction` is the
existing comparison hom, rational pullback on the representative, and comparison
inverse, in Lean's left-to-right composition order. No functor or scalar comparison
is chosen arbitrarily, and no coefficient category is redefined.

Hypotheses and clauses, in order:

- The fixed finite-field and coefficient conventions are `P : PurityFiniteSetting`:
  `P.field` has the finite field and its fixed algebraic closure, while
  `P.coefficients.l`, its prime instance, `different`, and `Qbar` give ell distinct
  from the characteristic and the fixed coefficient closure. The conventions'
  ancillary finite extension and positive level are unused in the statement.
- `X`, `Xi i` are schemes over `Spec P.field.k` and `j i : Xi i ⟶ X` are their
  morphisms over the base. `LocallyOfFiniteType X.hom`, `QuasiCompact X.hom`, and
  their dependent instances for every `Xi i` state exactly finite type over k.
  There is no immersion, cover, disjointness, separatedness or essential-surjectivity
  assumption. These distinguish this lemma from the downstream clopen descent result.
- `I : Type w` with `[Finite I]` permits any finite set, including the empty one;
  its universe is independent of the scheme universe.
- `Stage` is the dependency's raw rational category at the canonical small
  coefficient model of each finite intermediate field, on the small pro-etale site.
  `Pair`, `Common`, `StageHom`, `ofHom` and `transport` are all the recorded
  common-stage pair-category constructions, with no Karoubi completion.
- `hfully` quantifies over every finite coefficient field E and every pair K, M
  at that rational stage. Its `Function.Bijective` of the tuple of actual rational
  pullback maps is exactly full faithfulness of R_E. It does not assume fullness
  of each individual component functor or injectivity of scalar transitions.
- For arbitrary global pairs `A B`, the first conjunct is bijectivity of the tuple
  of canonical `restrictionHom` maps onto the product of their literal local Homs.
- The second conjunct gives the representative formula at every common field L:
  restriction of `ofHom ... a` is `ofHom ... (stageRestriction ... a)`. The latter
  is b_A.hom followed by r_L(a) followed by b_B.inv. This is precisely the node's
  b_B inverse composed with r_L(a) composed with b_A, with categorical composition
  written left to right.
- The third conjunct takes every component tuple v and every `Finset` S of finite
  coefficient fields. It supplies a common endpoint field L containing S and a
  single representative a whose restriction classes equal v. Together with the
  second conjunct, this gives a simultaneous representative of all components.
- The fourth conjunct starts with actual representatives v_i at arbitrary local
  common fields `Li i`, and quantifies over EVERY global common field L and bounds
  `hL : ∀ i, (Li i).val ≤ L.val`. It supplies a at this very L, with rational image
  b_A.inv followed by the transported v_i followed by b_B.hom. This is the displayed
  lifting equation in the node, not merely an existence claim at some larger field.
  In particular L may also contain any prescribed finite list.
- The fifth conjunct states the component-class equality iff existence of a common
  N where the two transported global representatives agree, for arbitrary L0,L1.
- The sixth conjunct takes the actual component equality witness fields `Ni i`
  and equalities of transported `stageRestriction` representatives there. It then
  quantifies over every N above L0, L1 and all Ni, asserting global equality at
  exactly that N. Thus no transition injectivity or backwards transport is used.
- The final conjunct is `IsEmpty I → Nonempty (A ⟶ B) ∧ Subsingleton (A ⟶ B)`,
  exactly that the global Hom is a singleton for the empty family. For this family
  the fourth clause permits any common endpoint field, and the sixth permits any
  common representative field. The finite-compositum construction starts with
  `Padic.finiteCoefficientBase` (Q_l); enlarging it for the endpoints and listed
  fields gives the choices in the third clause, also for S empty. No unnecessary
  strict extension is imposed, so Q_l itself is allowed when all bounds are Q_l.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting` and
  `PurityFiniteSetting.coefficientPrime_isUnit_stalk`; the latter supplies, rather
  than assumes, residue-field invertibility needed by the pullback API.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and its quasi-compact dependency:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt` and
  `Scheme.ProEt.topology`, as used by the recorded coefficient categories.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory` and the
  specified raw scalar extension underlying `Stage` and its transitions.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: `Stage`, `Pair`, `Common`,
  `StageHom`, `ofHom`, `transport`, `representatives`, and `stageSystem`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `rationalDerivedPullback`,
  `commonStagePullbackObject`, `commonStagePullbackComparison`,
  `commonStageDerivedPullback_existsUnique`, and `commonStageDerivedPullback`.
  The comparison incorporates `operationStageTransitionIso`, so the statement
  uses the exact stage-system transitions, not definitionally presumed substitutes.
- `Sheaf.Paper.IntegralOperationsScalarComparisons`: normalized integral scalar
  pullback comparisons and `scalarOperationsOrdinary_tower` / `_unit`; the rational
  comparisons already imported through the operation dependency rationalize these.
- `Sheaf.Paper.SfScalarExtensionComposition`: `sfRationalScalarComp` and its
  `existsUnique` normalization, underlying the recorded scalar transport.
- `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`: `Padic.FiniteCoefficientFields`,
  `finiteCoefficientBase`, `finiteCoefficientCompositum`,
  `finiteCoefficientFields_properties`; `Index` is the recorded alias of this type.

Edge cases checked before writing: empty I and empty prescribed list; Q_l endpoint
and representative fields; identity coefficient extensions and repeated fields;
identity j_i; zero objects; arbitrary different endpoint and representative fields;
equality that appears only after a later scalar extension. The lifting formula uses
both endpoint comparisons in the correct direction. The witness clause enlarges
actual equality witnesses and never assumes injectivity of any transition. No
STATEMENT-DISPUTED flag or source correction is needed.

Searches for an existing declaration:

- msearch.py, leanfinder: "Finite product of common stage coefficient Hom colimits
  admits simultaneous lifts and eventual equality under stagewise full faithfulness".
  Eight results: generic presentability/filtered-product colimit tools, including
  `colimitPointwiseProductToProductColimit` and `IsIPC.isIso`; no coefficient
  pullback theorem or the prescribed simultaneous lifting/equality clauses.
- msearch.py, loogle: "CategoryTheory.Functor.FullyFaithful, Function.Bijective".
  Two hits: `FullyFaithful.map_bijective` and `nonempty_iff_map_bijective`. They justify
  the Hom-wise encoding of the hypothesis but are not the common-stage conclusion.
- msearch.py, grep: `filtered.*(prod|pi)|colimit.*(prod|pi)` in
  `CategoryTheory/Limits`. Twenty-five generic colimit/product hits; no match.
- rg on `lean/WeilConjectures` and `lean/Sheaf`: common-stage Hom / full-faithfulness
  queries and exact intended namespace/declaration searches. No declaration of this
  statement. Exact item-ID grep in `WeilConjectures` has no hit. The downstream
  `FiniteProductFieldDescent.arrows_at_common_field` and
  `component_equality_iff_eventual` have clopen-cover and integral-equivalence
  hypotheses; they are not this lemma and cannot serve as a dependency without
  reversing the DAG. Their sources and full signatures were read.

Validation: prescribed scompile.py checks passed separately as a sandbox module
and as `Sheaf.Paper.CommonStageFiniteHomLifting`, with no errors or non-sorry warnings.
Initial endpoint inference errors were repaired by explicitly naming the local
source and target of `ofHom` and `transport`. All variables and universes are
explicitly bound, with `autoImplicit false`; no diagnostic commands remain.

## Second reading by Q98

This worker reread the source node and the final module clause by clause after the
compiler repair. The first check found that inferred endpoints could select global
pairs in component formulas; those endpoints are now explicit. Rechecked the fourth
conjunct's inverse/source and forward/target comparisons against the node's displayed
equation, the arbitrary-field quantifiers in the fourth and sixth conjuncts, and the
nonempty plus subsingleton assertion for I empty. No statement field was changed.
This is a worker self-check; the independent maintainer reading is performed after
delivery, as the dispatched brief specifies. No second agent was started.
