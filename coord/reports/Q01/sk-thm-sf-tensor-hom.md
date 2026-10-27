## Worker report

Item: `sk-thm-sf-tensor-hom`, group Q01, stage 2, 2026-10-22.
Delivery: `Sheaf.Paper.TensorHomExchange`, primary declaration
`WeilConjectures.ConstructibleTensorHom.exists_family`.

The theorem states existence of the canonical joint natural exchange family for the
published, unconditional constructible exceptional adjoint. This packet repairs
H3 of the immutable returned head `4becf9ec5517`: `Family.canonical` now fixes the
forward exchange by the actual projection map and adjunction counits. Its only
postponed proof is the item's theorem. All other declarations in the module are definitions, instances
by case analysis on the two recorded ring stages, or structures packaging the
clauses of this assertion. No definition has postponed data. The theorem docstring
follows all fifteen proof steps, including the finite-Tor Yoneda domain,
completed tensor at integral coefficients, retained ramified levels, and descent.

### Hypotheses and objects

- The source's fixed finite field is `D : FiniteFieldDatum.{u}`, with field `D.k`
  and characteristic prime `D.p`. The coefficient prime is `l : ℕ` with
  `[Fact l.Prime]` and `hl : l ≠ D.p`. These are the standing coefficient/base
  hypotheses of the blueprint operations. The algebraic closure of the coefficient
  field is `Ω : Type u`, `[Field Ω]`, `[Algebra (Padic l) Ω]` and
  `[IsAlgClosure (Padic l) Ω]`. It indexes the algebraically closed coefficient
  regime; the finite and integral components also quantify over all finite
  extension fields, independently of a choice of embedding into Ω.
- `X Y : Scheme.{u}` carry `[X.Over (Spec (.of D.k))]` and the analogous instance
  for Y. Finite type over k is the pair `LocallyOfFiniteType` and `QuasiCompact`
  on each structure morphism. Neither structure morphism is required separated.
- The given morphism is `f : X ⟶ Y`, with `[f.IsOver (Spec (.of D.k))]`,
  `[IsSeparated f]`, `[LocallyOfFiniteType f]`, and `[QuasiCompact f]`.
- `f^!` is `R.ring.operation c s |>.G`, where the normalized published
  `ConstructibleExceptionalCoefficients.System` is **produced** by the theorem's
  existential conclusion. It is not an extra hypothesis. The compact-support
  functor is the same operation's `F`. The System includes the recorded
  finite-etale identification and the normalized integral, rational, common-stage
  and compactification-refinement comparisons. In particular this statement
  assumes no ambient pro-etale exceptional right adjoint.
- `∀ c : Compactification f` chooses a model of the actual compact-support
  construction for a separated finite-type f, not an admissibility datum. The
  output System is shared before quantifying over compactifications.
- `M` and `N` range over the recorded full constructible finite-Tor categories
  `C l Ω X s` and `C l Ω Y s`. Their joint domain is `Pairs`, namely
  `(C l Ω X s)ᵒᵖ × C l Ω Y s`. The opposite factor records contravariance in M.
  For ring coefficients these are exactly the recorded finite/integral
  subcategories. The rational category uses raw scalar localization and the
  algebraically closed category uses the existing common-field construction.
  No perfectness or site-perfectness of M is required.

### Each conclusion clause

1. **The displayed source:** `source l Ω f s A` is the composite of the actual
   full inclusion on M, the actual exceptional operation `A.G` followed by the
   full inclusion on N, the recorded `derivedInternalHomOfUniverses`, and
   `PurCompactSupport.push (s.coefficients l) f`. Thus it is
   `Rf_* RHom_X(M,f^!N)`, with ordinary rather than exceptional direct image.
   The completed integral coefficient sheaf is retained; no constant-ring
   replacement is made.
2. **The displayed target:** `target l Ω s A` is the actual internal Hom applied
   to `(A.F M,N)` after their full inclusions. Thus it is
   `RHom_Y(Rf_! M,N)` with the same normalized constructible operations.
3. **Isomorphism and ambient D⁺:** `RingExchange.iso` is a `NatIso` between those
   two actual ambient bifunctors, not only an isomorphism of cohomology groups.
   `RingExchange.boundedBelow` states, for each pair, existence of an integer a
   for which **both actual endpoints** satisfy `DerivedCategory.IsGE a`.
   Consequently the ambient isomorphism lies in the full bounded-below derived
   subcategory, i.e. D⁺. This avoids replacing D⁺ by an unrestricted ambient
   category without a boundedness assertion. Rational and common-stage Hom
   domains, functors, and outputs already lie in the recorded bounded
   constructible categories. `IntegralLift` supplies the full integral
   constructible realization needed to localize the same exchange.
4. **Naturality in M and N:** all exchanges (`RingExchange.iso`,
   `IntegralLift.iso`, `RationalDescent.iso`, `Family.commonIso`) are natural
   isomorphisms of the joint pair functors. This includes arbitrary localized
   rational arrows and common-stage arrows, not just arrows from integral
   lattices or pairs at a single field of definition.
5. **Finite reduction and finite/integral scalar extension:** `Family.coefficient`
   is the commuting square for every recorded `Allowed` coefficient change.
   This includes finite quotient maps, completed-to-finite reduction, retained
   ramified levels, completed scalar inclusion, identities and composites.
   `sourceChange` uses the actual ordinary-direct-image counit mate, the
   evaluation-transpose scalar-Hom arrow, and the normalized exceptional
   comparison. `targetChange` uses the same scalar-Hom arrow and the inverse
   compact-support comparison in the contravariant argument. These arrows are
   definitions, not arbitrary supplied comparison maps.
6. **Scalar-Hom normalization:** `ScalarModel` reuses the existing
   `ScalarHomModels` and `ScalarHomTensorComparison` records. They retain the
   K-flat/pure-generator normalization. `scalarModelComparison` is the unique
   left-adjoint comparison to the actual `pbcDerivedExtend` via the identical
   restriction functor. `homChange` is explicitly the closed-adjunction
   transpose of scalar-extended evaluation with the tensor comparison.
   `Family.coefficient` holds for every such normalized model, so choosing an
   unrelated comparison cannot make the square vacuous. The existence theorem
   `scalarInternalHomAdjunction_exists` supplies these models for the actual
   maps; no flatness or finite-free hypothesis is added to the assertion.
7. **Raw rationalization:** `IntegralLift.left_eq/right_eq` are equalities of
   functors after the actual full inclusion, fixing both objects and arrows.
   Its `realization` identifies the integral exchange arrow with the ambient
   one. `RationalDescent.left/right` compare localization of these composites
   with the actual rational Hom composites; `normalization` says localization
   of the same integral exchange equals the rational exchange. The rational
   Hom functors are the published `rationalDerivedInternalHom`, on their
   published constructibility domains. The ordinary direct-image functor is
   determined as right adjoint to the actual `rationalDerivedPullback`;
   that adjunction is output data, not a hypothesis on the morphism.
8. **Rational field extension:** `Family.rationalCoefficient` is the explicit
   square for every finite-extension algebra map E → L. Its source arrow uses
   the counit mate `rationalDirectChange` of the actual
   `rationalPullbackScalarComparison`, followed by the actual normalized
   `rationalHomScalarComparison` and exceptional mate. Its target arrow uses
   the actual rational Hom comparison and inverse compact-support comparison.
9. **Algebraically closed coefficients:** `commonSource/commonTarget` use the
   published `commonStageDerivedInternalHom` and the same System's common-stage
   operations. `Family.commonOrdinary` specifies the ordinary direct image by
   adjunction with the actual `commonStageDerivedPullback`.
   `commonLeftDomain/commonRightDomain` assert the genuine Hom domains.
   `commonLeft/commonRight` realize the two common-stage composites at every
   finite field of definition. `commonNormalization` says the common-stage
   exchange restricts to the same rational exchange for **every** index i.
   Thus the isomorphism descends through common fields, rather than selecting
   one favored presentation. No idempotent completion is substituted.
10. **Shifts:** `RingExchange.firstShift/secondShift` are the commuting squares
    for arbitrary integers a,b, with sign -a in the first input and +b in the
    second. The four `leftFirst/rightFirst/leftSecond/rightSecond` fields fix
    the shift arrows to the published signed Hom shifts and actual direct,
    exceptional, compact-support and inclusion shift comparisons.
    `ShiftExchange` states both squares functorially; `ShiftNormalization`
    carries the same squares through integral inclusion, raw localization,
    finite rational extension and every common-stage inclusion. Thus shifting
    both inputs gives b-a. There is no assumed independent arbitrary sign.

11. **Canonical map, including its sign:** `Family.canonical s` asserts
    `CanonicalExchange l Ω c s A (R.ring.left c s) (ring s).iso`. The explicit
    equation is detailed below. The integral `realization`, rational
    `normalization`, and `commonNormalization` clauses identify their arrows
    with this same fixed map.

All variables and universes are explicitly bound; `autoImplicit` is false.
The small pro-etale site retains object universe u+1 and morphism universe u.
`siteSmall` merely supplies the canonical essentially-small-self instance at
that size. It does not identify the two universes or restrict the sites.

### Dependency declarations used

The original dependency `sk-def-sf-operations` has the Q02 binding
`Sheaf.Paper.SixFunctorOperationDatum`, `WeilConjectures.SixFunctorOperationDatum`.
That module is imported publicly to retain this owner of the six operations.
The statement uses the published unconditional System directly, without an
operation-datum hypothesis. On the finite-Tor subcategories its adjoint agrees
with the datum's adjoint via the unique right-adjoint comparison preserving the
adjunction, after the recorded compact-support realizations. Specifically,
`SixFunctorFiniteOperations.finiteExceptional` and `RingSystem.finiteRight`
both realize the existing `ProEtale.sfFiniteExceptional`; their support
realizations both realize the same compactification functor. At integral,
rational and common stages the specified normalized-system construction,
raw localization and common-stage comparisons give the corresponding agreement.
This is agreement through the prescribed adjoint comparison, not a definitional
equality of independently packaged records. The import is therefore a source
interface import; no arbitrary operation datum is substituted for the System.

Already-landed statement dependencies added to the item, with no changes to
those dependency nodes:

- `def-weil-exceptional-inverse-image`:
  `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`,
  `WeilConjectures.ConstructibleExceptionalCoefficients.System`, and its
  `Stage`, `C`, `Operation`, `RingStage`, `Allowed`, `Scalar`,
  `FieldComparison`, `RingSystem`, `FieldSystem`, `CommonSystem` declarations.
  The unconditional `exists_system` is also the existing proof prerequisite
  `lem-sf-constructible-exceptional-adjunction-coefficients`.
- `def-weil-derived-pullback-tensor-hom`:
  `Sheaf.Paper.DerivedPullbackTensorHom`, actual
  `rationalDerivedPullback`, `rationalDerivedInternalHom`,
  `constructibleRationalHomPairs`, `rationalHomScalarComparison`,
  `rationalPullbackScalarComparison`, `commonStageDerivedPullback`,
  `commonStageHomPairs`, and `commonStageDerivedInternalHom`.
- `def-sfb-scalar-hom-comparison-data`:
  `Sheaf.Algebra.Homology.ScalarInternalHomData`,
  `CategoryTheory.ScalarHomModels` and `ScalarHomTensorComparison`, with
  `SheafOfModules.ScalarDerivedPair` and its normalized scalar adjunction.
- `def-weil-finite-tor-amplitude`:
  `Sheaf.Paper.FiniteTorAmplitudeSites`, the restored pro-etale
  `finiteTorConstructible` and integral/field categories, not just the newer
  ordinary-etale predicate.
- `def-pur-integral-compact-support-coefficient-data`:
  `Sheaf.Paper.IntegralCompactSupportCoefficientData`,
  `WeilConjectures.PurCompactSupport.Change`, `finite`, `completed`, `push`,
  and its actual coefficient comparison API. The underlying actual
  `pbcDerivedExtend` and its adjunction are in `AlgebraicGeometry.Scheme`.
- `def-exchange-projection`: `Sheaf.Paper.ExchangeProjectionSuppliedDomains`,
  `CategoryTheory.SuppliedExchangeProjection.compactificationProjectionFromData`.
  `PurCompactSupport.projectionMap` uses this precise proper-counit/open composite.
- `def-coef-ringed-tensor-hom-model`:
  `Sheaf.Paper.CoefficientRingedTensorHomModel`, `CoefficientClosedStructure`,
  `CoefficientTensorModels`, `transpose`, and the fixed `uncurry_model`.

The existing theorem `CategoryTheory.scalarInternalHomAdjunction_exists` in
`Sheaf.Algebra.Homology.ScalarInternalHomAdjunction` witnesses inhabitance of
the scalar models. It is not an added statement dependency or hypothesis;
the statement uses only the owning definition node ScalarInternalHomData.

Additional exact interfaces used: `derivedInternalHomOfUniverses` and
`RingedHomUniverses.sourceShift/homCommShift` in the publicly imported ringed
Hom modules; the published closed tensor adjunction for evaluation transpose;
Mathlib `DerivedCategory.IsGE` for D⁺; Mathlib `Adjunction.leftAdjointUniq`
for the unique normalized scalar realization. Stated proof-dependency modules
are imported ordinarily, as required by the stage-2 contract.

### Edge cases checked before stating

These are mathematical/interface checks, not newly proved tests.

- n=1 is included; `RingStage.finite` uses `PositiveLevel`, so the source does
  not gain the extraneous n=0 quotient. Integral reduction quantifies over all
  positive levels.
- Empty schemes and zero inputs remain allowed: there are no points or
  nonemptiness assumptions, and the proof's empty-cover case is the zero
  object. Arbitrary shifts include zero and negative integers.
- The identity map and proper maps are included. Nonproper separated maps
  still use ordinary Rf_* on the left and compact-support Rf_! on the right.
- X and Y need not be separated over k. No global affine-cover separatedness
  is added to the Lean binders; only f is separated.
- Finite-Tor constructible inputs need not be perfect as site objects.
  The theorem does not assume an ambient exceptional adjoint, including in
  examples where an ambient adjoint would not preserve boundedness.
- Ramified scalar extension retains the en level in the recorded Allowed
  comparison before quotienting; the statement does not replace it by n.
  Identity and composed coefficient changes are included.
- Integral coefficients use the completed ring sheaf. Rationalization is raw
  localization; rational morphisms are not restricted to integral arrows.
- At algebraically closed coefficients, the two inputs may have different
  initial fields of definition. The actual common-stage construction takes a
  common enlargement; normalization quantifies over every finite index.
- For the sign ambiguity, take an identity morphism of a geometric point and
  unit inputs at integral coefficients. The fixed test is the identity after
  the specified tensor/unit comparisons; negating the exchange changes it to
  minus identity, including for l=2 since the integral coefficient ring has
  characteristic zero. At finite characteristic two the sign is already equal,
  but the same equation still fixes the map. The zero-object case imposes the
  unique zero arrow without imposing any nonzero-object hypothesis.
- Residue invertibility witnesses required by the rational/common APIs are
  output fields of `Family`, derivable from the fixed l ≠ char(k), shared by
  the relevant adjunctions. They are not new hypotheses on X or Y.

### Searches for reuse

Searches used `/home/ubuntu/weil-launcher-all/batch2/msearch.py Q01
sk-thm-sf-tensor-hom` with the following tool/query pairs, plus direct rg in the
named source directories. Tool searches are against the Mathlib index, so
project-only declaration names can correctly return unknown identifiers.

- leanfinder: "derived direct image internal Hom exceptional inverse image
  tensor Hom duality separated finite type constructible sheaves" — eight
  ordinary pullback/sheaf-adjunction results; no exact all-stage theorem.
- loogle: "AlgebraicGeometry.Etale.derivedHom,
  AlgebraicGeometry.Etale.rightDerivedUpperShriek" — zero matches/unknown
  Mathlib identifier. The upstream theorem was inspected directly.
- grep: "derivedHom.*[Ll]owerShriek|[Tt]ensor[Hh]om.*[Ee]xchange" in
  CategoryTheory — no exact theorem, only generic tensor-Hom material.
- leansearch: "derived pushforward internal Hom exceptional inverse image
  canonical exchange constructible sheaves" — eight ordinary sheaf-pushforward
  results, no exact theorem.
- rg and blueprint-id search in `lean/WeilConjectures` found the finite-etale
  tensor-Hom theorem. Its coefficient scope and datum interface are not the
  complete assertion here. rg in `lean/Sheaf` located the actual System and
  coefficient-stage constructions reused above.
- leansearch: "canonical scalar extension internal Hom comparison transpose
  evaluation arbitrary ring sheaf map" — eight ordinary ModuleCat scalar
  adjunction results.
- loogle: "derivedInternalHomOfUniverses, pbcDerivedExtend" — zero
  matches/unknown project identifiers in Mathlib.
- grep: "homChange|scalarHomComparison" in CategoryTheory — zero matches.
  `tools/blueprint_refs.py search 'scalar Hom comparison'` found zero entries
  by that phrase. Subsequent rg of project sources and DAG nodes located the
  **existing** ScalarInternalHomData/ScalarInternalHomAdjunction declarations
  and their two genuine DAG nodes. They were reused; no duplicate generic
  scalar model notion or new definition node was created.

The repair searches repeated leanfinder with "canonical tensor Hom exchange
characterized by projection formula and exceptional adjunction counit" (eight
rigid-category tensor-Hom bijections, no exact exchange), loogle with
"Adjunction.homEquiv, CoefficientClosedStructure.transpose" (zero hits, unknown
Mathlib identifier), and grep with
"tensor.*[Hh]om.*[Ee]xchange|canonical.*[Ee]xchange" in CategoryTheory (twelve
unrelated tensor/whiskering identities). Direct rg in the upstream SixFunctors,
project Paper and Algebra/Homology directories found the existing normalized
closed models and compact-support projection interfaces reused here; it found
no existing all-stage normalization of this exchange. The two new helper
declarations belong to this item's canonical-map assertion, rather than to a
new independent notion. They have source/blueprint docstrings and are listed
in `lean.declarations`.

There is no mathematical statement correction, disputed statement, new node,
or dependency module. Only the item's `lean` and additions of seven
already-landed definition prerequisites to `stmt_deps` differ from the current
main node. No upstream Lean source or dependency node is edited.

## Repair of return H3

The return identifies a real defect: the earlier shift and coefficient squares
were homogeneous in the exchange and therefore allowed simultaneous negation.
The repair is the new `CanonicalExchange` predicate and `Family.canonical` field.
For fixed ring stage, compactification, M, N, and every finite-Tor constructible
Yoneda test L, let t be ANY ambient arrow

    pull(L) tensor M -> G(N).

The equation says that the following two arrows from L tensor F(M) to N agree.
On the left, curry t by the normalized X tensor-Hom adjunction, apply the actual
`proEtaleRingDerivedAdjunction.homEquiv`, postcompose with `iso.hom.app (op M,N)`,
and uncurry by the normalized Y tensor-Hom adjunction. On the right, apply the
System's `left` realization to F(M), interchange the two tensor factors by the
normalized signed symmetry, apply the actual `PurCompactSupport.projectionMap`,
then compact support of the X symmetry followed by t, then the inverse `left`
realization at G(N), and finally the inclusion of `A.adjunction.counit.app N`.
Thus this is exactly PF followed by compact support of evaluation/test map and
the exceptional counit, with the ordinary counit built into its transpose.
Equivalently, moving PF to the other side uses PF inverse, yielding precisely
the five Hom bijections in steps 7--9. Taking t to be evaluation after the
ordinary counit gives the reviewer's displayed normalization.

`tensorPresentation` only restricts `CoefficientTensorModels.comparison` along
the existing inclusion of flat-term K-flat representatives. It defines real
data by whiskering; it introduces neither another tensor nor an auxiliary
postponed theorem. `CoefficientTensorModels.uncurry_model` fixes the closed
adjunctions to actual evaluation on pure tensors. The existing
`RingedDerivedTensorCoherence` fixes the symmetries to their signed swaps.
The equation is required for EVERY such normalized closed model, coherence and
intermediate tensor presentation, so no rescaling of an unrelated comparison
can absorb a rescaling of the exchange. These normalized models are inhabited
by `ringedDerived_closed_symmetric_monoidal`; intermediate tensor presentations
are the actual flat K-flat presentations. The coefficient pullback-composition
equality is explicitly supplied by an existential proof inside
`CanonicalExchange`, so the normalization is not conditional on an unprovided
composition identification. This proof is used directly in the projection map.

At integral coefficients ordinary tensors and pullbacks are used only before
mapping into derived-complete targets. By the completion reflector universal
property from source step 2, those Hom sets are the Hom sets out of the completed
tensor/pullback; the projection/counit equation is unchanged after the canonical
completion units. In particular the condition never asks for an ordinary tensor
to have a chosen finite-Tor constructible lift. This retains the full completed
coefficient statement rather than adding a site-perfectness hypothesis.

For every L the two successive left-side bijections allow every map
L -> source(M,N); the equation fixes its composite with the exchange. The target
and, through the exchange, the source lie in the full finite-Tor category by the
preservation results in steps 3--6. Yoneda there therefore fixes the exchange
itself. Its negative can obey the equation only where it is the same map. The
higher coefficient maps are then fixed by the existing `IntegralLift.realization`,
`RationalDescent.normalization`, and `Family.commonNormalization` equations.

Added `def-exchange-projection` to `stmt_deps` as requested by the return, with
its recorded module now a public import. Also added the existing normalized
closed-model definition owner `def-coef-ringed-tensor-hom-model`, whose recorded
module is publicly imported. Retained the original five added definition owners.
The informal node statement already requires the canonical map and is unchanged;
no `statement_change` is appropriate. The two consumers named in the return
remain valid: `sk-thm-sf-kunneth-verdier` uses precisely this evaluation-normalized
exchange for the beta-evaluation equality, and `sk-thm-sf-verdier-exchange` defines
epsilon by the inverse of precisely this exchange at the dualizing object.
Neither consumer is edited. The advisory concerning `SixFunctorOperationDatum`
is addressed in the dependency paragraph above.

## Second reading by Q01

Reopened the source statement, saved node, current main node and final module.
The hypotheses remain the fixed algebraic finite-field datum, l different from
its characteristic, finite-type X and Y, and separated finite-type f; only f,
not the two structure maps, is required separated. M and N still range over
`C` and the unconditional `System` is still output before the compactification
quantifier. The two bifunctors are still actual ordinary pushforward of internal
Hom and internal Hom from the System's compact-support functor. `boundedBelow`
still gives one lower bound for both endpoints, and each isomorphism is natural
in the joint pair category. The finite/integral scalar square, rational square,
raw localization and every common-stage normalization are unchanged. The two
shift signs remain minus a and plus b; their actual structural comparisons and
coefficient compatibility squares are unchanged.

The changed clause is canonicity: the new equation fixes `ring s`.iso through the
specific projection owner and the System's own adjunction counit, with normalized
closed evaluation and signed symmetries. It is not another free NatIso or an
existence-only normalization map. I checked both directions of the Hom chain,
including PF inverse, and the completion-reflector interpretation. The integral,
rational and common maps stay tied to that fixed ring exchange by the existing
realization equations. I also checked empty schemes, zero inputs, identity and
proper maps, l=2, ramified levels, arbitrary shifts, and different fields of
definition: the new equation drops none of them and adds no input hypothesis.

Compared the packet with current main: only `lean` and the seven existing
definition additions to `stmt_deps` differ. The saved returned module was retained
and amended with two helpers and one structure field; it was not replaced by
another formulation of the theorem. The theorem signature is verbatim in
`lean.statement`, with the current UTC date. All Lean lines fit 100 characters,
variables and universes are explicit, and the only postponed proof remains
`exists_family`. No tool, upstream file, target, consumer or dependency node is
changed. The historical route-pivot import-ownership refusal was resolved before
this repair; the required initial dry run passed at `e91b361ba62`.

### Validation

The first repaired `scompile.py` check completed with no diagnostics: sandbox
53.0 seconds, library 43.2 seconds. After making coefficient composition an
explicit existential proof in the normalization, the final `scompile.py` check
also passed without diagnostics: sandbox 32.4 seconds, library 34.5 seconds.
Both were within the prescribed 60-second per-file limit. The only `sorry`
is the theorem being stated. The final prescribed dry run passed:
`OK (dry run): commit 31a5c4be2f3 passes the preflight and compiles; nothing pushed`.
The final self-check found no further code or node changes needed. Delivery is
performed with the same wrapper after recording this validation result.
