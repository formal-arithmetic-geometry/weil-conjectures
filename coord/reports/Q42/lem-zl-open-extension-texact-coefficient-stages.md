## Worker report

Module: `Sheaf.Paper.ZlOpenExtensionTExact`. Main declaration:
`WeilConjectures.ZlOpenTExact.openExtension_tExact`.
The item statement is unchanged. The only postponed assertions are `quasiCompact`
and the main theorem; both have the node's source and complete proof plans.
All definitions have actual data, including the natural realization and integral
cohomology isomorphism. `AllStages` and `RepresentativeIndependence` are explicit
propositions packaging this theorem's conclusions, not additional hypotheses.
`ScalarModel` packages the universal-counit normalization needed to compare the
existing independently chosen scalar models; it introduces no replacement scalar functor.

Hypotheses, one by one:

- Finite field, its algebraic closure, and characteristic: `D : FiniteFieldDatum.{u}`
  and its `D.k`, `D.p`.
- Prime different from the characteristic: `l : ℕ`, `[Fact l.Prime]`, `hl : l ≠ D.p`.
- Closure of Q_l: `Ω : Type v`, `[Field Ω]`, `[Algebra ℚ_[l] Ω]`,
  `[IsAlgClosure ℚ_[l] Ω]`. Its universe is independent of the scheme universe.
- Every finite E inside Ω: `E : Index l Ω`, using the recorded equivalent small
  field `Coefficient.{u} l Ω E` and its specified inclusion into larger fields.
  Valuation rings, uniformizers and all positive quotients are those of the
  imported actual compact-support and scalar constructions, never new parameters.
- Schemes: `U X : Scheme.{u}`, both `Over (Spec (.of D.k))`, and the two
  `LocallyOfFiniteType` and `QuasiCompact` structure-morphism instances. These
  are exactly finite type over k. The named `sepU`, `sepX` are explicitly included
  in the main theorem to retain both separatedness hypotheses.
- Morphism: `j : U ⟶ X`, `[IsOpenImmersion j]`, `[j.IsOver (Spec (.of D.k))]`.
  Quasi-compactness of j is a conclusion. Helper definitions have a local
  `[QuasiCompact j]` interface, discharged in the main theorem by `quasiCompact D j`.

Conclusion clauses, in order:

1. `IsNoetherian X ∧ QuasiCompact j` is the first part of the main theorem.
   The helper theorem retains the finite-type assumptions on X explicitly.
2. `integral` is an abbreviation of `sfCompactSupportFiniteIntegralFunctor` for
   `Compactification.ofIsOpenImmersion j`, the literal (j,id) compactification.
   It therefore retains the defining strict reduction tower and derived limit.
3. `identification` is a natural isomorphism, constructed from the inverse
   `sfQcqsCompactSupportRealization`, followed by `openIdentity`. Its target is
   `ordinaryOpen`, the exact termwise module-sheaf extension localized to D.
   The first factor is projection/Roos normalized, not an arbitrary objectwise iso.
4. `AllStages` requires `OpenAdjunctionNormalization` at each finite coefficient
   field. This package states both ordinary unit/counit equations under exactly
   `identification`, both strict-system realization equations copied from
   `Normalization.openSystemUnit` and `.openSystemCounit`, and the explicit mate
   formula for `openPull`. The latter is ordinary unit followed by ordinary
   pullback of `identification.inv`, followed by ordinary pullback of the realized
   counit. It therefore specifies the pullback comparison using the strict-realized
   adjunction; it cannot be varied independently.
5. The finite-limit and finite-colimit clauses give exactness of the ordinary
   sheaf functor `PurCompactSupport.openExtension`. The following clauses give
   `IsSfDerivedComplete` and the full intrinsic `sfIntegralConstructible` predicate
   on its output, including all reductions and the uniform reduction interval.
6. `integralCohomology E a` is an actual natural isomorphism of functors to module
   sheaves. It is H^a of `identification`, followed by Mathlib's exact-functor
   `mapDerivedCategoryHomologyFunctorIso` in the required direction. The formula
   applies to every integer a. The explicit Bool bound clause handles either
   vanishing half-line at every integer n; it assumes neither finite Tor over a
   quotient nor that cohomology commutes with reduction.
7. The existential integral t-structures have their le/ge classes equal to the
   recorded standard classes in every degree, and are bounded. `Comparisons`
   packages give exact triangulated functors, both-half t-exactness, the actual
   additive restriction of the functor to the heart, preservation of every short
   exact sequence there, and natural normalized truncation/cohomology isomorphisms.
   The rational and common-stage `Comparisons` use the recorded standard
   t-structures and the actual `S.system.Φ E` and `S.system.functor`.
   Inverting their `.q a` gives H^a J ≅ J H^a, the direction requested in the node.
8. `SquareCompatible` for `identification` compares the intrinsic and ambient
   cohomology constructions. The rationalization iso has identity components on
   the literal localized integral objects; its `SquareCompatible` clause gives
   compatibility with localization on all truncations and cohomology maps.
9. Integral scalar `Comparisons` and their square use the supplied actual
   `S.integralBeta h`. Scalar realization is constructed by the inverse of
   `sfIntegralOrdinaryComparison`, then the inverse universal scalar comparison.
   `ScalarModel.counit` fixes that comparison on every complex by the universal
   K-flat counit and the ordinary tensor identification. Thus it is not a freely
   chosen comparison. The scalar-identification equation explicitly identifies
   beta under d_E and d_L with `PurCompactSupport.openComparison` for the actual
   completed coefficient inclusion. That map is the mate of the open-unit square.
   `sfIntegralOrdinaryComparison` is already fixed by the strict completion-chain
   map on good complexes, including quotient projections and the zero shifted
   Roos coordinate. This is the requested completed scalar passage through Rlim.
10. The rational scalar, inclusion, tower, and enlargement `SquareCompatible` and
    `CompositeCompatible` clauses use precisely `S.system.β`, its stage inclusion,
    the recorded tensor associators and `transIso`. Their q equations give the
    finite-stage representatives of the common-stage cohomology comparisons and
    independence after further enlargement. Shift structures for transitions and
    inclusions are explicitly identified with the recorded canonical ones.
11. `RepresentativeIndependence` spells out identity and composition of comparison
    isomorphisms, equality after replacing two finite-field/arrow representatives
    by equal colimit arrows, and the comparison formula for arbitrary specified
    presentations α and β of the same object. No faithfulness of transitions or
    equality detection by individual reductions is assumed.

Dependency declarations used:

- Mathlib `AlgebraicGeometry.IsOpenImmersion`, `LocallyOfFiniteType`,
  `QuasiCompact`, `IsSeparated`, `IsNoetherian`, and `Scheme.Over`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and its full category.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: `Stage`, `Pair`, `StageHom`,
  `ofHom`, `stageSystem`, `integralTransition`, canonical shifts, and stage inclusions.
- `Sheaf.Paper.SfConstructibleHeart`: all three standard-class definitions,
  `sfRationalStandardTStructure`, `sfCommonStageStandardTStructure` and their hearts.
- `Sheaf.Paper.QcqsCompactSupportRealization`: `sfQcqsCompactSupportRealization`;
  its imports supply the actual finite integral/rational functors and coefficient action.
- `Sheaf.Paper.CompactSupportCoefficientAction`: `SfCompactSupportCoefficientAction`,
  its `integralBeta`, normalized finite mate specification, rational beta,
  `comparison`, and `representative`.
- `Sheaf.Paper.IntegralSupportFunctorNormalization`: `ordinaryOpen`, `openIdentity`,
  `ordinaryOpenPull`, `ordinaryOpenAdjunction`, `systemDirectId`.
- `Sheaf.Paper.SfScalarExtensionComposition`: `sfIntegralOrdinaryComparison`,
  with its complete good-complex quotient/Roos characterization.
- `Sheaf.Paper.BoundedConstructibleTower`: `pbcExtend`, `pbcDerivedExtend`,
  `pbcComplexCounit`; `IntegralScalarExtension`: the actual ordinary scalar functor.
- `Sheaf.Paper.IntegralCompactSupportCoefficientComparison`:
  `PurCompactSupport.completedChange`, `openComparison` (the normalized open-unit mate).
- `Sheaf.CategoryTheory.Triangulated.CoefficientStageDescent`: `Comparisons`,
  `SquareCompatible`, `CompositeCompatible`. These existing notions package the
  cohomology, heart exactness, and finite-stage coherence conclusions unchanged.
- Mathlib `Functor.mapDerivedCategoryHomologyFunctorIso` supplies the actual
  integral sheaf cohomology map, including its cycles and quotient normalization.

The three theorem-only stmt_deps from returned head 92dd127bd508 were replaced,
exactly as requested in H2, by the three definition owners listed below. The theorem
nodes remain proof dependencies wherever already required by the accepted proof.
Additional landed definition owners are cited for constructible pullback, universal
scalar counits, rational localization, PurCompactSupport data and the strict system
realization/counit. No existing dependency record or node statement was changed.

Edge cases checked: empty U; the identity open immersion; negative, zero and positive
cohomological degrees; either unbounded vanishing half-line independently; equality
E=L and chains of enlargements; arbitrary presentation isomorphisms α, β, including
nonidentity automorphisms; different arrow representatives in unrelated finite
fields; torsion inputs with nonflat cohomology over O_E/varpi^n. The formulations
retain all these cases. The site object/morphism and closure universes are unchanged.

Searches before writing:

- msearch leanfinder: “Open extension by zero on constructible adic derived categories
  is t exact and commutes with cohomology and coefficient extension”: eight unrelated
  general exact-functor, Ext and local-cohomology results; no match.
- msearch leansearch: “Extension by zero is t exact on constructible l adic derived
  categories”: eight general derived/Ext/short-complex results; no match.
- msearch loogle: `"mapDerivedCategory", "homologyFunctor"`: zero results.
- msearch grep Mathlib/CategoryTheory: `extensionByZero|extension_by_zero|lowerShriek`:
  no matching exact statement.
- rg upstream WeilConjectures and Sheaf for open-extension, t-exactness, compact-support,
  scalar and cohomology declarations, and upstream grep for the item id: no theorem
  stating the full item. Reused the canonical operation and comparison declarations
  listed above; did not duplicate a category, site, heart or scalar functor.

No STATEMENT-DISPUTED issue, statement correction, or dependency-module repair.
Three new definition ownership nodes are supplied under section 1(A).
All compilation uses the authorized scompile.py wrapper; no global build or direct
shared-repository write was performed.

## Second reading by Q42

A second self-review was performed against the node and the complete Lean file.
No independent second worker was started: the dispatcher's explicit instruction
forbids starting other agents. The maintainer's independent review is still required.

Found and corrected before delivery: Lean initially dropped finite-type assumptions
from the quasi-compactness helper; they are explicitly included now. The main theorem
also explicitly retains both separated structure morphisms. The integral functor is
the actual (j,id) construction, not a chosen functor with the same objects. The
cohomology comparison is a natural functor isomorphism, not an existence assertion
for individual K. Scalar maps are fixed by universal counits and the existing
completion-chain comparison, and their open-identification equation is explicit.
No rational Karoubi completion, extra finite-Tor assumption, faithful coefficient
transition, or reduction/cohomology interchange was introduced.


## Returned-delivery repair

Returned immutable head: `92dd127bd508`. Both required points are repaired.

- H2: `def-zl-ordinary-open-integral-operations`,
  `def-zl-normalized-integral-scalar-comparison`, and
  `def-zl-texact-comparison-data` own the plain definitions formerly cited only
  through theorem nodes. Each is `existing: true` on the exact published module;
  no copy or alternative implementation is introduced. Their signatures and
  docstrings were read in full. Definition-node precedent:
  `def-sf-finite-open-tensor-operations` owns unchanged definitions in a theorem
  module by exactly this existing-record method.
- H3: the old free adjunction/iso package is replaced by
  `OpenAdjunctionNormalization`. Its final two equations are the published
  `Normalization.openSystemUnit` and `Normalization.openSystemCounit`, specialized
  to this exact `(j,id)` operation and `coefficientPrimeUnit`. They compare actual
  whole strict systems through `integralComparisonPullbackCounit`,
  `compactOperationReduction`, `systemDirectId`, and
  `systemDerivedOpenAdjunction`. They are not equalities only after each separate
  finite evaluation. The realized unit/counit are fixed by this reconstruction
  normalization. The additional explicit `openPull.hom.app K` formula is their
  canonical right-adjoint mate of the fixed `identification`. Thus an arbitrary
  scalar-twisted pullback iso and its transported adjunction no longer suffice:
  their unit/counit must satisfy the specified strict-system equations. The
  ordinary transport equations remain, asserting the requested compatibility
  rather than defining an otherwise unconstrained adjunction.

The helper proposition only groups this item's adjunction clause; it adds no
existence theorem or independent mathematical hypothesis. Splitting it out avoids
repeated elaboration of the same coefficient-stage expression. All helper variables
and universes are explicitly bound. All previous edge cases still apply: for the
identity open both comparisons use the identity-normalized system adjunction;
for the empty open and zero object the same unit/counit and mate formulas remain
well typed. Torsion objects are still allowed and no termwise reduction/homology
commutation is assumed. Main theorem signature and node statement are unchanged.

Repair self-review: read the new definition nodes with their source declarations,
and compared all five adjunction equations against the source interface. The
maintainer's H11 advisory remains accurate: this is self-review, not an independent
second agent. No other agent was started, as explicitly required by the dispatcher.

## New nodes

`def-zl-ordinary-open-integral-operations` owns the existing `ordinaryOpenPull`,
`ordinaryOpenAdjunction`, and `systemDirectId` in
`Sheaf.Paper.IntegralSupportFunctorNormalization`. Source: blueprint Part 2 and the
published declaration docstrings (Stacks 03DI, 03DJ, 015F, 03D8, 0941). These are the actual completed-ring pullback, derived open adjunction and
right-adjoint uniqueness system identity comparison. The four other ordinary-open
and identity definitions are owned by `def-zl-ordinary-open-support-normalization`
and are cited from that owner. Its dependencies cite the actual coefficient,
open-adjunction, pro-etale-operation and system-realization owners. DAG grep and
blueprint search found no definition owner. LeanSearch gives general pullback
adjunctions, Loogle general adjunction APIs, Mathlib grep none for these names;
upstream grep none; Sheaf grep finds these exact constructions. Reused them.

`def-zl-normalized-integral-scalar-comparison` owns the existing
`sfIntegralOrdinaryComparison` in `Sheaf.Paper.SfScalarExtensionComposition`.
Source: the quotient-completion argument in blueprint order 1828 and its published
docstring. Its map is uniquely determined on all good complexes by the actual
completion chain map, including zero homotopy coordinate. LeanSearch/LeanFinder
return general tensor/local-cohomology/cotangent APIs, Loogle no exact scalar
comparison, Mathlib/upstream grep no match. Sheaf grep finds the unique existing
construction, but no definition node owns it. Reused it without a new choice.

`def-zl-texact-comparison-data` owns `cohomology`, `heartRestriction`, `Comparisons`,
`CompositeCompatible`, and `SquareCompatible` in
`Sheaf.CategoryTheory.Triangulated.CoefficientStageDescent`. Source: BBD 1.3.3,
1.3.6, 1.3.17 and the explicit comparison argument used in blueprint Part 2.
The full package includes exactness of the heart restriction, both normalized
unique truncation comparisons, their specified shifted cohomology composite, and
all three explicit compatibility equations. LeanSearch/Loogle return only general
truncation functors. Mathlib/upstream grep finds no such package; Sheaf finds the
exact existing definitions. DAG grep and blueprint search find no definition owner.
Every new node records the actual search queries and their returned hits.


Validation of this repair: `scompile.py` compiled the delivered module in both
sandbox and library modes with no errors and no warnings (library 53.9 seconds).
`deliver2.py --no-push` then compiled the delivery and all existing-declaration
checks and reported `OK (dry run)` for commit `ca617f3e937`, with all preflight
checks passing. No build limit was changed. The delivery wrapper rebased the
packet on current published main; comparison with the current item shows only
`lean` and `stmt_deps` change, besides the new ownership nodes and module/report.


## Repair of returned head 8914e01fd1fd

The independent review accepted the preceding H2/H3 repair and returned H4/H12
for overlapping ownership with Q53. The new node
`def-zl-ordinary-open-integral-operations` is now restricted, in both its statement
and `lean.declarations`, to `ordinaryOpenPull`, `ordinaryOpenAdjunction` and
`systemDirectId`. Its primary declaration and verbatim recorded signature are now
`ordinaryOpenPull`. Its statement cites
`def-zl-ordinary-open-support-normalization`, which owns `ordinaryOpen`,
`identityModuleImage`, `identityImage` and `openIdentity`; the item also adds that
owner to `stmt_deps`. None of these four declarations is re-owned in this packet.
This is the exact ownership split requested by the reviewer, rather than a rebase
or unchanged re-push. The Lean module is byte-for-byte unchanged from the accepted
8914 adjunction repair; its hypotheses, clauses and edge cases remain as mapped
above. The declarations and docstrings at IntegralSupportFunctorNormalization
lines 155–178 were reread to verify the three retained definitions. No mathematical
statement correction or new comparison construction is involved.

The repair compile is clean. The first new dry run confirmed the only substantive
preflight failures are the not-yet-landed Q53 owner node. It also reported a
signature-format advisory for `sfIntegralOrdinaryComparison`: the record now
starts at the `def` keyword, as the current preflight extracts it, omitting the
`noncomputable` modifier. This changes no declaration or type.

Q53's `def-zl-ordinary-open-support-normalization` is now published on the live
base. Its existing record was read in full: it owns exactly the four declarations
removed from our owner record, plus `identityModuleImage_existsUnique`. Its primary
`openIdentity` signature and section-normalized construction agree with our uses.
The three retained declarations are disjoint from its ownership list. The packet
can now rebase through the normal delivery wrapper without a missing dependency.
