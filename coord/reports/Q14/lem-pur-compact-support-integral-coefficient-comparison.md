## Worker report

The module `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` states the
canonical integral coefficient comparison and its coherence clauses. Its primary
statement is `WeilConjectures.PurCompactSupport.integralCoefficientComparison`;
`comparisonIso` packages the ambient natural isomorphism on the uniform finite-Tor
subcategory; `recordedComparisonIso` transports it to the recorded compact-support
functors with their fixed Roos projections. Proofs are postponed, with source/proof docstrings. Definitions contain
actual constructions or choices uniquely characterized by their displayed normalization.
There is no statement correction and no disputed statement.

Clause-by-clause correspondence (names below are in `WeilConjectures.PurCompactSupport`):

- Global finite-field conventions are the actual `FiniteFieldDatum D`; `hl : l ≠ D.p`,
  `[Fact l.Prime]`, fields `E,F`, their `Algebra ℚ_[l]` and finite-dimensional instances,
  and the actual embedding `i : E →ₐ[ℚ_[l]] F` express the coefficient hypotheses.
  `coefficientPrimeUnit` supplies invertibility in the geometric field from these
  hypotheses; no extra invertibility assumption is imposed.
- `X.Over D.k`, `Y.Over D.k`, separation, locally finite type and quasi-compactness of
  the structure morphisms express separated finite-type k-schemes. `f.IsOver D.k`,
  `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f` express the hypotheses on f.
  They are explicitly included in the finite-Tor-domain theorems. There is no smoothness,
  purity, equidimensionality, or extra coefficient-flatness hypothesis.
- `completed l E` and `completed l F` use the recorded unrestricted completed integral
  CommRing sheaves. The scheme universe is u, site objects u+1 and site arrows u;
  coefficient sheaves take values in `CommRingCat.{u+1}`. No site universes are identified.
  `completedChange` uses the existing residue-normalized `completedCoefficientMap`.
  `pbcDerivedExtend` is ordinary derived scalar extension along this actual map.
- `finiteTorConstructibleIntegral` is the recorded complete constructible predicate
  with one uniform Tor interval. The main theorem proves preservation of this domain,
  completeness/constructibility of both compact-support values, and invertibility of
  the actual component. `image R c` is separately derived proper direct image after
  exact intrinsic extension by zero. The final object clause alone does not normalize that identification. The repair
  adds `recordedSupport`, using the published `sfCompactSupportFiniteIntegralFunctor`,
  and the natural `recordedIdentification`, fixed by `IsRecordedIdentification`
  against `sfCompactSupportFiniteReductionIso`. `recordedComparisonIso` is the
  conjugate of `comparisonIso` by these two normalized natural identifications. Naturality is built into `comparison`, and
  `comparisonOnFiniteTor_isIso`/`comparisonIso` restrict and package that transformation.
  Thus the source is exactly C_Y(P_E M) and target P_F(C_X M).
- `Ramification l E F i e` is equality of the extended principal ideal with the eth
  target uniformizer ideal; `hepos : 1 ≤ e` is separate. It never equates uniformizers.
  `finite n hn`, `ramifiedMap`, `ramifiedSheafMap`, and `finiteChange` construct
  A_E,n → A_F,en at every n≥1 from the actual integer inclusion, using a quotient lift
  whose kernel condition is the named theorem `ramifiedKernel`.
- `properComparison` is the normalized coefficient-adjunction mate of proper-image
  scalar restriction. `openComparison` is the open-unit normalized scalar mate;
  `openComparison_isIso` states its invertibility. `comparison_factorization` gives
  the required ordered composite: proper tensor map first, then proper image of the
  open tensor identification. It applies in particular to each `finiteChange`.
  `finiteComparison_isIso` gives finite-free invertibility on arbitrary finite-level
  inputs, without purity. Its proof uses a basis only to test the canonical maps.
- `projection` and `reduction` are ordinary derived tensor along the existing completed
  projections. `ramified_reduction_square` fixes the actual coefficient square.
  `ReductionComparisonEquation`/`comparison_reduction` give equality of its two
  morphism composites under `tensorSquare`, including both canonical compact-support
  reduction maps. `reductionComparison_isIso` makes those identifications invertible
  on the stated finite-Tor domain. Consequently reduction of c is the specified finite
  map, rather than merely some isomorphism between its endpoints.
- `finiteQuotient` reindexes the existing `compactSupportLevelSheafQuotient`; it is not
  a new quotient construction. `ramified_quotient_square` and `comparison_quotients`
  express compatibility with every further quotient, including equal levels, with
  ordinary tensor associativity and the actual compact-support quotient comparisons.
- `comparison_strict_towers` supplies flat K-flat representatives, a strict map v,
  its levelwise transition equality, and an equality identifying c with the induced
  Roos map. The identity scalar tower is the recorded `integralScalarTowerFunctor`
  for the identity extension, and its augmentation is `completedScalarIdentityUnit`.
  The retained tower is precisely arithmetic restriction with positive exponents
  e(n+1). `IsCofinalRoosMap` specifies BOTH signed cone coordinates: selection on the
  unshifted coordinate and the finite block sum on the shifted coordinate; the
  cofinal maps are quasi-isomorphisms. The new epsilon clauses identify each retained evaluation with
  `finiteTensorSource` and `finiteTensorTarget` after actual coefficient restriction.
  They normalize both comparisons by `finiteSourceProjection` and
  `finiteTargetProjection`, which are explicitly constructed from scalar units,
  `tensorSquare`, and the compact-support reduction mate. The final evaluation
  equation identifies the map of this same strict tower with `finiteTensorMap`:
  proper mate followed by proper image of the open identification. The existing
  all-transition equation and full Roos equation use that same chain map v.
  These assertions precede the inverse-limit construction and do not infer
  equality of integral maps from equality of their reductions.
- `ProjectionComparisonEquation`/`comparison_projection` give the complete projection
  square. Its tensor maps are `scalarTensor`, normalized on flat K-flat pure tensors;
  `scalarPull` is the canonical left-adjoint comparison. `projectionMap` uses the
  dependency's actual supplied-domain counit projection followed by open projection,
  with `ProjectionComparisons` uniquely fixed componentwise by canonical maps.
  `projectionDomain_complete` identifies these ordinary tensor presentations with
  completed tensor on the stated domain, using the completion-reflector unit.
- `scalarCommShift` is uniquely specified by the scalar adjunction counit, and
  `imageCommShift` is the inherited proper/open shift structure.
  `comparison_commShift` asserts commutation with every integer shift.
- For a genuine compactification refinement r, `refinementProperOpen` is the unique
  proper-open comparison normalized by the open unit and proper counit, including the
  open triangle. `refinementComparison` uses inverse proper composition and inverse
  proper-open comparison, in that order. `comparison_refinement` gives the coefficient
  square. `refinementComparison_coherence` gives identity and composition; hence the
  common-refinement identifications make c independent of compactification.
- `comparison_identity` with `completedMap_identity` states the identity-field clause
  under the ordinary tensor multiplication unit `tensorIdentity`.
  `comparison_composition` with `completedMap_composition` states exactly the displayed
  field-tower equation, with `tensorComposition` the ordinary scalar-adjunction tensor
  associator (right-adjoint comparison is identity on underlying sections).

The general ring-sheaf helper interfaces organize the specified finite and completed
systems; the asserted comparisons always specialize to their actual canonical maps.
The temporary tensor models range over the existing representative-characterized
`ProEtaleTensorModel`, and `tensorModel_exists` supplies their existence. No arbitrary
map, chosen nonempty natural isomorphism, or extra assumption replaces a canonical map.

Dependency declarations read and used:

- `def-pur-conventions`: `Sheaf.Paper.PurityFiniteSetting` — `WeilConjectures.PurityFiniteSetting`.
- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` — `Padic.finite_coefficientExtensionRing`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` — `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper` — `AlgebraicGeometry.IsProper`.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale` — `AlgebraicGeometry.Scheme.ProEt`.
- `def-weil-completed-integral-coefficients`: `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` — `WeilConjectures.integralConstantToCompletionOfUniverses`.
- `lem-pur-derived-change-of-rings`: `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel` — `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`.
- `def-weil-derived-complete-integral-detailed`: `Sheaf.Paper.SfIntegralConstructible` — `WeilConjectures.sfIntegralConstructible`.
- `def-weil-finite-tor-amplitude`: `Sheaf.Paper.FiniteTorAmplitude` — `WeilConjectures.finiteTorConstructible`.
- `def-weil-integral-rational-qbar-compact-support`: `Sheaf.Paper.IntegralRationalQbarCompactSupport` — `WeilConjectures.sfQbarCompactSupportValue`.
- `def-exchange-projection`: `Sheaf.Paper.ExchangeProjection` — `AlgebraicGeometry.ProEtale.coefficientExtensionExchangeProjection`.
- `lem-weil-finite-free-completed-scalar-comparison`: `Sheaf.Paper.FiniteFreeCompletedScalarComparison` — `WeilConjectures.finiteFreeCompletedScalarComparison`.
- `def-weil-compactifications-refinements`: `WeilConjectures.Compactification.Refinement` — `AlgebraicGeometry.Compactification.Refinement`.
- `def-weil-extension-by-zero`: `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero` — `AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZero`.
- `def-weil-derived-direct-image`: `Sheaf.Paper.SfDerivedDirectImage` — `WeilConjectures.SfIntegralDirectImage`.


The derived scalar construction also uses `pbcDerivedExtend`, `pbcDerivedRestrict`,
`pbcDerivedScalarAdjunction`, `pbcComplexCounit`, and the strict scalar towers from
`BoundedConstructibleTower` and `FiniteFreeCompletedScalarComparison`.
The intrinsic open API (`proEtaleRingOpenExtension`), ringed separately derived proper
API (`proEtaleRingDerivedDirectImage`), canonical tensor-pullback API, quotient tower
API and actual compactification `Refinement` are used, with their original definitions.
Recorded proof-dependency modules are imported where compatible. The legacy monolithic
`EtaleCompactSupportCoefficientChange` import passes through the old ExchangeProjection
module and conflicts with the intrinsic finite-coefficient API; its finite-map step is
stated here directly via the same canonical mates and finite-free biproduct argument.

Edge cases checked: n=1 (the least positive quotient), e=1, e>1 with differing
uniformizers but equal ideals, equal-level quotients, the identity field inclusion,
a tower of nontrivial inclusions, identity refinements and composition of refinements,
zero objects, empty schemes and all integer shifts. Quotient exponent zero is outside
the assertion. No dense-open or smooth compactification assumption has been added.
The block coordinate in arithmetic cofinality and the normalization of both proper/open
refinement factors were checked separately from endpoint isomorphism existence.

Searches: LeanSearch for extension of finite l-adic coefficient fields commuting with
integral compactly supported cohomology returned 8 unrelated finite-field/intermediate
field results. LeanFinder for integral compact support commuting with finite-free
extension with reduction/tensor coherence returned 8 unrelated adic-completion results.
Loogle `compactSupport, derivedScalarExtension` returned 0 (unknown compactSupport).
Mathlib grep `compactSupport.*[Cc]oefficient|[Ii]ntegral.*[Cc]ompact[Ss]upport` returned
16 analytic compact-support hits, with no relevant sheaf comparison. Upstream and
side-project rg for the item id and compact-support/coefficient names found its
prerequisites and the Roos cofinality source mention, but no theorem stating this node.
The existing partial prerequisites are imported instead of redeclared. Searches are
logged in the sandbox `searches.jsonl`.

Validation: all files are compiled separately through the prescribed scompile wrapper;
only expected sorry warnings are allowed. The delivery dry run will verify the final
node records, docstrings, signatures and clean per-file compilation.

## Dependency modules

`def-exchange-projection`: the recorded monolithic `ExchangeProjection` module imports
legacy `UpperLowerStar.Iso` alongside the current intrinsic
`FiniteCoefficient.UpperLowerStar.Iso`; importing it with current integral operations
reports duplicate `AlgebraicGeometry.ProEtale.upperStarIsoLowerStarInv`. The supplied-domain
portion is extracted verbatim into `Sheaf.Paper.ExchangeProjectionSuppliedDomains`, in
namespace `CategoryTheory.SuppliedExchangeProjection`, with only generic adjunction and
projection imports. It preserves the direct exchange mate, proper exchange then open
base change, proper projection then open projection, stage data, integral-reduction
compatibility, rationalization/common-stage representatives, unit/counit preservation,
and identity/composition scalar cocycle. It asserts no invertibility or existence of
higher-stage data. The old finite-level specializations remain in their original module;
this repair exposes the identical higher-stage interface needed by this item without
pulling the conflicting legacy finite-operation imports into its environment. Its node
copy changes only lean and explains this import/interface repair in lean.note.

## Repair of the returned head

The first prescribed dry run of the retained packet passed (commit 2a3500a68d).
The mathematical self-check nevertheless confirmed both H3 omissions in the return;
the preflight did not check those statements. The existing modules and proof route
were retained. The repair adds the natural recorded-functor identification and its
normalized coefficient comparison, and strengthens `comparison_strict_towers` in place.
No mathematical node statement or proof route was changed. The only new statement
dependency is the already published `def-weil-compact-support-finite-action`, whose
module supplies the fixed integral functor and its chosen-projection reduction iso.
All new helpers belong to this item's canonical comparison, and are listed in its
`lean.declarations`. There are no new definition nodes.

The endpoint audit also found that a heterogeneous equality alone would not provide
the comparison between the ringed proper/open presentation and the recorded intrinsic
finite presentation. The repair therefore constructs `finitePullbackIso` by uniqueness
of the normalized left adjoint to constant direct image, `finiteOpenIso` by the open
adjunction, and `finiteImageIso` by their exact/derived transports. The supporting
`finiteDirectImage_eq` identifies the actual structural maps by their sheaf-adjunction
transpose. `finiteReductionIso` is the scalar-adjunction comparison for the two quotient
tensor presentations. `IsRecordedIdentification` now states an ordinary typed equality
including these explicit endpoint maps; it contains no heterogeneous equality.

The original theorem's `Nonempty` object identification remains for compatibility;
it is superseded for the canonical-functor clause by `recordedIdentification` and
`recordedComparisonIso`. The strict-tower theorem now also takes the actual
`Ramification` equality. Its arithmetic step e is consequently the ramification index
in its new finite-level equations, rather than an unrelated cofinality parameter.

## Second reading by Q14

This is a separate clause-by-clause reading by the delivery author; no second agent
was started, as the dispatcher brief forbids it. The maintainer supplies the independent
review. I opened the node statement, the delivered module, and the cited fixed-functor
and strict-tower interfaces together. The earlier automatically inserted disclaimer
was not a mathematical reading. The correspondences checked are:

| Node hypothesis or clause | Lean counterpart and result of the second pass |
| --- | --- |
| Global finite field, prime different from p | `D : FiniteFieldDatum`, `[Fact l.Prime]`, `hl : l ≠ D.p`; `coefficientPrimeUnit` derives the needed invertibility. No new premise. |
| Finite extensions E⊂F | Fields with `Algebra ℚ_[l]` and `FiniteDimensional`, actual `i : E →ₐ[ℚ_[l]] F`. |
| Ramification index e≥1, equality of ideals | `Ramification l E F i e` and the positive bound. The repaired strict theorem now uses `heRam` in every finite map. Uniformizers are not equated. |
| Separated finite-type k-schemes X,Y and morphism f | The `Over`, `IsOver`, `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` instances in `Refinements`; no smoothness instance. |
| Small pro-etale site and completed rings | `Scheme.ProEt`, `completed`, the actual completed coefficient inclusion. Object/morphism universes remain u+1/u. |
| Ordinary C_W and finite-Tor domain | `pbcDerivedExtend` and `finiteTorConstructibleIntegral`; `scalarFiniteTor` uses the proved-as-statement preservation clause with no extra input. |
| P_E and P_F are the recorded functors | Found the original `Nonempty` clause insufficient. Added `recordedSupport` from `sfCompactSupportFiniteIntegralFunctor` and a natural identification normalized against its actual chosen Roos projection adjuncts. `finiteReductionIso` and `finiteImageIso` explicitly transport the finite endpoints in that typed equation. |
| Canonical natural iso, with the displayed source and target | `recordedComparisonIso` has precisely `recordedSupport E ⋙ C_Y ≅ scalarFiniteTor ⋙ recordedSupport F`. Its definition conjugates the normalized scalar mate; it does not choose a bare endpoint iso. |
| Fixed compactification j open, p proper | `c : Compactification f`; `openExtension` is exact, and `image` uses separately derived proper image. |
| Every positive n and B_n=A_F,en | In the new helpers index n denotes exponent n+1 and retained index `e * (n+1) - 1`. This includes exponent 1 and has no exponent-zero case. |
| Ordered finite proper/open maps | `finiteTensorMap` literally composes `properComparison` with proper pushforward of `openComparison`. Its endpoints are `finiteTensorSource` and `finiteTensorTarget`. |
| Strict compatibility before derived limits | Found the old chain lift insufficient. The new epsilon clauses normalize the actual retained evaluations and identify `Q(v_n)` with the restricted `finiteTensorMap`. The all-transition equality holds for the same strict map, before the subsequent Roos equation. |
| Integral comparison induced by these finite maps | The full equality in `comparison_strict_towers` uses the same v, a0, a1 and the independently normalized completeness units. Its cofinal maps retain both cone coordinates via `IsCofinalRoosMap`. |
| Specified reduction and further quotients | `ReductionComparisonEquation`, `comparison_reduction`, `ComparisonSquareEquation`, `comparison_quotients`; both reduction mates and actual quotient maps occur. The new source/target projection formulas use the same scalar units and associator. |
| Projection compatibility | `ProjectionComparisonEquation`, `comparison_projection`, `projectionDomain_complete`; actual supplied-domain proper/open projection and canonical tensor comparisons. |
| Canonical shifts | `scalarCommShift`, `imageCommShift`, `comparison_commShift` use the derived counit and inherited exact structures, for every integer. |
| Compactification independence | `refinementProperOpen`, `refinementComparison`, `comparison_refinement`, `refinementComparison_coherence`; actual refinement, open-unit normalization, proper composition, identity and composition. |
| Identity inclusion | `completedMap_identity`, `tensorIdentity`, `comparison_identity`; identity field inclusion is not excluded. |
| Field-tower cocycle | `completedMap_composition`, `tensorComposition`, `comparison_composition`; target associator is inside P_L, source associator is evaluated on P_E M, in the node's order. |
| Ordinary/strict scalar identification | Uses the imported normalized `completedScalarComparison`, the actual identity-unit augmentation, and the two-coordinate cofinal map. No alternative completion predicate. |

I also reread the dependency repair `ExchangeProjectionSuppliedDomains`. Its supplied
categories, operation functors, adjunctions and tensor/open comparison data are retained;
its projection is the proper counit projection then the open projection. It adds no
invertibility or existence assumption. The owning node's lean-only repair explains the
legacy duplicate-import problem. The definition has real data, and its associated
statement proofs, like all statement proofs in the item module, are only `sorry`.

Edge checks were repeated at e=1 and e>1, n=0 in the new helpers (positive exponent 1),
zero input, empty schemes, identity scalar extension, equal quotient levels, all shifts,
and identity/composite refinements. The new functor maps are actual maps in the full
subcategories (`homMk` on the underlying maps), not arbitrary actions on objects.
The primary signature remains verbatim in the node; all added declarations are recorded.

Validation after the endpoint-transport correction: the prescribed scompile.py invocation
with both delivered files exited 0. The final item compile took 32.8 s and the sandbox
item check took 28.4 s, under the unchanged 60-second limit; neither emitted diagnostics.
The dependency module also compiled cleanly. Both files have explicit `autoImplicit false`
and no lines over 100 characters. Both primary node signatures were compared verbatim
with their declarations, and both node copies retain indent 1, Unicode and a final
newline. The declaration extraction now ignores docstrings, so the previous spurious
`PurCompactSupport.maps` entry cannot be regenerated. Final preflight and delivery are
performed by the prescribed deliver2.py wrapper on the current base.
