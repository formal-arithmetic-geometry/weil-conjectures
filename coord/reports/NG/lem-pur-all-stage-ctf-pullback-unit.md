## Worker report

Item: `lem-pur-all-stage-ctf-pullback-unit`. Module:
`Sheaf.Paper.AllStageCtfPullbackUnit`. The only new postponed theorem is
`WeilConjectures.AllStageCtfPullback.preserves_ctf_and_unit`.
The finite and integral unit isomorphisms already exist, and are publicly reexported,
not restated. The module constructs their rational and common-stage images with real
maps. Every new theorem proof is `sorry`; no definition contains `sorry`.

Hypotheses and clauses, matched against the node:

| Node | Lean rendering |
| --- | --- |
| Fixed algebraic closure of a finite field, prime different from its characteristic, finite coefficient subextension and uniformizer | `P : PurityFiniteSetting.{u}`; `P.field`, `P.coefficients.l`, `P.coefficients.different`, `P.extension`; the recorded `Padic.coefficientExtensionRing` uses the recorded integer ring and uniformizer. |
| Small pro-etale site and its module derived category | `Scheme.ProEt`, `proEtaleDerivedCategory`, and `DerivedCategory (scalarReductionSource ...)`; the site remains object universe `u+1`, morphism universe `u`. |
| Every positive finite exponent | `n : ℕ` with exponent `n+1` and `Nat.succ_le_succ (Nat.zero_le n)`; no quotient is omitted. |
| X,Y finite type over k; no separatedness of X,Y over k | `X Y : Over (Spec (.of P.field.k))` and `LocallyOfFiniteType` plus `QuasiCompact` on their structure maps; there is no `IsSeparated X.hom` or `IsSeparated Y.hom`. |
| f a separated finite-type k-morphism | `f : X ⟶ Y`, with `IsSeparated f.left`, `LocallyOfFiniteType f.left`, `QuasiCompact f.left`; the Over morphism contains the commutation with the base. |
| Finite K bounded constructible, Tor interval [a,b] | First conjunct: `intrinsicFiniteTorsionConstructible ... K` and `HasProEtaleTorAmplitude ... K a b`. The latter includes `a ≤ b`. Both properties are asserted of `(finiteDerivedPullback ... f.left).obj K`, with unchanged `a,b`. |
| Restriction to finite Dctf | Second conjunct: preservation of `finiteTorConstructible` by precisely the same recorded ambient pullback. The full-subcategory restriction is determined by this object-property preservation. |
| Integral input in Db_c and a single Tor interval for all reductions | Third conjunct: `sfIntegralConstructible ... K`, followed by `∀ a b`, and `∀ n, HasProEtaleTorAmplitude ... ((scalarReductionDerivedExtension ... n).obj K) a b`. The endpoints precede the level quantifier. |
| Integral output derived complete, bounded constructible | `sfIntegralConstructible ... ((integralDerivedPullback ...).obj K)`, whose recorded definition is derived completeness, constructible finite reductions, and one uniform cohomological interval. |
| Canonical reduction is finite pullback of reduction | Third conjunct supplies a derived isomorphism (`Nonempty (... ≅ ...)`) with exactly these endpoints, and separately `IsIso (integralPullbackFiniteComparison ... K R e n)` for EVERY good K-flat representative R and identification e. The latter is the already specified adjoint of the actual Roos projection, not an arbitrary map. |
| Same integral Tor interval at every level | The third conjunct asserts `HasProEtaleTorAmplitude` for every output reduction with the same input `a,b`. |
| Integral Dctf restriction | Fourth conjunct preserves `finiteTorConstructibleIntegral`, whose defining existential interval is independent of all positive levels. |
| Rational pullback is integral pullback on representatives | The imported `rationalDerivedPullback` is the uniquely prescribed extension of `constructibleIntegralPullback`: same objects and scalar-linear action on integral arrows. No replacement functor is defined. |
| Common-stage pullback uses a common finite representative | The imported `commonStageDerivedPullback` retains the literal stage and has the representative-arrow normalization of its defining existence/uniqueness theorem. |
| Dctf=Db_c at field stages | The imported `finiteTorFieldCoefficientCategory` is definitionally its input category. The two recorded pullback functors already have the full rational/common-stage constructible categories as their source and target. |
| Finite unit and its exact inverse-image normalization | Reexported `ConstantGeometricStalkUnit.finiteUnit` has source the recorded `finiteDerivedPullback` of `finiteConstantCoefficientObject`, and target the same finite coefficient object on X. Its underived `finiteUnitHom` is the adjoint of section one, with the specified single-complex comparison. |
| Integral unit is the ACTUAL completed regular sheaf, not the discrete constant ring | Reexported `ConstantGeometricStalkUnit.integralUnit` has endpoints `(integralDerivedPullback ...).obj (integralConstantCoefficientObject ... Y)` and `integralConstantCoefficientObject ... X`. It is the good-representative comparison followed by the inverse of Q applied to the normalized strict chain unit. |
| Integral unit obtained from compatible finite units through the specified inverse limit | Reexported `integralChainUnit_existsUnique` fixes every finite quotient generator AND the zero shifted-product coordinate; `integralChainUnit_isIso` makes its derived image invertible. Its target is the actual shifted-cone construction `integralOperationsPullbackComplexFunctor`, not a freely chosen distinguished triangle. |
| Rational unit is the rationalized integral unit | `AllStageCtfPullback.rationalUnit`: the unchanged-object comparison followed by `sfRationalConstructibleLocalization.mapIso (ObjectProperty.isoMk _ (ConstantGeometricStalkUnit.integralUnit ...))`. This specifies the arrow and inverse. |
| Algebraically closed unit is its common-stage image | `AllStageCtfPullback.commonUnit P L f`, for EVERY finite coefficient field `L`, is the unchanged-stage comparison followed by `GeneralAlgebraicallyClosedCoefficients.inclusion L |>.mapIso (rationalUnit ...)`. `Coefficient.{u}` is the recorded canonically algebra-equivalent small model of the same field. In particular take `L = ⟨P.extension, inferInstance⟩` for the fixed E. |
| Invertibility of ell is not an extra assumption | `residueInvertible` transports `P.coefficientPrime_isUnit_stalk` along `W.residue w`. Its real data supplies the two existing operations' residue-field instances. No additional hypothesis is imposed. |
| Empty schemes included | No nonempty/site-point/stratum hypothesis occurs. On the empty site all unit complexes are zero and these constructions give the unique isomorphisms. |

Dependency declarations read and used (module names below have the prefix
`Sheaf.Paper.` unless a different prefix is displayed):

- `PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, its recorded field,
  coefficient and finite-extension structures, and `coefficientPrime_isUnit_stalk`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`,
  the actual weakly-etale over-category and its `ProEt.topology`.
- `DerivedPullbackTensorHom`: `finiteDerivedPullback`, `constructibleIntegralPullback`,
  `rationalDerivedPullback` and `rationalDerivedPullback_existsUnique`,
  `commonStageDerivedPullback` and `commonStageDerivedPullback_existsUnique`.
- `FiniteTorAmplitudeSites` reexports `FiniteTorAmplitude`: `finiteTorConstructible`,
  `finiteTorConstructibleIntegral`, and `finiteTorFieldCoefficientCategory`.
- `CompletedIntegralConstantMapOfUniverses`: the same completed sheaf and its quotient
  projections, via the completed coefficient module declarations it reexports.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: separatedness is `IsSeparated`,
  not `IsProper`; no properness assumption is made.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`; combine
  it with `QuasiCompact`, as the dependency node explicitly records.
- `IntrinsicFiniteTorsionConstructibility`:
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`.
- `SfIntegralConstructible`: `sfIntegralConstructible` and its full category.
- `DerivedScalarExtensionRestrictionAdjunction`: `scalarReductionSource` and
  `scalarReductionDerivedExtension`, derived tensor along the actual projection.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `CategoryTheory.IsDerivedLimit`; the unit uses the more specifically normalized
  strict Roos construction supplied by the operation dependency, rather than
  choosing a morphism between triangles satisfying this predicate.
- `SfRationalizationKaroubi`: `sfRationalConstructibleCategory` and
  `sfRationalConstructibleLocalization`; this is the raw localization with unchanged
  objects, no idempotents adjoined.
- `GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory` and the same-stage `inclusion`.
- Added already-landed statement dependency `lem-zl-constant-geometric-stalk-unit`,
  module `ConstantGeometricStalkUnit`: the exact finite and integral unit declarations
  listed above. This addition is permitted by brief-stage2 §5 (landed dependencies).
  A full traversal of its statement/proof dependencies found no path back to this item.

The declared proof imports include the modules of every recorded proof dependency:
`PullbackTorAmplitude`, `IntegralOperationsPreserveConstructible` (also publicly
reexported by the operation module), `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`,
`Sheaf.AlgebraicGeometry.ProEtaleConstantExact`, `ConstantScalarStrictUnit`,
`Sheaf.SixFunctors.CompletedCoefficientFreeResolution`, `IntegralOperationsWellDefined`,
`IntegralOperationsScalarComparisons`, `ConstantCoefficientScalarNormalization`.
The six-step proof in the theorem docstring follows the node's actual finite interval,
uniform reductions, quotient compatibility, completed rank-one unit, strict-cone
comparison, and field-transport proof.

Searches (raw msearch responses are in sandbox `searches.jsonl`):

- LeanFinder: “Derived pullback of constructible complexes preserves a fixed Tor
  interval and the completed coefficient unit”: eight hits about bounded derived
  categories; no all-stage statement. A second query about preservation and the
  completed integral coefficient unit returned general scheme base-change lemmas.
- Loogle: `"torAmplitudeIn"`: no hits; `"pullback", "unit"`: twelve hits about
  categorical pullbacks and their adjunctions, no completed coefficient unit.
- Mathlib grep: `completed.*[Pp]ullback|[Pp]ullback.*[Uu]nit`: 25 hits, including
  `Sheaf/PullbackFree.lean`; these give the underived canonical regular-module map,
  not the all-stage constructible assertion.
- LeanSearch: “Derived inverse image preserves constructible finite Tor complexes
  with the same interval and the completed integral coefficient unit”: eight hits,
  including `Functor.mapDerivedCategory` and ordinary adic tensor completion;
  no exact statement match.
- Project and upstream `rg`: unit/pullback patterns, Tor-amplitude patterns, the
  proposed full namespace, and the item's blueprint id. Upstream contains ordinary
  scheme/module pullback units, not this all-stage assembly. Project searches found
  `ConstantGeometricStalkUnit.finiteUnit` and `.integralUnit`, which are REUSED.
  `PullbackTorAmplitude` covers finite coefficients only. `ConstantPurityFrobeniusSquare`
  has related field units but its DAG reaches this item, so it is not imported.
  `CompletedUnitPullbackTower` has extra whole-system coherence and separated-scheme
  assumptions; it is not used to justify the present more general statement.

Edge cases checked: exponent one (n=0); arbitrary ramification; a=b and negative
endpoints; zero K; identity f; X or Y empty; nonseparated finite-type k-schemes;
coefficient stage equal to itself; arbitrary finite common stages, including the
specified E. The same single integral interval is retained at every quotient.
No new nodes, dependency repairs, statement corrections, or disputed statements.

## Second reading by NG

This is the dispatched worker's explicit second pass, not a claim that a second
agent reviewed the work. The dispatcher forbids spawning agents and assigns the
independent review to the maintainer after delivery.

Reopened the node and final module. Checked separately the five geometric hypotheses
(finite type of each structure map, separated finite type of f), and the four main
conjuncts. There is no separatedness condition on either structure map. The finite
and integral predicates use the SAME recorded rings and derived reductions. The
third conjunct keeps a,b outside the positive-level quantifier, and records both
the derived endpoint isomorphism and invertibility of the actual canonical comparison
on all good representatives. The field functors already have the required categories
as their domains; the two new field-unit definitions are literal images of the
existing completed integral unit. The finite unit is reused with its recorded exact
single-complex comparison. The completed unit is pinned by finite projections and
zero shifted coordinate, so no arbitrary cone filler or object-only choice is used.

The second pass removed duplicate finite/integral unit constructions and avoided the
cyclic downstream purity-square import. All introduced definitions have real data;
the sole new theorem is the assigned statement, with its proof postponed. Universes
are explicitly declared, autoImplicit is false, and all Lean lines are at most 100
characters. Independent mathematical review remains the maintainer's delivery review.
