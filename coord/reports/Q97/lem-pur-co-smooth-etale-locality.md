## Worker report

The item is stated in `Sheaf.Paper.CohomologicalSmoothEtaleLocality`, with two named
`sorry` theorems: `AlgebraicGeometry.ProEtale.isCohomologicallySmooth_of_surjective_etale`
and `AlgebraicGeometry.ProEtale.isCohomologicallySmooth_etale_and_dualizing`.
Together these give exactly the two sentences of the node. No item statement,
statement dependency, proof, or proof dependency was changed.

Source checked: current blueprint main-20261015,
`sec-six-functors-basics/sk-prop-cohsm/lem-pur-co-smooth-etale-locality.md` and its proof;
the node's detailed seven-step proof was read in full. The older source field has the
same statement. The proof in the module records all seven steps, including the actual
projection/exchange mate identities, the globally constructed RHom inverse, arbitrary
base change and nonseparated targets, and the empty-scheme cases.

Hypothesis and conclusion correspondence:

- The chapter's fixed setting is `P : WeilConjectures.PurityFiniteSetting.{u}`. Its fields
  retain p prime, a positive, the finite base field and its fixed algebraic closure,
  ell prime different from p, the finite coefficient subextension, and positive level n.
  `P.Coefficient` is the existing lifted quotient O_E/(varpi_E^n), not an arbitrary ring.
- The schemes are `U X Y : Scheme.{u}`. Each `Over (Spec (.of P.field.k))` instance and
  each map's `IsOver` instance gives precisely its k-structure and compatibility.
- Finite type over k is the pair of `LocallyOfFiniteType` and `QuasiCompact` instances
  on each structure morphism. There is no assumption that Y is separated over k.
- `U.IsSeparated` and `X.IsSeparated` express the separated source schemes in the
  source-cover assertion. Since Spec k is separated, this is equivalent to their
  separatedness over k. It also supplies separatedness of e, f, and their composite.
- `f : X ⟶ Y`, with locally finite type and quasi-compact instances, is the separated
  finite-type map of the fixed setting. Its composition with the cover is `e ≫ f`.
- `e : U ⟶ X`, `[Etale e]`, and `[Surjective e]` give the exact surjective etale cover.
  The quasi-compact instance on e spells out an automatic property of a map between
  these finite-type schemes over a field. Such sources are quasi-compact and targets
  are Noetherian, hence quasi-separated; Mathlib's `quasiCompact_of_compactSpace`
  gives it. This excludes no cover from the node.
- `h : IsCohomologicallySmoothCompared P (e ≫ f)` is precisely the hypothesis that fu
  is cohomologically smooth. The conclusion is `IsCohomologicallySmoothCompared P f`.
- The second theorem quantifies separately over any etale `e : U ⟶ X` in the fixed
  setting, without surjectivity or absolute separatedness of either scheme. The
  separatedness of e is the separated-morphism convention required for R e_! and R e^!.
  Etaleness supplies local finite type; the quasi-compact instance is again automatic
  in this finite-type field setting.
- Its first conjunct is cohomological smoothness of e. Its second is `Nonempty` of
  the isomorphism from `comparedDualizing P e` to the actual derived tensor unit on
  the small pro-etale site of U. This is exactly omega_e isomorphic to Lambda_U.
  The compactification argument is the constructed Nagata compactification, not an
  extra existence or adjoint hypothesis.
- The predicate used here is the dependency's repaired, canonically transported
  three-clause definition described below. Thus the main assertion includes tensor
  invertibility with an inverse in Dctf, invertibility of the specified tensor mate
  for every Dctf input, and invertibility of the specified beta after every allowed
  finite-type change of base. Arbitrary changes of base are not required to be
  separated or smooth. No orientation, dimension, trace, shift, or smoothness of f
  has been added.

Dependency declarations read and used:

| Node | Module and declaration |
| --- | --- |
| def-pur-conventions | `Sheaf.Paper.PurityFiniteSetting`, `WeilConjectures.PurityFiniteSetting`, `Ring`, `Coefficient` |
| def-pur-co-smoothness | Original `Sheaf.Paper.CohomologicalSmoothness`, `AlgebraicGeometry.ProEtale.IsCohomologicallySmooth`, full signature and clauses read; repaired as below |
| def-weil-etale-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `AlgebraicGeometry.Etale`, full class signature and docstring read |
| def-weil-scheme-morphism-properties | Convention node, no declaration of its own; use `Scheme`, `Scheme.IsSeparated`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`, `Surjective` and the recorded etale notion |

The repaired dependency additionally uses the existing
`Etale.dualizingComplex`, `Etale.dualizingComplexTensorMap`,
`Etale.dualizingComplexBaseChangeMap`, `ProEtale.comparisonUpperStar`,
`ProEtale.DerivedCategory.constructibleFiniteTor`, `ProEtale.derivedTensor`,
`HasCompactification.compactification` and `Compactification.ofIsPullback`.
No definition of any of these notions is copied.

Edge cases checked before drafting: identity cover and identity etale map; nonsurjective
open immersion in the second assertion; a disconnected finite etale cover; empty U
and X (surjectivity forces X empty when U is empty); empty etale source without
surjectivity; nonseparated Y and Y' and arbitrary changes of base; independent site
object universe u+1 and morphism universe u; arbitrary finite coefficient level n>=1
including non-field, nonreduced quotient rings. The coefficient unit of the zero
module category on the empty scheme is zero, so its invertibility causes no exception.

Searches for an existing declaration:

- `msearch.py ... leanfinder` query: "Cohomologically smooth morphisms are local on the
  source for surjective etale covers and etale morphisms have trivial relative
  dualizing complex". Eight hits on ordinary smoothness/etaleness and ring-map
  locality, none on cohomological smoothness or dualizing complexes.
- `msearch.py ... leansearch` query: "Cohomological smoothness is local on a surjective
  etale cover of the source". Eight hits on smooth ring maps, ordinary scheme
  smoothness, and surjectivity on stalks; none match.
- `msearch.py ... loogle` query:
  `AlgebraicGeometry.ProEtale.IsCohomologicallySmooth, AlgebraicGeometry.ProEtale.dualizingComplex`.
  Zero hits, unknown identifier for the project-specific predicate.
- `msearch.py ... grep` query:
  `IsCohomologicallySmooth|cohomologically.smooth|dualizingComplex`. Zero Mathlib hits.
- `rg` of the pinned Mathlib AlgebraicGeometry, source `WeilConjectures`, project
  `lean/Sheaf`, side upstream `lean/WeilConjectures/SixFunctors`, and
  `dag/lean_names_upstream.json`: only the recorded project definition and generic
  canonical-map/coherence infrastructure. None state this two-clause locality lemma.
  The exact blueprint-id grep in the pinned source found nothing. New declaration
  names were also checked for duplicates. The current server source of the recorded
  cohomological-smoothness module and etale-shriek-base-change module was read via
  `scompile.py --source`, so a stale local file was not treated as a blocker.

## Dependency modules

`def-pur-co-smoothness` is repaired in
`Sheaf.Paper.CohomologicalSmoothnessComparison`, whose main declaration is
`AlgebraicGeometry.ProEtale.IsCohomologicallySmoothCompared`.
The recorded module cannot currently be imported: both a full proof-import compile
and a compile with only the statement imports fail inside
`WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.BaseChange` because
`UpperLowerStar.Iso` duplicates `upperStarIsoLowerStarInv` from
`FiniteCoefficient.UpperLowerStar.Iso`. This is an unusable dependency interface under
section 1(B), not a missing mathematical hypothesis.

The repair uses the exact canonical ordinary-etale adjunction mates already provided
by the published upstream framework, and the canonical exact comparison pullback.
It changes only this dependency node's `lean` record. It does not change the original
source module or any other node's statement.

Its clause-by-clause interpretation is:

1. `comparedDualizing` is nu_X^*(f_et^! Lambda_Y). The canonical comparison unit and
   its unit-object identification identify this with the prescribed
   nu_X^* f_et^! Rnu_Y,* Lambda_Y, so it is the same relative dualizing object.
   `comparedInvertibilityClause` uses the original pro-etale derived tensor,
   coefficient unit and `constructibleFiniteTor` predicate. The inverse lies in
   precisely the original Dctf category; both tensor orderings are required.
2. `comparedTensorClause` requires invertibility of the image under nu_X^* of the
   actual `Etale.dualizingComplexTensorMap` for every etale K whose nu_Y^* image
   lies in Dctf. Every pro-etale Dctf object has such a representative. Conversely,
   exact and conservative comparison pullback makes any such representative bounded;
   it is not an unrestricted extra test domain. The canonical tensor/pullback and
   compact-support comparisons preserve the counit transpose, so this is exactly
   the original theta, written after tensor symmetry and in these coordinates.
   No arbitrary endpoint isomorphism or arbitrary map is used.
3. `comparedBaseChangeClause` quantifies over all finite-type k-schemes X',Y' and
   all k-morphisms g',f',g making an `IsPullback` square. It requires invertibility
   of comparison pullback of `Etale.dualizingComplexBaseChangeMap`, the actual mate
   of inverse compact-support exchange, followed by the coefficient-unit map.
   The primed compactification is the base change of the original one and its
   quasi-compactness is supplied by the existing pullback theorem. Canonical
   comparison/exchange compatibility gives exactly the original beta. There is
   no separatedness restriction on g, X', or Y'.

All helper definitions have real data: the finiteness instance reuses the quotient
finiteness theorem; the compactification reuses Nagata after deriving Noetherianity
and compactness from the field structure morphism; all functors, tensors and maps
reuse the published declarations. The repair introduces no postponed theorem and
no data chosen from an undetermined existence statement. The original, incompatible
module remains untouched; the new module gives the equivalent transport interface
used by this delivery. It preserves the small-site and coefficient universes.

Five recorded proof-import modules also reach the same incompatible legacy API and
are deferred from this statement file: `Sheaf.Paper.ExchangeProjection`,
`Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula`,
`Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`, and
`Sheaf.Paper.CanonicalOriginCompactSupportComposition`, and
`Sheaf.AlgebraicGeometry.EtaleOriginAdjointClass`. The last imports both legacy and
finite-coefficient derived comparison and fails with duplicate
`derivedComparisonAdjunctionPlus`. Their DAG edges and the full
proof plan remain unchanged. All other recorded, stated proof-dependency modules
are imported without `public`; unstated proof nodes have no module to import.
This import failure needs maintainer attention before those legacy proof modules can
be used together with the canonical finite-coefficient framework.

Validation: `scompile.py Q97 lem-pur-co-smooth-etale-locality` with both delivered
modules in dependency order passed: dependency 4.8 seconds, item 4.8 seconds in
the library-name checks, with no errors or warnings. Both files also passed their
sandbox-name checks. No timeout limit was changed; abstracting the tensor clause
over its finite coefficient ring eliminated the expensive quotient-instance kernel
reduction. There are exactly two postponed named theorem proofs and no postponed
definition data. A final static check found no line above 100 characters, and both
node copies differ from the repository only in `lean`, with verbatim signatures.

## Second reading by Q97

I read the node statement and its Stacks/blueprint source place before checking the
Lean signatures. The statement's objects, hypotheses, and conclusions are rendered as
follows.

* The fixed purity datum is `P : PurityFiniteSetting.{u}`, supplying the finite field,
  its algebraic closure, the prime and coefficient quotient `P.Coefficient`.
* In the first assertion `U X Y : Scheme.{u}` are schemes over `Spec (.of P.field.k)`;
  `U` and `X` are separated, and all three structure morphisms are locally of finite
  type and quasi-compact. The map `f : X ⟶ Y` is over the base, locally of finite type,
  and quasi-compact. The map `e : U ⟶ X` is over the base, étale, quasi-compact, and
  surjective. The hypothesis is
  `h : IsCohomologicallySmoothCompared P (e ≫ f)`, and the conclusion is
  `IsCohomologicallySmoothCompared P f`.
* In the second assertion `U X` are finite-type schemes over the same base, and
  `e : U ⟶ X` is an étale, base-compatible, separated, quasi-compact map. The
  conclusion is the conjunction `IsCohomologicallySmoothCompared P e` and
  `Nonempty (comparedDualizing P e ≅ 𝟙_)`. The explicit separatedness is the domain
  requirement of the cohomological-smoothness predicate; it does not add a condition
  beyond the source's separated finite-type setting in which that predicate is stated.

Each object and clause appears in the Lean in the same order. The first theorem's
`U.IsSeparated` and `X.IsSeparated` also supply separatedness of `e`, `f`, and their
composite through the recorded scheme-property instances. `Y` is not assumed
separated, matching the source. The second theorem has no absolute separatedness
hypothesis on either scheme and permits nonsurjective étale maps, as in the source;
`[IsSeparated e]` is exactly the separated-morphism side condition needed to form the
cohomologically smooth predicate. The comparison definition retains all three clauses:
the Dctf tensor inverse, the specified counit projection mate on every permitted
étale representative, and the specified base-change mate for every finite-type
Cartesian change, with no dimension, orientation, trace, or smoothness assumption.

The repaired dependency `def-pur-co-smoothness` was read clause by clause. Its
`CohomologicalSmoothnessComparison` interface uses the same small pro-étale site and
coefficient/site universes as the original definition and uses the canonical
comparison pullback of the existing étale dualizing and mate maps. It is therefore a
valid interface repair, rather than a weakened or arbitrary replacement. No item
statement correction was needed, and the item node's `statement` remains verbatim
equal to the source and to both Lean theorem signatures' mathematical content.

Edge cases checked are the identity and disconnected covers, a nonsurjective open
immersion in the second assertion, empty source/target schemes (including the zero
coefficient module category), arbitrary nonseparated `Y` and base-change schemes,
all positive coefficient levels including nonreduced quotients, and the distinct
small-site object/morphism universes. Surjectivity forces an empty target when the
first source is empty; no case is excluded by a universe equality or by `n`.

The existing-declaration searches were repeated with LeanFinder, LeanSearch, Loogle,
`rg` over Mathlib, the pinned upstream `WeilConjectures`, the project `lean/Sheaf`,
and `dag/lean_names_upstream.json`. They found only ordinary smooth/étale locality and
generic dualizing infrastructure, with no matching cohomological-smoothness locality
lemma or duplicate declaration. The source and all recorded dependency declarations
were opened; no private copy or local notation is used.

The only defect encountered was the recorded `def-pur-co-smoothness` module's import
collision (`UpperLowerStar.Iso` duplicated `upperStarIsoLowerStarInv`). I retained its
node statement and repaired only its `lean` record with the canonical comparison
module `Sheaf.Paper.CohomologicalSmoothnessComparison`, including real helper data and
the exact three clauses. No mismatch in the item's own hypotheses or conclusions was
found, so the item Lean was left unchanged. Both delivered files compile with the
required `scompile.py` wrapper, with only the two named theorem `sorry`s.
