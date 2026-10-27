## Worker report

The item is stated by `WeilConjectures.PodHomChain.counit_formula` in
`Sheaf.Paper.PodHomChainCounitFormula`. All mathematical theorem proofs are
`sorry`; all definitions have data. The item statement and DAG edges are unchanged.

Hypothesis and clause correspondence:

* The finite field and four coefficient conventions are the parameters
  `D : FiniteFieldDatum`, `C : D.CoefficientDatum`, the finite extension `E`,
  `n`, `hn`, and `S : SixFunctorOperationDatum D C E n hn`.
  `s : PodCoefficientStage` ranges over finite, integral, rational and common.
  Its `category`, `domain`, `operations`, `internalHom` and `tensor` are case
  distinctions on the existing categories, predicates and functors, not new
  coefficient models. Integral tensor and operations are completed; rational
  and common-stage branches use the recorded rationalization/compositum models.
* `X Y : SixFunctorSpace D` are finite-type k-schemes (no separatedness of their
  structure maps is imposed in the item). `f : X ⟶ Y` and the instances
  `IsSeparated f.hom.left`, `LocallyOfFiniteType f.hom.left`, and
  `QuasiCompact f.hom.left` render the separated finite-type morphism.
  `c : Compactification f.hom.left` specifies the compactification used by the
  supplied exceptional adjunction and the same projection.
* The chosen restricted adjunctions are encoded by `R : PodCtfAdjunctionData`.
  Its functors are actual full-subcategory lifts of the specified operations;
  its ordinary and exceptional adjunctions are `Adjunction.restrictFullyFaithful`
  with identity comparisons. The tensor-Hom adjunction uses the chosen closed
  structure and its signed symmetry. `tensorX` and `tensorY` identify this
  presentation with the recorded partial tensor. `podCtfAdjunctions_exists`
  supplies this data at every stage, so `R` names the chosen restriction rather
  than imposing a new geometric assumption. No definition chooses from it.
* `M`, and the quantified `N`, `T`, `T'`, `N'`, belong to the full subcategories
  of `PodCoefficientStage.domain`. Finite and integral membership is the actual
  finite-Tor predicate; field-stage predicates are top.
* `C` is `R.support.obj M`. `L_N` is
  `(homX S s f c R M).obj (R.exceptional.obj N)`. `sourceFunctor` is the
  composite exceptional / internal Hom / direct image, hence is exactly `A_N`;
  `targetFunctor` is internal Hom from `C`, hence is exactly `B_N`.
* `rawProjection` is the existing finite compactification projection component
  or `compactSupportProjectionComponent` at the other three stages.
  `rawProjectionIso` obtains invertibility from `compactSupportProjectionFormula`,
  with no extra isomorphism hypothesis. `projectionIso` transports this same map
  through `R.tensorX`, `R.tensorY` and the fully faithful inclusion.
  `projection` is its forward arrow, `C tensor T` to `f_!(M tensor f^*T)`.
* `pairing` is precisely `projection` at `A_N`, followed by `R.support.map` of
  tensoring the ordinary counit with `M` and then tensor-Hom evaluation, followed
  by the exceptional counit. Lean composition `a ≫ b` means first `a`, then `b`.
* `homEquiv` composes the inverse ordinary Hom equivalence, inverse tensor-Hom
  equivalence, inverse exceptional equivalence, precomposition with the forward
  `projection` (via `Iso.homCongr projectionIso.symm (Iso.refl N)`), and the
  tensor-Hom equivalence on Y. These are the five displayed bijections in order.
  `uncurriedChain` also spells out their first four arrows as a map.
* `curriedPairing` applies the fifth, same chosen tensor-Hom equivalence to
  `pairing`. The theorem's first conjunct says, for every `N T t`,
  `homEquiv ... t = t ≫ curriedPairing ...`.
* The second conjunct is test-object naturality for every `a : T' ⟶ T`.
  The third is target naturality for every `r : N ⟶ N'`; its two functor maps are
  exactly `Rf_* RHom(M,f^!r)` and `RHom(C,r)`.

Dependency declarations read and used:

* `Sheaf.Paper.SixFunctorOperationDatum`, `WeilConjectures.SixFunctorOperationDatum`,
  its finite/integral finite-Tor domains, and its recorded higher/closure stages.
  `Sheaf.Paper.SixFunctorDatum` supplies `SixFunctorClosedDomain`.
* `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions` records the ambient
  ordinary/exceptional adjunctions at finite coefficients. Here their supplied
  four-stage versions are the `SixFunctorPushStage.pullDirectAdjunction` and
  `exceptionalAdjunction` fields of `S`, restricted without changing the Hom maps.
* `Sheaf.Paper.DerivedPullbackTensorHom`: `constructibleIntegralHomPairs`,
  `constructibleIntegralHom`, `constructibleRationalHomPairs`,
  `rationalDerivedInternalHom`, `commonStageHomPairs`,
  `commonStageDerivedInternalHom`, and the finite intrinsic Hom model.
* `Sheaf.Paper.CompactSupportProjectionFormula`,
  `WeilConjectures.compactSupportProjectionFormula`; its finite projection
  component and `compactSupportProjectionComponent` give the actual maps.
  The supplied-domain exchange/projection construction is
  `Sheaf.Paper.ExchangeProjectionSuppliedDomains`,
  `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`, already
  used by these recorded stage constructions.
* The unusable `det-thm-sf-ctf-stability-adjunctions` record is repaired below.
* `Mathlib.CategoryTheory.Monoidal.Closed.Basic`:
  `CategoryTheory.MonoidalClosed.uncurry_curry`, `uncurry_natural_left`,
  `uncurry_eq` are the three declarations in the mathlib dependency record.
  The chosen adjunction is used directly through `Adjunction.homEquiv` so the
  formula uses its own evaluation and currying consistently.

Edge cases checked on the types and formulas: identity and proper f, empty X,
zero M or N, identity/composite maps in either naturality variable, n=1,
nonseparated X or Y with separated f, and all four coefficient stages. The
projection is never inverted in the pairing or in the fourth Hom-chain arrow.
The finite branch explicitly converts the double full-subcategory finite-Tor
object to the existing single-subcategory object, preserving its carrier and
arrows. All universes and section parameters are bound explicitly; auto-implicit
and relaxed auto-implicit are disabled. No additional equality of universes is
assumed. There is no statement dispute or correction.

Searches for an existing item declaration (logged in `searches.jsonl`):

* `msearch.py`, LeanFinder: “The inverse tensor Hom adjunction chain with ordinary
  and exceptional counits and projection formula is postcomposition with a
  curried pairing” returned eight tensor-Hom equivalence laws, none the five-map
  four-stage formula.
* `msearch.py`, Loogle: `CategoryTheory.MonoidalClosed.uncurry_eq,
  CategoryTheory.Adjunction.homEquiv_counit` returned zero hits.
* `msearch.py`, grep: `homChain|hom_chain|counitFormula|counit_formula`,
  Mathlib `CategoryTheory`, returned zero hits.
* Project `rg` searches for the same names in `lean/WeilConjectures` and
  `lean/Sheaf`, and `grep -rn` for the item id in `lean/WeilConjectures`, found
  no exact existing statement. The upstream TensorHom isomorphism concerns
  finite étale coefficients and does not identify this representative at all
  four stages. Searches for `HasCompatibleRestriction` and existing restriction
  declarations found no surviving copy of the retired helper.

## Dependency modules

`det-thm-sf-ctf-stability-adjunctions`: the recorded module
`Sheaf.Paper.ConstructibleFiniteTorAdjunctions` was deleted, explicitly noted in
its record on 2026-10-20; `scompile.py --source` confirmed that its source is
unavailable. `Sheaf.Paper.PodCtfAdjunctions` restores the general admissible
coefficient theorem as `AlgebraicGeometry.ProEtale.CondensedRing.podGeneralCtfAdjunctions`.
It states all three clauses with compatibility of the actual ambient Hom
bijections, right-factor tensor via signed symmetry, and every boundary
compactification, retaining the standing scheme/coefficient hypotheses of the
recorded interface. The old inclusion and localizing compactification helper modules are also
retired (`scompile.py --source` confirmed both unavailable). The real
`podCtfToLocalizing` inclusion is `ObjectProperty.ιOfLE` with the immediate
intersection membership proof, and `podLocalizingLowerShriek` is the actual
compactification functor lifted using its preservation witness. These restore
the missing canonical constructions, with no arbitrary maps or data chosen
from existence. `podCompatibleRestriction` gives the compatibility
equation explicitly. The same module supplies `PodCtfAdjunctionData`, its real
restriction constructions, and `podCtfAdjunctions_exists` for the four actual
coefficient-stage categories required by the item. Only the dependency's `lean`
field changes.

## Second reading by Q47

A second pass checked the two modules against the item, dependency, source Hom
chain and the recorded signatures. It removed a provisional extra projection
invertibility hypothesis by deriving it from the recorded projection theorem,
and retained the full general dependency theorem in addition to the interface
needed here. Inverse ordinary/tensor/exceptional Hom maps, forward projection,
then curry have the required directions. Naturality uses the actual composite
functors on morphisms. No node statement or edge was changed. This is the
worker's own second pass; the dispatch explicitly forbids starting another
worker and assigns independent review to the maintainer.

## Validation

Both modules are compiled separately in dependency order through `scompile.py`
against the published live build and the private sibling overlay. Final delivery
preflight and per-file compilation results are recorded by `deliver2.py`.
