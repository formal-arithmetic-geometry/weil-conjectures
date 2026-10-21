## Worker report

The module Sheaf.Paper.LatticeSupportedHomFiniteComparison states
AlgebraicGeometry.ProEtale.CondensedRing.latticeSupportedHomFiniteComparison,
with the single postponed proof `sorry`. Its conclusion supplies the structure
LatticeSupportedHomFiniteComparison. This is a package of the node's conclusions,
not an additional mathematical assumption. No statement correction or dependency
repair was needed. All source files were read from the read-only live clone;
all edits are in the item sandbox.

Hypotheses and objects, clause by clause:

- The section binders `l : ℕ`, `[Fact l.Prime]`, `E : Type u`, `[Field E]`,
  `[Algebra (Padic l) E]` and `[FiniteDimensional (Padic l) E]` fix exactly the
  prime and finite coefficient extension. The recorded integer ring, uniformizer
  and quotient are Padic.coefficientExtensionIntegers, coefficientExtensionUniformizer
  and coefficientExtensionRing. The last uses exponent n, not n+1.
- The theorem's `k`, `[Field k]`, `p`, `[Fact p.Prime]`, `[CharP k p]`, `hpl : p ≠ l`
  give precisely the positive characteristic and unequal primes.
- S, Z, V, X have `Over (Spec (.of k))` structures and LocallyOfFiniteType,
  QuasiCompact and IsSeparated structural maps. Locally of finite type plus
  quasi-compact is finite type. `i.IsOver`, `j.IsOver` and `v.IsOver` express that
  every displayed morphism is over k. `IsClosedImmersion i`, `IsOpenImmersion j`,
  `IsOpenImmersion v`, and `hij` identify Z, its open complement V, and S open in Z.
  The composite a is represented directly as v followed by i; no arbitrary a_! is used.
- `n : ℕ` and `hn : 1 ≤ n` render the positive integer level.
- `R` and `A` are only local notation for DerivedNakayama.integerRing l E and
  quotientRing l E n. These are the actual continuous condensed rings, with the
  spectral topology and quotient topology. `condensedRingObj` supplies their
  pullbacks on each small pro-etale site. `φ Y` is coefficientMap of the actual
  continuous reductionRing l E n.
- FormalSupportModules is the recorded category of internal module sheaves.
  DerivedCategory, leftDerivedFunctor, rightDerivedFunctor and mapDerivedCategory
  are the existing ordinary unbounded constructions. Universe u is explicit; the
  scheme site has objects at u+1 and morphisms at u, coefficient sheaves take values
  in Ab at u+1. No equality between site object and morphism universes is imposed.
- `L` is the source lattice and `hL : IsLisseCoefficientModule R L` means finite
  locally free on a pro-etale covering. Mod.IsFree allows rank zero and varying ranks.
- `Q` abbreviates exactly `(lowerStar R i).obj ((openImmersionLowerShriek R v).obj L)`.
  `D` is the existing internal Hom `(ihom L).obj (𝟙_ _)`, namely the integral dual.
- `Ext Y` is Mod.extendScalars along φ Y. Thus `Ln` and `Dn` are the actual ordinary
  scalar extensions of L and its dual along the quotient, i.e. L/pi^n and
  L-dual/pi^n with their quotient action. This is the usual quotient universal
  property, not an arbitrary finite module. `Res Y` is Mod.comap along the same
  coefficient map, and its mapDerivedCategory is exactly termwise Res_n.
- The target is not fixed or bounded: the functor isomorphisms range over the
  entire DerivedCategory (FormalSupportModules A X).

Conclusions, clause by clause:

- `finite` asserts Finite of the precise ring A_n.
- `torsion` asserts that one power of l kills every element, with nsmul in the
  additive group. No unramifiedness assumption is used.
- `reduced_lisse` asserts that Ln is finite locally free over the quotient sheaf.
- `dualReduction` is an isomorphism from Dn to Hom_A(Ln,A), the inverse orientation
  of the display in the node. `evaluation` fixes it canonically: after the two
  ordinary scalar-adjunction units, the reduced pairing equals the original
  pairing followed by φ S. Mod.tensorObjπ is the actual relative-tensor quotient
  of the underlying abelian-sheaf tensor. This is the formula
  lambda-bar(x-bar) = lambda(x) mod pi^n, so no arbitrary rescaling is allowed.
- `sourceReduction` is an isomorphism between L(Ext_X)(Q[0]) and (a_!Ln)[0]
  in DerivedCategory (FormalSupportModules A X), retaining the finite scalar action.
  It is not merely an isomorphism after restricting to integral coefficients.
- `derivedComparison` gives the natural comparison at the level of derived
  abelian-group complexes, from global integral RHom after exact restriction to
  the supported reduced-dual RΓ complex. This also satisfies the derived-form
  requirement rather than providing only per-degree cohomology groups.
- For every integer q, `groups` gives all three displayed natural isomorphisms of
  functors to AddCommGrpCat. The first component is explicitly the inverse of
  Mod.derivedExtendMapDerivedCategoryAdjunction.homEquiv, with target K shifted by q.
  The second is explicitly precomposition with sourceReduction.inv. The third
  identifies Hom(a_!Ln,K[q]) with degree-q homology of F. Using Res(K[q]) is the
  canonical shift-compatible expression for (Res K)[q], since Res is termwise.
- `F` is local notation for the exact expression:
  formalClosedSupport A i j right-derived, then exact formalSupportPullback A v,
  then derivedTensor A S with Dn[0], then right-derived formalClosedSupportSections.
  The recorded formalClosedSupport is literally i* ker(id → j*j*) before total
  right derivation. formalClosedSupportSections forgets the module to an abelian
  sheaf and applies Γ; its total right derived is global RΓ with abelian values.
- `termwise` supplies exactness of tensorLeft Dn and a natural isomorphism from
  its ordinary termwise descent to the recorded derived tensor with Dn[0]. The
  letI introduces only the provided exactness instance; no object is chosen and
  no mathematical hypothesis is added.

Dependency declarations used (modules, names):

- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible:
  standing scheme conventions from sk-def-sfb-dc-setting (in the public import
  closure of FormalClosedSupport). The theorem spells out the setting; it does
  not use bounded constructible categories or compactifications as assumptions.
- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite and CoefficientExtension:
  Padic.finite_coefficientExtensionRing and the coefficient constructions above.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic:
  condensedRingObj, coefficientRing and upperStarFromPoint.
- Sheaf.Paper.DerivedNakayamaResolution: integerRing, quotientRing, reductionRing,
  the exact coefficient constructions recorded by def-sfb-torsion-stratum-coefficients.
- Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions and upstream
  derived-functor modules: DerivedCategory and total derivation, publicly imported
  by DerivedNakayamaResolution; no new derived-category convention is introduced.
- def-weil-size-convention has no mathematical declaration: explicit universes
  fulfill its convention.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients:
  coefficientMap; its public ModuleObjects.DerivedExtendScalars dependency supplies
  Mod.extendScalars, Mod.comap and derivedExtendMapDerivedCategoryAdjunction.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs:
  CondensedRing.lowerStar; LowerShriek.Defs: openImmersionLowerShriek.
- Sheaf.Paper.CoefficientHeartStratificationDefs: IsLisseCoefficientModule.
- Sheaf.Paper.FormalClosedSupport and its public FormalClosedSupportAdjunction:
  FormalSupportModules, formalClosedSupport, formalSupportPullback,
  formalClosedSupportSections and the existing support/stratum assertions.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom and Tensor:
  derivedHom and derivedTensor; ordinary internal Hom is ihom in the same closed
  relative module category.
- Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses:
  ringedSiteZerothHypercohomologyOfUniverses, the recorded H^0 RΓ convention in
  the equivalent SheafOfModules encoding. The module-object RΓ used here is the
  already supplied formalClosedSupportSections right derived functor; no private
  copy or unnecessary cross-encoding choice is made.

The available proof dependencies are imported privately:
LocallyFreeDerivedScalars, IntTensorProjection, SliceScalarHomChainAdjunction,
SheafRingDerivedCoefficientAdjunction, ClosedSupportStratumHom. The module docstring
and theorem docstring give the complete seven-step DAG proof, including the
coefficient-action argument that upgrades source reduction to D(A_n).

Edge cases checked before and after writing: n=1 works even for ramified E, since
l lies in (pi); n=0 is deliberately excluded by the node's hn. Zero lattice and
rank-zero trivializations give zero dual/source and zero Hom groups. Empty strata,
empty Z, Z=X and empty open complement make the existing support and shriek
functors reduce to their usual zero/identity cases. Negative q and arbitrary
unbounded targets remain quantified. No constructibility, derived completeness,
flatness of the quotient coefficient map, connectedness or fixed rank is imposed.

Searches made:

- msearch.py leanfinder: "Derived Hom from an integral locally free lattice
  extended by zero into restricted finite coefficients equals supported cohomology
  of the reduced dual". Eight hits (ordinary module scalar adjunction, group
  cohomology/Ext, and unrelated Nobeling results); none states this comparison.
- msearch.py loogle: `"extendRestrictScalarsAdj"`. Twelve ordinary ModuleCat scalar
  adjunction hits, no sheaf-support/lattice comparison.
- msearch.py grep: `supported.*[Hh]om|[Hh]om.*supported`. Twenty-five hits about
  supported complexes, finitely supported maps, and unrelated categorical extensions.
- rg of lean/WeilConjectures and lean/Sheaf for latticeSupported, lattice_supported,
  supportedHom, supported_hom, SupportedHom and the item ID: unrelated purity,
  Kummer and Grothendieck-existence Hom comparisons, no exact existing statement.
  The reusable support and scalar constructions were read directly and reused.
  The item-ID grep of lean/WeilConjectures and the declaration-name search of
  dag/lean_names_upstream.json also returned no hits.

No STATEMENT-DISPUTED fault was found. No new DAG node is introduced; the only
item JSON field changed is lean.

## Second reading by NW

I reopened the node and reread the complete module against it, without delegating
(the dispatch brief forbids other agents; the maintainer provides the independent
review). The quotient exponent, actual continuous coefficient action, arbitrary
unbounded target, every integer q, and the finite-coefficient location of the source
isomorphism all match. The displayed dual is reversed only by isomorphism symmetry;
the explicit evaluation equation fixes its meaning. I checked that all three
natural transformations have AddCommGrpCat values, that the first two component
normalizations use the actual scalar adjunction/source isomorphism, and that the
last target contains the finite-coefficient support functor rather than integral
support followed by reduction. The termwise assertion is retained. The additional
derivedComparison states the same comparison before taking homology, as the
project requires. No mathematical statement change was needed.

Compiler repair: local notation required quotPrecheck false; autoImplicit and
relaxedAutoImplicit remain false, and every parameter/universe is explicitly bound.
For elaboration, use the upstream irreducibility settings for the K-injective closed
structures and respectTransparency.types=false. The heartbeat option is scoped to the conclusion package; the wrapper retains its
60-second wall limit. No global build or live edit was run.
