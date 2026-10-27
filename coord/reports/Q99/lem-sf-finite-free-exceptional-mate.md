## Worker report

The module `Sheaf.Paper.FiniteFreeExceptionalMate` states
`CategoryTheory.finiteFreeExceptionalMate_isIso`, with one postponed proof. The
representing isomorphism, the mate, the successive Hom map, and the finite-sum maps are real constructions
from Mathlib adjunctions. `FiniteFreeExceptionalScalarPresentation` packages the
universal scalar extension and its normalized coordinates. The theorem supplies these
presentations existentially before quantifying over the four functors: their existence,
unit normalization, and coordinates are conclusions, never additional assumptions.
The universal property determines the extension up to its unique counit-compatible
isomorphism. The finite-basis column equation determines its coordinate map uniquely.
There is no choice of an arbitrary comparison from a mere existence assertion.

Hypothesis and clause correspondence:

- The ring homomorphism A to B is `[CommRing A] [CommRing B] [Algebra A B]`, with
  `algebraMap A B`; any ring homomorphism defines this algebra structure. The specified
  finite basis is `basis : Module.Basis (Fin r) A B`, including r = 0.
- The sites are `(J : GrothendieckTopology C)` and `(K : GrothendieckTopology D)`.
  Their object and morphism universes are independent. Fixed-ring module sheaves
  `Sheaf J (ModuleCat A)` are the constant-ring case of the recorded category
  `ringedSiteModules`, through `CategoryTheory.constant_ring_module_sheaves`.
  Coefficients and module values live in the common maximum of both site sizes and
  the ring universe. `HasSheafify` explicitly supplies the sheafification interfaces
  available on such small sites. The four `HasDerivedCategory.{w}` binders select
  the ordinary unbounded localizations in the chosen independent Hom universe w.
- T is the universal left-derived functor of
  `Sheaf.composeAndSheafify J (ModuleCat.extendScalars (algebraMap A B))`:
  the presentation's `counit` and `universal` retain its actual universal pair.
  U is literally `(Sheaf.restrictScalars J (algebraMap A B)).mapDerivedCategory`.
  The scalar adjunction field `adj` is normalized by the localized ordinary tensor
  unit (`unit_normalized`); its coordinates have exactly the unit followed by
  multiplication-by-basis columns (`column`). These are theorem conclusions.
- FA, GA, FB, GB have precisely the four derived module-sheaf endpoints in the node;
  all four `Functor.Additive` instances and specified `aA : FA ⊣ GA`, `aB : FB ⊣ GB`
  appear in the universal quantification. Adjunction includes the Hom bijections,
  unit, counit and triangle identities.
- `multiplication` states exactly `GB.map (a • 𝟙 N) = a • 𝟙 (GB.obj N)` for every
  B scalar and every B-derived object N. No stronger linear-functor hypothesis is used.
- `c : FA ⋙ SD.T ≅ SC.T ⋙ FB` renders T_D FA isomorphic to FB T_C in Lean's
  diagrammatic functor composition convention.
- `ρ` renders U_D FB isomorphic to FA U_C. `normalization` conjugates U_D(c)
  by the two coordinate isomorphisms and ρ and equates it to `biproduct.desc` of
  `FA.map (biproduct.ι ...)`, precisely the stated finite-sum comparison.
- `finiteFreeExceptionalTheta` is `rightAdjointUniq` between `sC.comp aB` and
  `(aA.comp sD).ofNatIsoLeft c`. Thus it is a natural isomorphism, without a
  postponed existence choice. `finiteFreeExceptionalSumComparison` and `finiteFreeExceptionalSumInverse` are
  respectively the explicit `biproduct.desc` and `biproduct.lift` constructions.
  The first conjunct identifies postcomposition with
  its hom with `finiteFreeExceptionalHomMap`, whose body explicitly runs the
  five displayed adjunction bijections with precomposition by c in the middle.
- `finiteFreeExceptionalMate` is the existing `mateEquiv aA aB` applied to c.inv.
  It is a natural transformation defined without a basis. `IsIso` asserts the
  natural isomorphism. The next conjunct is the exact counit equation, in Lean's
  left-to-right morphism composition notation.
- The next conjunct says every natural transformation satisfying that equation
  is this same mate. This records the stated uniqueness/basis independence:
  neither the definition nor its determining counit equation uses a basis.
- The next conjunct restricts the mate and conjugates by SC.coordinates,
  theta, and GA of SD.coordinates. Its right side is `biproduct.desc` with
  j-th column `GA.map (biproduct.ι ...)`.
- The last conjunct gives both inverse identities for that comparison and
  `biproduct.lift` with rows `GA.map (biproduct.π ...)`. The mate is already a
  morphism in the B-linear derived module category, so its B-linearity is built
  into its type, not an additional assumption on FA or GA.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`: publicly retains
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and its universal cochain pair;
  the constant-ring presentation here spells out the same left-derived property.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, specialized via the constant-ring equivalence
  to upstream `CategoryTheory.Sheaf.restrictScalars`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`; we use the associated
  `GrothendieckTopology` and `Sheaf` convention, requiring no global pullbacks.
- Added landed dependency `lem-cbc-constant-ring-module-sheaves`, module
  `Sheaf.CategoryTheory.ConstantRingModuleSheaves`, declaration
  `CategoryTheory.constant_ring_module_sheaves`: the exact constant-ring equivalence.
- Proof imports retained: `Sheaf.CategoryTheory.DerivedFiniteFreeScalarCoordinates`
  (`SheafOfModules.RingedTensor.derived_finiteFreeScalarCoordinates`),
  `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`
  (`SheafOfModules.sheafRingDerivedCoefficientAdjunction`),
  `Sheaf.Algebra.Homology.ScalarInternalHomAdjunction`
  (`CategoryTheory.scalarInternalHomAdjunction_exists`, including conservativity),
  `Mathlib.CategoryTheory.Yoneda` (`CategoryTheory.Yoneda.fullyFaithful`), and
  `Mathlib.CategoryTheory.Adjunction.Mates` (`CategoryTheory.mateEquiv`).

Edge cases checked: r = 0 (empty biproducts, zero target coefficient ring, both
comparison composites still identities of zero objects); zero objects; zero source
ring; the empty site and topologies with empty covering sieves; r = 1 and identity
ring map; arbitrary unbounded complexes; distinct site object/morphism universes.
The multiplication hypothesis retains the correction for the conjugation-twisted
additive functor counterexample already resolved in stage 1. No statement correction
or new independent notion is needed. No STATEMENT-DISPUTED remains.

Searches made using `msearch.py Q99 lem-sf-finite-free-exceptional-mate`:

- leanfinder: "Finite free coefficient extension right adjoint counit mate
  isomorphism additive functors derived sheaves". Eight hits: derived adjunction
  counit infrastructure, constant-sheaf counits, pushforward counits, condensed
  free/forget adjunctions. No exact statement.
- loogle: `"rightAdjointUniq"`. Twelve hits, including the definition and its
  unit/counit equations. Used this existing isomorphism construction.
- grep, Mathlib CategoryTheory: `isIso_mateEquiv_app_of_isIso_biproductDesc|
  finiteFree.*[Mm]ate|rightAdjointUniq`. Nineteen hits for generic uniqueness
  infrastructure, no complete statement.
- leansearch: "Finite free scalar extension right adjoint mate biproduct".
  Eight hits, ordinary module extension/restriction adjunctions and rigid dual
  mates; no derived sheaf result.
- rg in project and upstream: `finiteFree`, `scalarCoordinates`, `exceptionalMate`,
  `rightAdjointUniq`, `constantRingModule`. Read the finite-free scalar calculus,
  generic copower criterion, constant-ring module equivalence, scalar internal-Hom
  data and scalar-coordinate interfaces. None states this arbitrary-site result
  with theta's Hom characterization and the two finite-sum formulas.
- Literal item-id search in `lean/WeilConjectures` and `lean/Sheaf` returned no
  existing declaration. Searches in `dag/lean_names_upstream.json` found no exact
  named match. No duplicate declaration is introduced.

Named sum maps in the final signature are the transparent mathematical constructions
spelled out in their bodies: finiteFreeExceptionalSumComparison is biproduct.desc,
and finiteFreeExceptionalSumInverse is biproduct.lift. Irreducibility only controls
elaboration unfolding; it changes none of their data or mathematical meanings.

## Second reading by Q99

Self-review only: the dispatcher explicitly prohibits starting other agents; the
maintainer's independent review remains required. Reopened the node and final source
and matched every binder and conjunct above. In particular c is inverted for the
mate, but not in the Hom chain for theta; the scalar coordinate iso points from UT
onto the biproduct, so its inverse is used on the source. The normalization for c
uses ρ at T_C P, and the last comparison uses theta at T_D M. The two projection
identities have opposite composition orders, as required. The B-multiplication
condition is on GB alone. The final scalar-presentation existential was moved before
the functor quantifiers so canonical scalar adjunctions and basis coordinates are
supplied, rather than assumed. Site universes were generalized and their common
coefficient maximum retained. No source claim or node statement was changed.

Validation: all compiler invocations use scompile.py and its fixed 60-second per-file
limit. The large theorem signature uses maxHeartbeats 800000 for elaboration; the
wall-clock limit is unchanged. Early compiler checks exposed missing explicit
sheafification interfaces, then a size constraint in the ordinary scalar adjunction.
The final interfaces use the common coefficient maximum, with no site universe
equality. Named irreducible Hom and finite-sum constructions reduce repeated unfolding.
