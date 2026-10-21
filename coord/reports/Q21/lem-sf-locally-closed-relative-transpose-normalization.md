## Worker report

The delivery states `AlgebraicGeometry.ProEtale.locallyClosedRelativeTransposeNormalization`
and `locallyClosedRelativeTransposeNormalization_refactor` in
`Sheaf.Paper.LocallyClosedRelativeTransposeNormalization`. Both theorem proofs are `sorry`;
every definition and instance has actual data. The helper declarations, all listed in
`lean.declarations`, only package the inputs and canonical maps of this one node.
No statement correction, new mathematical notion, or dependency repair is needed.

Hypothesis and clause correspondence:

- The global finite-field datum, prime distinct from the characteristic, finite extension
  and positive level are `P : WeilConjectures.PurityFiniteSetting`. Its fields are the
  recorded `FiniteFieldDatum`, `CoefficientDatum`, finite intermediate extension and
  `level_pos : 1 ≤ level`. `P.Ring` is the existing quotient O_E/(varpi_E^n), and
  `P.Coefficient = ULift P.Ring` is its standard coefficient-size lift. Its finite instance
  is `boundedSiteCoefficientFinite`, using the recorded finite-quotient theorem. An
  extension is represented in the fixed coefficient algebraic closure, as in the global
  coefficient convention; no hypothesis on ramification or divisibility is added.
  `def-pur-conventions` is added as a landed statement dependency for this existing bundle.
- `D : RelativeTransposeGeometry P` contains S,V,T, the structure maps `aS,aT`, their
  local finite type and quasi-compactness instances, and their separatedness instances.
  Its `c,v` are respectively closed and open; `over_base` says their composite is over k.
  `D.s` abbreviates exactly `D.c ≫ D.v`. Thus no factorization or isomorphism replacing
  the immersion is chosen. Noetherianity of T and V is derived in real instances; it is
  not added as a hypothesis. Quasi-compactness of s and of complementary opens is inferred
  from those hypotheses.
- Ordinary categories are `DerivedCategory (Sheaf ... (ModuleCat.{u+1} P.Coefficient))`
  on `smallEtaleTopology` and `Scheme.ProEt.topology`. The pro-etale site keeps object
  universe u+1 and morphism universe u. The recorded finite-coefficient realization
  identifies these with the constant-ring module categories; no structure-sheaf ring
  map is substituted.
- `D.Fe,D.Fp` are derived closed direct image followed by exact open extension, and
  `D.Je,D.Jp` are exact open restriction followed by the ordinary closed right adjoint.
  The etale closed adjoint is the universal-property-selected right adjoint supplied by
  the recorded existence theorem. The pro-etale closed adjoint is the actual derived
  `closedUpperShriek`, i.e. closed pullback of the kernel for the canonical complementary
  open. `D.adjE,D.adjP` use `Adjunction.comp`, with the published open adjunctions.
  Derived closed direct image agrees with termwise direct image by exactness: etale
  finite direct-image exactness, and the published complementary-open pro-etale theorem.
- `D.closure` has `Z := D.s.image`, `g := D.s.imageι`, `i := D.s.toImage`.
  Mathlib defines this image as `s.ker.subscheme`, with its canonical image inclusion and
  factor map. Thus this is the specified scheme-theoretic closure, not a freely supplied
  compactification, and includes nilpotent scheme structure. `D.Ee,D.Ep` are the existing
  ordinary compact-support functors at this compactification.
- `N : RelativeTransposeIdentifications D` retains the two termwise sheaf isomorphisms
  with `etale_normalized` and `proetale_normalized`. Each normalization explicitly says
  its pullback along s agrees with the canonical restriction identification. The etale
  restriction maps are the dependency's exact declarations. The pro-etale restriction
  maps use pullback composition, inverse open unit and closed counit, without choosing
  an arbitrary restriction isomorphism. `N.qE,N.qP` descend these maps termwise, using
  the published exact/right-derived identifications.
- The fixed identification J_e with s-times is implemented by `N.closureAdjunction :=
  D.adjE.ofNatIsoLeft N.qE`. In these coordinates the right adjoint is literally J_e;
  the counit is the pasted etale counit precomposed with q_e inverse. This is exactly
  the specified conjugate, not a second arbitrary adjunction. Consequently `D.G` is
  R-nu-star followed by J_e followed by C_S, the existing exceptional composite in
  these fixed coordinates.
- `D.CS,D.CT` are the recorded exact comparison pullbacks; R-nu-star is
  `comparisonLowerStar ... |>.rightDerivedFunctor`. The actual unit comes from
  `derivedComparisonAdjunction`, including in `D.rho := boundedSiteRho ...`.
- `relativeTransposeClosedComparison` includes the recorded counit mate
  `fixedComparisonDirectImageMatePlus` in the ordinary categories using only canonical
  bounded-below compatibility isomorphisms. `relativeTransposeOpenComparison` is the
  termwise published sheaf comparison. Their prescribed composition is `D.delta L`.
  `D.B L` is `compactSupportSiteComparison.symm.app L`, whose definition is precisely
  closed mate followed by closed pushforward of the open comparison at the closure.
  `N.square` is Delta followed by q_p equals C_T(q_e) followed by B, for every L in D+.
- `L : DerivedCategory.Plus ...` ranges over all bounded-below etale source complexes.
  `M : RelativeTransposeTarget D` consists of the actual etale object, the recorded
  `isBoundedConstructible` predicate, and `right_plus` for J_e M. No constructibility
  of L, perfectness, Tor amplitude, or cohomological dimension hypothesis is imposed.
- `γ : RelativeTransposeGamma D` retains the given isomorphisms, their naturality in
  every map of admissible M, and exactly the pasted-counit equation from the node.
  This is input, never an assumed equality of Hom functions.
- The main theorem's first two conjuncts are invertibility of `D.rho M.obj` and
  `γ.theta M`, where theta is defined as gamma inverse followed by rho.
- The next conjunct is `∃! h₀`, with `(D.delta L).hom ≫ h = D.CT.map h₀`.
  The following conjuncts render the two formulas using the actual pasted `homEquiv`
  and `N.phi`, with g_0 written explicitly as `D.adjE.homEquiv ... h₀`.
- `N.phi` is literally `boundedSiteTranspose` at `D.closure`, `D.Je` and the conjugated
  `N.closureAdjunction`. The main theorem also spells out its unit/U_T formula for
  every z. This identifies the actual chosen-closure function, not merely an unspecified
  bijection between the same Hom sets.
- The theorem identifies ambient transpose followed by theta with Phi after q_p inverse,
  asserts bijectivity of Phi and states its compatibility with the inverse ambient
  transpose. Its final two clauses explicitly evaluate the transported counit on
  J_p C_T M using the gamma witness, and the unit wherever the forward object is
  identified with C_T M. Equality of the actual Hom functions and their inverses also
  covers every identity evaluation defining a unit or counit within these domains.
- `relativeTransposeWitnessPhi` transports Phi by a retained isomorphism alpha using
  alpha inverse on the resulting source. The theorem quantifies over every such K,L,
  alpha, gives the transported normalization, and equates the functions for every pair
  of witnesses alpha,beta. No origin witness is chosen or discarded.
- Naturality in L is the explicit precomposition equation for b : L' → L.
  Naturality in M is stated both for theta and for the actual Phi with postcomposition
  by C_T(b). The assumed gamma naturality and the actual comparison unit are used.
- `RelativeTransposeRefactor N` retains an arbitrary second actual closed/open
  factorization c',v' of the same s, with both normalized sheaf maps to the same closure.
  The second theorem's `compatible` is exactly r_p Delta = Delta' C_T(r_e), with
  r_tau = q_tau followed by q'_tau inverse. Normalized uniqueness identifies these
  with every identity-normalized factorization change. No extra Delta/B closure
  square for the new factorization is assumed.
- `R.adjP` is the new actual pasted adjunction. `R.rightComparison` is exactly the
  conjugate of r_p inverse using `conjugateIsoEquiv`. The old etale right-adjoint
  coordinates are retained by the specified conjugation of q'_e. For every new gamma'
  satisfying its normalized counit equation, the refactor theorem gives gamma' = t gamma,
  t followed by theta' = theta, and equality of the actual closure arrows. It also
  states the identity and composition equations for these conjugate comparisons.
- All results concern bounded etale-origin tests and these targets. The ordinary closed
  support adjunction is used only to construct the specified local J_p. There is no
  assertion of an arbitrary-pro-etale compact-support exceptional adjunction.

Dependency declarations read and reused (their recorded modules are all publicly imported):

| Node | Declaration/interface used |
| --- | --- |
| def-weil-finite-field-fiber | `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`, `.CoefficientDatum` |
| def-weil-l-adic-coefficient-extension | `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`, existing quotient |
| def-weil-closed-immersion | `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`, `IsImmersion` |
| def-weil-open-immersion | `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion` |
| def-weil-finite-type-morphism | `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, `QuasiCompact` |
| def-weil-proper-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsSeparated`, `IsProper` |
| def-weil-pbc-derived-categories | `WeilConjectures.AlgebraicGeometry.DerivedCategories`: `Etale.DerivedCategoryModule`, ordinary `DerivedCategory` and `.Plus` |
| def-weil-pbc-proetale-modules | `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: fixed-scalar realization and equivalence with `FiniteCoefficientModules` |
| lem-exc-closed-ambient | `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`: `Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion` |
| lem-exc-proetale-closed-support | `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedAmbient`: intrinsic adjunction; its published fixed-scalar counterpart `ProEtale.derivedLowerStarClosedUpperShriekAdjunction` in `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedImmersion` |
| def-weil-pbc-composite-adjunction | Mathlib `CategoryTheory.Adjunction.comp` |
| def-weil-pbc-extension-by-zero | `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`: `Etale.openImmersionLowerShriek` |
| def-weil-extension-by-zero | `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`: canonical realization of the same fixed-scalar `ProEtale.openImmersionLowerShriek` |
| def-nagata-scheme-theoretic-image | `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`: `Scheme.Hom.image`, `.imageι`, `.toImage` |
| lem-sfb-etale-locally-closed-extension-comparison | `Sheaf.SixFunctors.EtaleLocallyClosedExtensionComparison`: normalized restriction isomorphisms and comparison uniqueness |
| lem-sfb-locally-closed-extension-coherence | `Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence`: normalized module/derived extension coherence |
| def-amb-etale-compact-support | `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`: `Etale.rightDerivedLowerShriekOfCompactification` |
| thm-amb-etale-exceptional-adjoint | `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`: ordinary compact-support adjoint existence |
| def-weil-pbc-adjunction-conjugate | Mathlib `CategoryTheory.conjugateEquiv`, `conjugateIsoEquiv`, `Adjunction.ofNatIsoLeft` |
| def-weil-pbc-site-comparison-morphism | `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `Scheme.proEtaleSiteComparison`, module comparison constructions |
| thm-weil-pbc-site-comparison | `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`: actual comparison unit; unbounded-on-D+ unit theorem reexported by the fixed derived comparison |
| def-weil-exceptional-inverse-image | `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`: retains the finite `sfFiniteExceptionalAt` through its public imports; `D.G` uses the specified conjugated etale right-adjoint coordinates |
| lem-weil-pbc-comparison-direct-image-canonical-mate | `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`: `fixedComparisonDirectImageMatePlus`, `isIso_fixedComparisonDirectImageMatePlus` |
| lem-cbc-proetale-extension-zero-comparison | `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`: `openImmersionLowerShriekComparisonUpperStarIso` |
| def-weil-pbc-constructible-complexes | `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`: `Etale.DerivedCategory.isBoundedConstructible` |
| lem-pur-bounded-site-adjunction-transpose | `Sheaf.Paper.BoundedSiteAdjunctionTranspose`: `boundedSiteTranspose`, `boundedSiteRho` |
| thm-sf-ambient-adjoint-class | `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`: specified compactification/class Hom-chain interface |

The fixed-scalar counterpart of the intrinsic pro-etale support adjunction is already
published; it is not restated here. The intrinsic extension's definition itself transports
the fixed-scalar open extension used here. Thus these recorded dependencies are usable
via their existing realization interfaces and need no lean-only repair.

Edge cases checked by reading the constructions and the displayed types:
identity immersion; open-only and closed-only factorizations; S empty or T empty;
L zero; M zero; positive level n=1; arbitrary finite ramification; nilpotent closure
structure; distinct etale-origin witnesses; and a nontrivial rescaling of gamma.
No nonemptiness or dimension assumption is imposed. In the empty case there is no
maximum over charts. A rescaled gamma must still satisfy the actual counit equation;
there is no unconditional arbitrary-isomorphism normalization. Complementary open
choices use the actual set complement and do not impose a new hypothesis.

Searches executed with the prescribed msearch.py wrapper:

- LeanFinder: “For a locally closed immersion compare the exceptional adjunction
  transpose with the compact support transpose using the etale to proetale comparison
  unit”. Eight hits: generic restriction adjunction/unit/counit formulas, none the node.
- Loogle: `CategoryTheory.Adjunction.homEquiv, CategoryTheory.Adjunction.counit`.
  Twelve generic adjunction hits, including `homEquiv_symm_apply` and uniqueness/counit
  formulas; none states the locally closed scheme/site normalization.
- LeanSearch: “Locally closed immersion exceptional inverse image adjunction transpose
  compatible etale proetale comparison unit”. Eight generic comparison/adjunction hits,
  none the node.
- Mathlib grep: `homEquiv_symm_apply|homEquiv_naturality_right`, `CategoryTheory`.
  Twenty-five generic adjunction uses; no scheme/site statement.
- Local rg in both `lean/WeilConjectures` and `lean/Sheaf`:
  `relativeTranspose|locallyClosedRelativeTranspose`; zero hits before this delivery.
  Exact node-id search in `lean/WeilConjectures` also gave zero hits. Broader normalization
  searches exposed the existing bounded-site transpose and specified class Hom interface,
  reused directly rather than redefined.

Source inspected: main-20261015
`sec-smooth-purity/sk-lem-sp-tower/lem-weil-finite-duality-site-comparison.proof.md`, second
paragraph. Component proof references are Stacks 03QP (finite exactness), 03DJ (open exactness),
099V (comparison full faithfulness), 0037 (adjunction formulas), 0B65 (conjugation),
01R6--01R8 (image/closure), and 09BM (closed pro-etale support).

## Second reading by Q21

I reopened the node and the completed module for a separate clause-by-clause reading.
The dispatcher explicitly prohibits starting another agent, so this is a second pass by
this worker, not an invented independent reviewer. The maintainer's independent review
remains the review of the delivered result.

I checked that Fe and Fp have closed-then-open order, while the closure Ee and Ep have
open-then-closed order; that q goes from F to E; that gamma goes from C_S J_e M to J_p C_T M;
and that theta consequently has gamma inverse before rho in Lean composition order.
The lift condition is Delta followed by h, the closure arrow is q_p inverse followed by h,
and the explicit Phi uses eta at E_e L followed by U_T(B followed by z). The conjugated
closure adjunction retains J_e, so its transpose of q_e inverse followed by h_0 is the
same g_0. The retained gamma family includes actual naturality and the precise counit
normalization. All these directions agree with the node.

The first draft only identified the Hom functions, leaving units/counits implicit.
I added explicit counit and unit evaluations, plus the inverse-transpose and Phi
naturality equations. The refactor clause uses actual second c',v', normalized q'
and the stipulated Delta compatibility, and states the conjugate gamma/theta equations
and identity/composition. I verified that it does not assume the conclusion as a
compatibility hypothesis. The geometric domain adds no compactness, Noetherianity,
dimension, Tor, nonemptiness or constructibility-of-L restriction. The final file has
`autoImplicit false`, explicitly declared universe u and only named postponed theorems.
No remaining mathematical mismatch or disputed statement was found in this pass.
