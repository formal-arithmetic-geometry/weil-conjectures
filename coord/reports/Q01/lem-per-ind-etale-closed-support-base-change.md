## Worker report

The delivery states `lem-per-ind-etale-closed-support-base-change` in
`Sheaf.AlgebraicGeometry.IndEtaleClosedSupportBaseChange`. All four theorem proofs are
`sorry`; every definition and the shift instance have actual data. There are no new DAG
nodes, dependency-record repairs, or changes to the natural statement.

The source read was Stacks `etale-cohomology.tex`, `theorem-higher-direct-images`
(Tag 03Q9, including its D+ complex version), `lemma-sections-with-support-acyclic`
(Tag 09XQ, including the preceding definition and Hom adjunction), and
`lemma-cohomology-with-support-triangle` (Tag 0A45, including the injective-resolution
proof). The node assembles these with strict-local invariance, rather than quoting a
single source theorem. Its eleven proof steps are included in the main theorem docstring;
the composition and identity docstrings give their respective transposition arguments.

Hypotheses and clauses, matched to Lean:

* Finite commutative coefficients: the section binds `A : Type (u + 1)` with
  `[CommRing A] [Finite A]`. The universe is the existing six-functor coefficient
  convention. It permits every finite ring, including the zero ring, with no restriction
  on characteristic or invertibility of an integer.
* Noetherian source and target: `[IsNoetherian T] [IsNoetherian T']`. The Mathlib
  `isNoetherian_iff_of_finite_iSup_eq_top` identifies this with a finite affine cover
  whose rings are Noetherian, exactly the node's explicit convention.
* Affineness: `[IsAffineHom g]`, which means inverse images of affine opens are affine.
* Locally ind-etale: `hg` gives, at each `t : T'`, affine open neighborhoods `V,U`,
  a morphism `e : V.toScheme ⟶ U.toScheme`, the equation
  `e ≫ U.ι = V.ι ≫ g`, and
  `RingHom.IndEtaleAcrossUniverses e.appTop.hom`. Membership `t ∈ V` and that
  equation also ensure `g(t) ∈ U`. The dependency's canonical ULift predicate is
  used without replacing its filtered-colimit notion by weak etaleness. This is the
  usual local affine-chart formulation; it neither assumes absolute affineness of T
  nor forces the two rings into a common original universe.
* Closed immersion: `[IsClosedImmersion i]`. The square has a closed base-changed
  immersion `i'`, with `[IsClosedImmersion i']`, which is a derived property of a
  pullback of i, not an additional geometric restriction.
* Cartesian square and its maps: `sq : IsPullback h i' i g`. Quantifying over a
  pullback square is the invariant formulation of the chosen `pullback i g` and its
  projections: the chosen fibre product instantiates it, and the universal property
  identifies any such square uniquely with it. No alternate square relation is used.
* Small etale sites and modules over the constant ring sheaf: the categories are
  `_root_.DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat A))` and
  their analogues for Z, T', Z'. This is the dependency's established module-valued
  encoding of modules over the constant sheaf, not a new sheaf-of-rings encoding.
* The functor i!: `closedSupportPlus` is the right adjoint of
  `(lowerStar (ModuleCat A) i).rightDerivedFunctorPlus`. The named theorem
  `closedSupportPlus_isLeftAdjoint` supplies this universal property by the
  supported-kernel adjunction, restriction of its natural Hom bijection to scalar
  endomorphisms, and `Adjunction.derivedPlus`. Since closed direct image is exact,
  this is precisely R of `i^{-1} ker(1 → j_*j^{-1})`. Choosing a right adjoint
  determines the functor together with its adjunction up to the unique
  counit-compatible isomorphism; it does not choose an unspecified object from a
  bare existence claim. The selected counit corresponds to the derived support
  inclusion under that unique identification. The open complement is determined
  by i; it is not additional input to the existence assertion.
* Exact g*, h*: `(upperStar (ModuleCat A) g).mapDerivedCategoryPlus` and the same
  for h apply the existing exact inverse-image functors levelwise. Closed i*, i'*:
  the existing `lowerStar` right derived functors agree canonically with levelwise
  direct image by exactness of a closed (hence finite) direct image.
* Canonical comparison and naturality: `closedSupportBaseChangePlus` is a natural
  transformation `closedSupportPlus A i ⋙ h* ⟶ g* ⋙ closedSupportPlus A i'`.
  Its definition applies `mateEquiv` to the inverse of the exact existing
  `derivedBaseChangeMapPlus (ModuleCat A) sq`. There is no arbitrary exchange map
  parameter. The helper `closedSupportExchangeInverse` uses the inverse when that
  natural transformation is invertible and zero otherwise; the first conjunct of
  the theorem asserts invertibility on every square at issue, so the extension is
  never used there.
* Isomorphism on every K: the second conjunct is `IsIso` of this natural
  transformation, and hence gives a natural isomorphism on all of D+.
* Counit normalization: the final universal equation in the main theorem reads
  `c.app (i!.obj K) ≫ i'_*.map (beta.app K) ≫ epsilon'.app (g*.obj K) =
  g*.map (epsilon.app K)`. This is exactly the equation in the node, with Lean's
  left-to-right composition order. The adjunctions used here are exactly those
  used in the mate definition.
* A-linearity: all categories are derived categories of A-module sheaves, every
  displayed morphism is a morphism there, and the mate is formed using their
  adjunctions. There is no forgetting to abelian groups in the statement.
* All cohomological shifts: `NatTrans.CommShift ... ℤ`. The closed right adjoint
  has the canonical `rightAdjointCommShift` structure transported from direct
  image through its adjunction; pullback and direct-image shift structures are
  the existing derived ones. This asserts compatibility with the canonical
  isomorphisms, not equality of untransported shifted objects.
* Composition: `indEtale_closedSupport_baseChange_comp` binds two successive
  affine locally ind-etale maps between Noetherian schemes and two pullback
  squares, and compares the map of their horizontal composite with h₂* of the
  first map followed by the second. Both sides are transported by precisely
  `upperStarCompDerivedPlus` for h₂,h₁ and g₂,g₁. Its displayed paths have source
  `(h₂ ≫ h₁)* i! K` and target `i₂! g₂* g₁* K`.
* Identity: `closedSupport_baseChange_id` compares the identity square with the
  two canonical `upperStarIdDerivedPlus` identifications. It records the identity
  coherence explicitly.
* No constructibility: K ranges over all of `DerivedCategory.Plus` in every
  assertion, with no predicate on its cohomology sheaves.

Statement dependencies read and reused:

* `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing` and `isNoetherianRing_iff_ideal_fg`; the scheme convention is
  Mathlib `IsNoetherian` as explained above.
* `def-weil-pbc-ind-etale-algebra`: `Sheaf.RingTheory.IndEtaleUniverseTransport`,
  `RingHom.IndEtaleAcrossUniverses`. Its definition uses the original
  `RingHom.IndEtale` on the canonical ULift map. The imported
  `IndPrincipalZariski` and upstream `IndEtale` definitions were inspected.
* `def-weil-closed-immersion`:
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `IsClosedImmersion`.
* `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.lift`; here its universal property
  is expressed as `IsPullback`.
* `def-weil-pbc-derived-categories`:
  `WeilConjectures.AlgebraicGeometry.DerivedCategories` and its imported
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`;
  `DerivedCategory.Plus`, `Etale.DerivedCategoryModule`. The recorded source
  was absent in the older local source tree, so its current full source was
  read with `scompile.py --source WeilConjectures.AlgebraicGeometry.DerivedCategories`.
* `def-pur-etale-supported-kernel`:
  `Sheaf.AlgebraicGeometry.EtaleSupportedKernelAdjunction`, `supportedKernel`
  and `supportedClosedInverseImage`, and its `supportedKernel_closedAdjunction`.
  These are the abelian versions used in deriving the module-valued adjunction;
  no duplicate kernel definition is introduced.
* `def-weil-pbc-constant-sheaf`:
  `Mathlib.CategoryTheory.Sites.ConstantSheaf`, `constantSheaf` (sheafification
  of the constant presheaf); used through the established ModuleCat encoding.
* `def-weil-pbc-inverse-image` and `def-weil-pbc-direct-image`:
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, `upperStar`,
  `lowerStar`, `upperStarLowerStarAdjunction`; bounded-below direct image is
  `rightDerivedFunctorPlus` as in the recorded derived direct image interface.

The proof modules recorded on the node are imported without `public`, including
`PlusAdjunction`, strict-local invariance, strict-local global homology,
forgetting coefficients, stalk conservativity, the cohomology ladder and five
lemma. The single omitted recorded proof import is
`Sheaf.SecSmoothPurity.DerivedExchangeCube`: compiling the required import
reported `cannot import non-module Sheaf.SecSmoothPurity.DerivedExchangeCube
from module`. Its file must be migrated by its owner before that proof import
can be enabled. Its mathematical use remains explicitly Step 8 of the docstring.
No dependency file or live module was changed to circumvent this.

Edge cases checked from the formulas: Z empty makes the supported right adjoint
zero; Z=T makes it the identity under the closed adjunction. The same mate and
counit formulas work in both cases. The zero coefficient ring gives zero module
categories. T or T' empty is allowed; in the latter case the local ind-etale
condition is vacuous for the correct reason and all sheaves there are zero.
Identity base change has its own equation. Arbitrary positive, zero, and negative
shifts are covered by ℤ, and arbitrary bounded-below nonconstructible complexes
are retained. The square formulation also admits replacing a chosen fibre
product by its canonical isomorphic presentation.

Searches performed:

* msearch LeanFinder: `Extraordinary inverse image for a closed immersion of etale
  sites commutes with ind etale base change`: eight hits on etale categories and
  ordinary etale base change, no supported exceptional base-change theorem.
* msearch Loogle: `CategoryTheory.Adjunction, Functor.rightDerived`: zero hits;
  it reports the identifier `Functor.rightDerived` unknown, rather than an
  exhaustive search failure. The actual API was located by source inspection.
* msearch grep: `supportedClosedInverseImage|IndEtale|extraordinary`: two hits
  about extraordinary homology in manifold bordism, no match.
* msearch LeanSearch: `Etale sheaves closed immersion supported kernel right
  adjoint base change ind etale`: eight hits on ideal-sheaf kernels, closed
  immersion isomorphisms, and the ordinary scheme-module restriction adjunction;
  no exact match.
* rg in the upstream WeilConjectures tree by the item id, `supportedKernel`,
  `supportedClosedInverseImage`, and ind-etale/extraordinary support keywords:
  no exact existing theorem. The general finite exactness and derived exchange
  modules were found and reused.
* rg in `lean/Sheaf`: the exact abelian `supportedKernel` definition and adjunction
  were found and reused. Existing closed ambient right adjoints and support triangles
  were also inspected; they concern unbounded categories, not the normalized D+
  base-change interface of this item. Searching the proposed `closedSupportPlus`
  and `closedSupportBaseChangePlus` names gave no prior definitions.

Validation: the final module (including composition and identity statements)
compiled through `scompile.py` as both a sandbox module and its actual library
module, each in about four seconds, with no errors or warnings. Compilation was
only through the authorized wrapper; no global build was run. All universes and
variables are bound, lines are at most 100 characters, and the Lean record's
main signature is copied verbatim from the module.

No statement dispute or source correction is needed.

## Second reading by Q01

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
