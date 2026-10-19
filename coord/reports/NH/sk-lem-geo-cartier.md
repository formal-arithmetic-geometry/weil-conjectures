## Worker report

The module `Sheaf.AlgebraicGeometry.GeoCartierCycleClass` states
`AlgebraicGeometry.ProEtale.exists_geoCartierCycleClass`. Its only theorem has proof
`sorry`. Its twelve auxiliary definitions contain real data or explicit predicates
for the very objects and diagrams of this statement; none chooses a class from an
undetermined existence theorem. No statement correction or disputed statement is needed.

The source is the current main-20261015 blueprint unit
`sec-six-functors-basics/sk-lem-geo-cartier/_section.md`, together with all eight
proof steps of the DAG node. The unit states existence of the supported pro-etale
class, its Chern equation, coefficient change, and all Cartier-preserving base changes.
The expanded node additionally spells out the finite coefficient line and independence
of the killing exponent; those are retained.

Hypotheses and objects, individually:

* Prime ℓ is `(ℓ : ℕ) (hℓ : ℓ.Prime)` in the theorem.
* An integer exponent r ≥ 1 is `(r : ℕ) (hr : 0 < r)` in the simultaneous
  `GeoCartierClassFamily`. Using naturals here covers exactly the allowed integers.
* A finite commutative Z/ℓ^r-algebra is `(A : Type (u + 1)) [CommRing A] [Finite A]`
  with `hA : ((ℓ ^ r : ℕ) : A) = 0`. The unital ring structure map from Z/ℓ^r
  is unique, namely `Scheme.finiteEtaleTwistScalar`, already used by the Tate line.
  Consequently every unital `φ : A →+* B` in the coefficient clause is exactly an
  algebra homomorphism over this ring; there is no missing extra compatibility.
* The schemes are arbitrary `{D Z : Scheme.{u}}`. A divisor is `(i : D ⟶ Z)`
  with `[IsClosedImmersion i] (hI : i.ker.IsInvertible)`. The recorded upstream
  `isEffectiveCartierCenter_iff_isInvertible_ker` identifies precisely these
  hypotheses with the effective Cartier divisor, locally cut out by a nonzerodivisor.
* Invertibility of ℓ is rendered by `hZ : IsUnit ((ℓ ^ r : ℕ) : Γ(Z, ⊤))`.
  For r > 0 this is equivalent to ℓ being invertible; being a unit globally is
  equivalent to being a unit at every local ring. No geometric condition is added.
* Ordinary small pro-etale module sheaves are the fixed-scalar presentation
  `Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)`. The recorded
  `finiteCoefficientRealization` is the canonical associated-module-sheaf
  equivalence with the continuous-function coefficient-sheaf category in
  def-weil-pbc-proetale-modules. Its exactness and equivalence declarations are
  already published. Thus this is the ordinary category, with the specified site
  (object universe u+1, morphism universe u), rather than a condensed category.
* `geoCartierConstant A D` is the actual constant sheaf of A-modules. The source
  of `GeoCartierClass` is `(ProEtale.lowerStar (ModuleCat A) i).obj` of this
  sheaf, i.e. ordinary sectionwise closed direct image. It is not an arbitrary
  isomorphic support object or an assumption of an unspecified exchange.
* `geoCartierLine A N hA Z` is literally `comparisonUpperStar.obj` of the
  existing `Scheme.finiteEtaleTateLine Z N A hA`. That existing sheaf is the
  sheafified tensor A ⊗[ZMod N] μ_N, canonically μ_N ⊗ A by symmetry, with the
  powers action of ZMod N on the kernel of N on G_m. No Tate line is redefined.
* `GeoCartierClass` is `Ext source line 2`. The existing canonical
  `CategoryTheory.Abelian.Ext.homEquiv` identifies it with the requested arrow
  `single₀(i_* A_D) ⟶ single₀(A_Z(1))⟦(2 : ℤ)⟧`; concretely a family member's
  `.hom` is that derived arrow. Exact-functor Ext maps and Ext composition below
  are the same derived inverse image and composition through this equivalence.

Conclusions and canonical maps, individually:

* The outer `∃ c : GeoCartierClassFamily ℓ` is simultaneous in schemes, divisors,
  exponents and finite rings, so all compatibility clauses compare actual members
  of the same family. It is not a separate, unrelated existential at every square.
* `geoCartierSourceComparison` is the published comparison mate
  `lowerStarComparisonUpperStarBaseChange`, followed by direct image of
  `comparisonUpperStarConstantSheafIso`. The first conjunct asserts its
  invertibility. The relative-boundary equation in the last part of that conjunct
  specifies the canonical construction: precomposing c by that comparison is
  `κ.mapExactFunctor comparisonUpperStar`, with κ satisfying the already-recorded
  `Etale.SupportedKummerBoundary`. This is the extension/torsor construction in the
  source proof, expressed using its existing interface.
* `GeoCartierChernEquation` requires an etale module class c₁ whose image after
  exact scalar forgetting and evaluation on the integral generator is precisely
  `Etale.supportedKummerChern A N hA i hI hZ`. That existing definition applies
  `Scheme.kummerδ₁` to the Picard class of `Scheme.Modules.dual i.ker.toModules`
  and then the actual roots scalar map. The recorded module/abelian cohomology
  comparison makes this the unique module-derived Kummer Chern class; it is not an
  arbitrary class satisfying a vacuous normalization. The second equation is
  exactly unit followed by c equals ν*c₁, with the published comparison of constants
  on the source. Its unit is `Scheme.proEtaleConstantDirectImageMap`, the actual
  adjunction unit followed by the canonical inverse-image identification of constants.
* Every coefficient map is explicitly universally quantified as `φ : A →+* B`
  for finite commutative coefficient rings killed by ℓ^r. In
  `GeoCartierScalarCompatibility`, η sends each local constant a to φ(a), and θ
  sends each comparison image of a pure root tensor a ⊗ z to φ(a) ⊗ z. The
  comparison adjunction unit on etale objects supplies those generators. These
  are canonical sheaf maps: constant-sheaf and sheafification adjunctions determine
  them from those formulas. The two `GeoCartierScalarUnit` conditions state their
  derived extension universal properties against **every unbounded derived object**.
  Thus these conditions identify derived scalar extension of the supported constant
  and of the line with the displayed B-objects. The final Ext equality is the
  adjoint form of the requested derived scalar-extension square, under exactly
  these units. No coefficient-flatness or chosen alternative scalar functor occurs.
* `GeoCartierBaseChange` universally quantifies arbitrary g and gD and
  `sq : IsPullback gD i' i g`, with effective Cartier hypotheses for both divisors.
  Giving an arbitrary pullback square includes the chosen fibre-product square
  and every canonically isomorphic realization. It adds no flatness hypothesis.
  hZ' is the invertibility already inherited from hZ, made explicit to index c.
  `geoCartierExchange` is defined as the adjoint of inverse-image commutation,
  followed by the pulled-back counit and canonical constant inverse-image map.
  This is precisely the canonical exchange specified by the node. Its invertibility
  is asserted, not assumed. `geoCartierLinePullback` composes the published
  comparison square with the roots-normalized line isomorphism. The final Ext
  equality is pullback(c) followed by this line comparison equals exchange followed
  by c on the pulled-back divisor. `OrdinaryFiniteTwistTransport` pins roots by
  inclusion into G_m and line maps by pure tensors, excluding arbitrary isomorphisms.
* `GeoCartierExponentIndependence` quantifies r ≤ s with r,s positive and the
  same ring killed by ℓ^r. The extra written proof hA' of killing by ℓ^s and
  hZ' of invertibility of ℓ^s are automatic consequences, serving only as indices
  for the same family. It specifies q on roots by
  `q ≫ kernel.ι = (ℓ^s / ℓ^r) • kernel.ι`, which is the powers projection in
  additive notation. The line isomorphism e is required to send a ⊗ z to
  a ⊗ q(z). The final equality transports c at exponent s by ν(e) to c at
  exponent r, exactly retaining independence of the exponent.

Recorded dependency declarations read and used (modules and names):

* `WeilConjectures.AlgebraicGeometry.EffectiveCartier`,
  `Scheme.IdealSheafData.IsInvertible.isInvertible_dual_toModules`, and its imported
  `Scheme.Modules.dual`, `IdealSheafData.toModules`, `IsEffectiveCartierCenter`,
  `isEffectiveCartierCenter_iff_isInvertible_ker`: dual Cartier ideal and its hypotheses.
* `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`,
  `ProEtale.FiniteCoefficientModules`, `finiteCoefficientRealization`,
  `finiteCoefficientRealization_exact`, `finiteCoefficientRealizationIsEquivalenceRing`,
  `finiteCoefficientDerivedComparison`: prescribed ordinary coefficient category and
  its fixed-ring presentation. These are imported through ComparisonDerivedPullbackFixed.
* `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`,
  `Scheme.proEtaleSiteComparisonModules`: the recorded module comparison is exactly
  the upstream `ProEtale.comparisonAdjunction`, with `comparisonUpperStar` its inverse image.
* `WeilConjectures.AlgebraicGeometry.Sites.Kummer`,
  `Scheme.kummerSequence`, `rootsOfUnitySheaf`, `kummerSequence_shortExact`, `kummerδ₁`;
  `WeilConjectures.AlgebraicGeometry.Sites.Gm`, `Scheme.gmSheaf`: the actual Kummer data.
* `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`,
  `Scheme.finite_etale_torsion_twist_line`, with the imported
  `Scheme.finiteEtaleTateLine`, `finiteEtaleTwistScalar`: finite roots tensor and flatness.
* `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`,
  `ProEtale.siteComparisonDerivedPullbackPlus`: the recorded bounded-below version;
  the unbounded exact inverse image used here is the same
  `comparisonUpperStar.mapDerivedCategory`, or its canonical map on Ext.
* `WeilConjectures.AlgebraicGeometry.Sites.GmPicard`,
  `Scheme.nonempty_equiv_quotient_torsor`, `picEquivQuotientTorsorGmSheaf`;
  `WeilConjectures.CategoryTheory.Sites.Torsor`,
  `Sheaf.nonempty_equiv_H_one_torsor`: identify the generator torsor and its H1 class.
  Their actual Chern class is reused via `supportedKummerChern`, not copied.
* `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`,
  `SheafOfModules.DerivedChangeOfRingsCochainModel`,
  `nonempty_derivedChangeOfRingsCochainModel`: proof dependency for derived scalar extension;
  the statement expresses its normalized extension-unit universal property directly.
* `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
  `Etale.upperStar`, `upperStarLowerStarAdjunction`: etale inverse image in the
  recorded transport and canonical relative boundary.
* `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`,
  `Scheme.etaleFiniteTwistPullback`: roots-normalized transport and exponent projection.
* `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`,
  `Scheme.proEtaleSheafInverseImage`, `proEtaleSheafDirectImage`,
  `proEtaleConstantDirectImageMap`, `proEtaleConstantInverseImageMap`,
  `proEtaleConstantModuleDirectImage`: actual module inverse/direct images. The fixed-scalar
  `ProEtale.upperStar/lowerStar` have the same sectionwise action in the canonical
  realization, so no dependency repair or competing inverse image is needed.
* Two already-landed statement dependencies are added to cite existing notation used
  here: `def-asd-ordinary-supported-kummer-boundary` from
  `Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary`, with
  `Etale.SupportedKummerBoundary` and `supportedKummerChern`; and
  `def-asd-ordinary-finite-p1-arrows` from
  `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows`, with
  `Etale.OrdinaryFiniteTwistTransport`. Their source signatures and docstrings were read.
  No new DAG node or dependency replacement is introduced.

The module also imports each available recorded proof-dependency module, without
`public` where the statement does not need it. The two proof prerequisites that currently
lack Lean declarations (divisible-extension-derived-reduction and exponent-independence)
are documented in the theorem proof but are not prerequisites to type its signature.
No missing statement notion is being deferred to them.

Edge cases checked before writing and again against the signature: empty Z and empty D
are allowed, with zero supported object; the unit ideal gives the empty Cartier divisor.
The identity of a nonempty scheme is not a Cartier divisor and is correctly excluded by
invertibility of its zero ideal. For the empty scheme the identity is allowed and all
classes are zero. The zero coefficient ring is included; its rank-one module is zero.
Nonflat coefficient maps such as Z/ℓ² -> Z/ℓ and nonflat base changes whose pulled-back
equation stays regular are included. r=0 is excluded exactly as the node requires; r=s
uses the identity roots projection, while s>r uses the correct power, not root inclusion.
No roots of unity, orientation, connectedness, regularity, reducedness, noetherianity,
separatedness, coefficient flatness, or geometric flatness is chosen or assumed.
All scheme and coefficient universes and variables are explicit with autoImplicit false.

Searches for an existing full statement:

* `msearch.py ... leansearch "effective Cartier divisor cycle class in etale derived category"`:
  eight generic site, derived-category, and ring-etale hits; no Cartier class statement.
* `msearch.py ... leanfinder "effective Cartier divisor cycle class supported constant sheaf
  Tate twist degree two compatible base change coefficient extension"`: eight generic
  scheme sections/localization hits; no matching class construction.
* `msearch.py ... loogle "cycleClass, firstChern, IsEffectiveCartierCenter"`:
  zero hits, unknown cycleClass identifier.
* `msearch.py ... grep "cycleClass|cartier.*class|Cartier.*[Cc]lass" AlgebraicGeometry`:
  zero Mathlib hits.
* `rg -n 'geo-cartier|cycleClass|cartierCycle|CartierCycle'` in WeilConjectures and
  lean/Sheaf: GeoCartierCoeffExtension provides only the coefficient-source comparison;
  the other cycleClass hit is an unrelated support-cohomology representative. Broader
  Cartier/Kummer searches found the etale OrdinarySupportedKummer interfaces, reused here.
* Search for every new `geoCartier`/`GeoCartier` declaration name in
  dag/lean_names_upstream.json, WeilConjectures and lean/Sheaf found only the distinct
  existing `geoCartierCoeffExtension` theorem, hence no name collision or full statement.

Validation: the file passed scompile.py's sandbox and library checks, with no warnings
or errors. A second wrapper pass verifies the final proof-import list. No global build
or direct compilation outside the wrapper was run. Dry-run and delivery outcomes are
recorded below after running the prescribed wrappers.

## Second reading by NH

This is an author's second reading, not an independent review; the dispatch brief assigns
independent review to the maintainer and prohibits spawning another agent.
I reopened the node, its current unit and all its dependency records, then read the final
module clause by clause. The checklist above records each binder, derived object, map
normalization and equality. The first compile caught that `(ℓ ^ r : A)` is ring power
rather than the cast of a natural power required by the existing line interface; all such
binders now explicitly cast `(ℓ ^ r : ℕ)`, including on global sections. The compiler also
caught an unqualified `toProEt`, now `Scheme.toProEt`. No mathematical hypothesis changed.
The second reading verified the exchange orientation: i'^*g^* -> gD^*i^*, then the counit,
then the constant comparison. It checked that the scalar square is a derived scalar
square through its unbounded universal properties, that θ is fixed on comparison-unit
images of pure root tensors, and that the exponent equation goes from the larger roots
to the smaller roots by the quotient power. It confirmed that the Chern class uses the
dual ideal, which fixes its sign, and that all family members compared in the three
naturality clauses share the same c. No statement mismatch remains.

Delivery validation: `deliver2.py NH sk-lem-geo-cartier --no-push` returned
`OK (dry run): commit 894c80de29 passes the preflight and compiles; nothing pushed`.
Both sandbox and library checks of the final module passed without warnings or errors.
