## Worker report

This repairs the returned stage-1 packet at immutable head 67121fa9ef4a by supplying an
actual stage-2 module, `Sheaf.Paper.OrientedProperFibreExchange`, with primary declaration
`AlgebraicGeometry.OrientedNearbyCycles.ProperFibre.properFibreExchange`. The sandbox
initially contained only dispatcher marker files, with no retained module, node, or report.
The item node was copied from the shared reviewed node, retaining its seven proof steps,
proof_deps, split_report, tool_uses and reviewed record verbatim. Only lean and the permitted
addition of an already landed statement dependency change. There is no statement correction.

The source was read in Orgogozo's author PDF, Lemma 9.1.1 on printed pp. 19–20, including
the two consequences immediately before Proposition 9.1.2. It computes the proper oriented
direct-image stalk by cohomology of the geometric fibre and deduces arbitrary base change
and first-projection exchange. The Lean module includes the reviewed seven-step proof,
including initiality of each component of the affine triple system, and preservation of
K-injectivity by j* because its left adjoint j! is exact. It does not restore the invalid
argument about a right adjoint preserving K-injectives.

Hypothesis and clause correspondence:

- The schemes and maps X → Y → S are `{X Y S : Scheme.{u}}`, `h`, `g`; the composite f is
  `h ≫ g`. Properness is `[IsProper h]`, the recorded Mathlib notion.
- The commutative ring is `(Λ : Type v) [CommRing Λ]`; its annihilating positive integer is
  `(m : ℕ) (hm : 1 ≤ m) (hΛ : (m : Λ) = 0)`. This is equivalent to a positive integer
  annihilating Λ. No nontrivial-ring instance is required, including when m = 1.
- The derived categories are the recorded `VanishingDerived` and `EtaleDerived`, with the
  same `Coeff` universe transport and constant-module `Morphism.pull`, `push`, and `adj`.
  `IsBoundedBelow V R A` is only an abbreviation for Mathlib's standard
  `DerivedCategory.TStructure.t.plus A`: an integer lower cohomological bound. No upper
  bound or constructibility predicate occurs. The scheme universe u and coefficient
  universe v remain independent.
- The two geometric points use arbitrary algebraically closed fields `Ω Ξ : Type u`,
  `y : Spec (.of Ω) ⟶ Y` and `t : Spec (.of Ξ) ⟶ S`. The specialization c is the actual
  morphism `strictHenselizationScheme t ⟶ strictHenselizationScheme (y ≫ g)` over S;
  `hc` explicitly expresses the over-S condition inherent in a geometric specialization.
- `strictLift_existsUnique` characterizes the strict-local limit leg by its over-base and
  closed-point evaluation equations. `specializedLift` composes that leg with c and
  evaluation at t. `specializationPoint` and `specializationDirect` therefore represent
  this prescribed specialization, with its germ restriction mate. No arbitrary stalk
  transformation is supplied as a hypothesis or selected by mere existence.
- The point z is `pointLift g y t c hc`, the recorded universal compatible lift of y, t
  and `pointOrientation`. `pointComposition` uses the existing pullback-of-pointed-lifts
  comparison (`pointSmallEtaleComapIso` and `sheafFiberComapIso`), fixing its normalization.
- The scheme X_y is Mathlib `pullback h y`, with its first and second projections. This
  uses the scheme fibre product, rather than a set of geometric lifts.
- `fibreGlobal h y` is the sections morphism of the fibre: its direct image first pushes
  to Spec Ω and then takes the identity geometric-point stalk. Étale sheaves on an
  algebraically closed field are sets, so this stalk is global sections. `fieldSections`
  is the inverse of that particular geometric point equivalence; `fieldUnit` uses the
  adjunction unit. Thus `globalModules h y` is the usual global-sections morphism, and
  its `push` is the K-injective RΓ of the node.
- `fibreLift h g y t c hc` constructs φ_z with the actual first component `pullback.fst h y`,
  constant second point t via `fibreGlobal`, and orientation obtained by pulling back c.
  Its first/second/compatible fields are the recorded universal-product lift data. They
  give p_(f,1) φ_z = i and the prescribed pointwise description x ↦ (x,t,c).
- `fibreSquare_existsUnique` specifies h̄ φ_z ≅ z Γ by both projection equations. Its
  chosen isomorphism determines `fibreExchange`: `ordinaryExchange` of the inverse-image
  mate of this exact square. The first conjunct of the theorem makes each component
  invertible for bounded-below A. Since fibreExchange is a natural transformation on
  the derived categories, these isomorphisms are natural on D⁺.
- The second half of that first conjunct states the actual adjunction equation:
  the inverse homEquiv image of fibreExchange.app A is `fibreCounit h g y t c hc Λ A`.
  The latter is the canonical derived-square identification followed by φ_z* of the
  direct-image counit of h̄. This is the requested counit compatibility, not Nonempty
  of an unspecified isomorphism.
- For every `(T : Scheme.{u}) (q : T ⟶ S)`, the scheme X_T is `pullback (h ≫ g) q` and
  Y_T is `pullback g q`. `baseArrow` is their canonical induced h_T. The theorem
  `baseArrow_structure` identifies its composite with g_T with the chosen f_T second
  projection. `baseSourceLift` and `baseTargetLift` are exactly the induced universal
  lifts v_f and v_g of `squareLift` from the dependency.
- `baseSquare_existsUnique` fixes their commutation with h̄, h̄_T by both projection
  equations; `baseExchange` is its ordinary derived counit mate. The theorem's second
  conjunct says its component is an isomorphism for all q and bounded-below A. There is
  no condition on T, q, or any Tor dimension.
- `firstModules` is the actual first projection p₁. `firstExchange` is the ordinary mate
  of `(properLift h g).first`. The theorem's third conjunct makes its component an
  isomorphism for every bounded-below B on X_et, exactly the specified first-projection
  comparison p_(g,1)* Rh_* B → Rh̄_* p_(f,1)* B.
- No Noetherian, finite-dimensional, constructibility, finite-Tor, or invertibility-on-S
  assumption is present. In particular characteristic dividing m is included.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Sheaf.Paper.OrientedNearbyCycles`: `EtaleSite`, `etaleTopology`, `etaleBaseChange`,
  `etaleMorphism`, `VanishingTopos`, `p₁`, `p₂`, `orientation`, `Lift`, `lift`, `squareLift`,
  `squareModules`, `moduleMorphism`, `etaleDatum`, `vanishingDatum`, `Coeff`,
  `EtaleDerived`, `VanishingDerived`, and `etaleComposition`.
- `Sheaf.CategoryTheory.Sites.OrientedProductLargeSites`: the recorded
  `CategoryTheory.OrientedProduct.universalWithLargeSites`; its public universal-property
  API is used through the dependency's projection-normalized `lift` construction.
- `Sheaf.AlgebraicGeometry.StrictHenselization`: `Scheme.strictHenselizationScheme`, from
  the recorded small pointed-affine coordinate-ring colimit. The canonical structural
  map and point evaluation come from `StrictHenselizationCanonicalMap` and its imports.
- The geometric points are the recorded inline `[Field Ω] [IsAlgClosed Ω]` and Spec maps.
  Fibre products are `CategoryTheory.Limits.pullback`, `fst`, `snd`, and `lift`.
- `Sheaf.Paper.OrientedProductPointsConservative`: `punctualSite`, `punctualEquivalence`,
  `etaleSheafEquivalence`, `geometricEtalePoint`. This already landed node, also a proof
  dependency, is added to stmt_deps because its canonical point constructors are used.
- `Sheaf.Paper.CompletionMateComparison`, imported through nearby cycles:
  `CategoryTheory.AdicSites.Morphism.pull`, `push`, `adj`, `derivedSquare`, and
  `ordinaryExchange`. These retain the insertion-normalized constant-module square and
  use the same K-injective derived adjunctions as the dependency.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`:
  `Scheme.pointSmallEtaleComapIso`; Mathlib `Point.sheafFiberComapIso` and
  `Point.sheafFiberIso`. These are canonical comparison data, not new copies of stalks.

Edge cases checked mathematically: h = identity (all maps reduce to the usual restriction
and identity mates); empty X (the geometric fibre and its sections are zero); Λ the zero
ring and m = 1; arbitrary characteristic including characteristic dividing m; a field Ω
larger than the strict-local residue field (no closed-immersion hypothesis on X_y); a
nonidentity specialization c; T empty or T → S nonflat; and independent u,v. Definitions
of φ_z and all comparison maps do not use properness or torsion: those occur only in the
invertibility theorem, as they should.

Searches made with msearch.py: LeanFinder, “Proper direct image on vanishing topoi has
geometric stalk equal to derived cohomology of proper geometric fibre and commutes with
base change”, returned eight ordinary stalk/pushforward lemmas and no oriented derived
fibre theorem. Loogle, “IsProper, ordinaryExchange”, returned no hit (unknown identifier
IsProper in that query service). Mathlib grep, `vanishing.?topos|oriented.?product` under
AlgebraicGeometry, returned zero hits. Direct rg in WeilConjectures and lean/Sheaf for
properFibreExchange, this node id, and oriented/proper-fibre terminology found no existing
statement; the GeometricFibreExchangeGerms modules belong to the different
lem-sbc-geometric-fibre-exchange-germs node and were not reused as a false match. The
nearby-cycle, point, and mate APIs found by those searches were reused. Namespace and
primary-name searches in Mathlib, upstream, and the shared Sheaf library found no collision.

All postponed theorems are named, have source and proof docstrings, and belong to this
node's canonical-map construction or its seven proof steps. Definitions have actual data;
choices are only from the uniquely specified strict lift and the two projection-normalized
universal-property isomorphisms. Every theorem proof is `sorry`, as required at stage 2.
No new definition node or dependency replacement module was necessary.

## Second reading by Q12

No separate worker was started: the dispatcher instructs this worker to deliver directly,
and the maintainer performs the independent review. In a second pass with the node and
module open, Q12 checked the three arrows' directions against `ordinaryExchange`, corrected
the inverse-image square orientation for fibre/base exchange, and made the counit adjunct
equation explicit. The first-projection square needs the opposite inverse-image direction,
which is retained. The over-S condition on c, both projection normalizations on both
universal squares, the empty and zero-ring cases, and arbitrary T were checked. The
bounded-below predicate is Mathlib's plus predicate, with no upper bound. The reviewed
initiality step and exact-j!-adjunction argument were verified present both in the unchanged
node and the module's main proof docstring. Universe inference is handled through explicit
universe arguments and a transparent generic abbreviation for the existing plus predicate;
no universe equality is imposed.

## Validation

The prescribed scompile.py wrapper compiled the complete module in both its sandbox and
library locations with exit code 0 and no warnings. The first deliver2.py --no-push run
passed server preflight and per-file compilation (dry-run commit e22069fb7b). A comparison
against the shared reviewed node confirms that only lean and the added already landed
statement dependency differ. All lines are at most 100 characters; autoImplicit is false.
The final delivery reruns compilation and preflight after the documentation additions.
