## Worker report

The module `Sheaf.SecSmoothPurity.ProperScalarCounitSquare` states
`AlgebraicGeometry.ProEtale.properScalarCounitSquare`, with its whole proof `sorry`.
It reuses the existing natural transformation `directImageScalarComparison` for γ,
rather than constructing another mate. Three transparent specializations name exact
restriction, the existing normalized scalar adjunction, and D = d⁻¹.
One new existing:true definition node records the already published geometric
adjunction and its scalar mate. There are no dependency modules or statement corrections.

Hypotheses and objects, matched to the node:

- The finite commutative rings are `{A B : Type u} [CommRing A] [CommRing B]
  [Finite A] [Finite B]`. The unital map is `(φ : A →+* B)`.
- Schemes and the arbitrary morphism are `{Z Y : Scheme.{u}} (h : Z ⟶ Y)`.
  There is no properness or other geometric hypothesis.
- `T.proEtaleDerivedCategory R` is the ordinary unbounded derived category of
  modules over `proEtaleConstantRing T R` on `T.ProEt`, with its recorded standard
  derived localization. This is precisely the constant-ring presentation requested
  here and supplied by `def-weil-pbc-proetale-operations`; it is uncompleted.
  The intrinsic sheafified connected-component coefficient presentation of
  `def-weil-pbc-proetale-modules` is publicly imported, including its realization
  equivalence. No bounded-constructible subcategory or fixed-module alternate
  category is used. Site object universe u+1 and morphism universe u are retained.
- T_W is `directImageScalarExtension φ W`, the published universal derived
  extension along `proEtaleConstantRingMap φ`. The helper
  `directImageScalarRestriction φ W` is exact termwise `mapDerivedCategory` of
  `proEtaleRingRestrictScalars` along this same map. The helper
  `directImageScalarAdjunction` is exactly `proEtaleRingDerivedExtensionAdjunction`,
  with the already published representative/unit normalization.
- P_R is `proEtaleConstantRingDerivedPullback R h`, R_R is
  `directImageConstantPush R h`, and e^R is the counit of
  `directImageConstantAdjunction R h`. That adjunction is the existing
  `proEtaleRingDerivedAdjunction` specialized to the canonical constant sections.
- χ is `directImageScalarPullbackIso φ h`, the existing `proEtaleReductionPullbackIso`.
  Its inverse is defined by the scalar mate of the canonical restriction/pullback
  comparison, with the balanced K-flat tensor normalization. No arbitrary
  isomorphism or adjunction is a theorem parameter.
- d is `proEtaleRingRestrictionDerivedDirectImage` specialized to the four
  constant ring sheaves and their canonical comparisons. `directImageScalarRestrictionIso`
  is literally its `.symm`. Naturality of the constant-section comparison supplies
  the required coefficient square; this is constructed, not an extra hypothesis.

Conclusions, clause by clause (Lean writes composition from left to right):

1. The first `∀ N` equation is P_B(γ_N) ≫ e^B = χ ≫ T_Z(e^A), exactly the
   geometric transpose defining γ. The existing `directImageScalarComparison`
   is the mate of χ, so already has a real natural-transformation construction.
2. The second `∀ N N' v` equation spells out its naturality for every derived
   A-morphism v. It imposes no invertibility claim on γ.
3. For every `H : Z.proEtaleDerivedCategory B`, the first equation in the pair
   is χ⁻¹ ≫ P_B(ε_Y(R_B H)) ≫ e^B_H =
   T_Z(P_A(D_H⁻¹)) ≫ T_Z(e^A_(r_Z H)) ≫ ε_Z(H).
   This is exactly the specified composite-adjunction counit equation. Mathlib's
   `Adjunction.comp_counit_app` identifies the two composite counits.
4. The second equation in that pair is
   T_Y(D_H) ≫ ε_Y(R_B H) = γ_(r_Z H) ≫ R_B(ε_Z(H)), the scalar counit square.
   Its domain includes every restricted object r_Z H, without a Tor bound.
5. The final `∀ J [J.IsKInjective] I [I.IsKInjective] j [QuasiIso j]` clause
   states that the image h_*(j) is a quasi-isomorphism, and gives the normalization
   equation for this particular D. It writes out the K-injective direct-image
   computation isomorphisms, the exact restriction/localization factors and the
   termwise identity-on-sections comparison. Thus D is the inverse of the class
   of h_*(j), under exactly these canonical identifications. The equation has
   the same orientation and factors as `proEtaleDerivedDirectImage_restrictScalars`:
   the latter's sectionwise constant-module direct image is here expressed by
   the canonical identified-coefficient ringed direct image. Both use the same
   constant-section structural map; the underived comparison is explicitly the
   canonical `proEtaleRingRestrictionDirectImage`. This is the representative
   normalization supplied by the same κ of the ringed-topos composition node,
   not a new existential choice of D. No premise asserts that r_Z J is K-injective.
6. No properness, flatness, boundedness or finite Tor-amplitude assumption appears
   anywhere. These omissions are deliberate clauses of the informal statement.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `FiniteCoefficientModules`,
  `FiniteCoefficientDerivedCategory`, `finiteCoefficientRealization_isEquivalence_ring`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` and its public
  `ProEtaleOperationsCanonicalAdjunction`: `proEtaleConstantRingComparison`,
  `proEtaleConstantRingPullback`, `proEtaleConstantRingPushforward`,
  `proEtaleConstantRingDerivedPullback`, `proEtaleRingDerivedDirectImage`,
  `proEtaleRingDerivedAdjunction` and the ordinary module adjunction.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`:
  `SheafOfModules.sheafRingDerivedCoefficientAdjunction`; the normalized Hom,
  unit, adjunct and resolution-counit clauses are read, and the published selected
  scalar adjunction is reused through `FourCorners`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`:
  `proEtaleRingRestrictScalars`, its finite-limit/finite-colimit preservation,
  `proEtaleRingRestrictionDirectImage`, `proEtaleRingRestrictionDerivedPullback`,
  `proEtaleRingRestrictionDerivedDirectImage_existsUnique`,
  `proEtaleRingRestrictionDerivedDirectImage`, `proEtaleRingSheafChangeAdjunction`.
- The recorded module `Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage`
  was missing in the read checkout, so its live source was read with `scompile.py --source`.
  It publicly imports `Sheaf.AlgebraicGeometry.ProEtaleDirectImageRestrictionOfScalars`,
  which provides the relevant constant-ring declaration
  `proEtaleDerivedDirectImage_restrictScalars` and coefficient restriction functor.
  The fixed-module-sheaf `fixedScalarRestrictionDirectImage_kInjective` uses a
  different equivalent presentation; we use the original ring-sheaf declaration.
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`:
  `CategoryTheory.ringedToposDerivedPushforwardComposition`, including its unique κ,
  derived-unit normalization and K-injective-resolution formula.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`
  and its retained canonical representative interfaces, without collapsing universes.
- Added definition dependencies: `def-sp-proetale-constant-coefficient-ring-map`
  records `AlgebraicGeometry.Scheme.proEtaleConstantRingMap` in
  `Sheaf.Paper.StratumScalarExtension`; `def-sp-constant-scalar-pullback-comparison`
  records `directImageScalarExtension`, `directImageConstantPush` and
  `directImageScalarPullbackIso` in `Sheaf.SecSmoothPurity.DirectImageScalarOperations`.
  The new `def-sp-direct-image-scalar-adjunction-mate` owns the same module's
  `AlgebraicGeometry.ProEtale.directImageConstantAdjunction` and
  `AlgebraicGeometry.ProEtale.directImageScalarComparison`.
  `def-weil-pbc-four-corners` is retained for `proEtaleRingDerivedExtensionAdjunction`
  and `proEtaleReductionPullbackIso`. Neither the scalar-exchange theorem nor the
  stratum-scalar-extension theorem is a statement dependency for these plain definitions.
- Available proof dependencies are imported plainly: the independent-coefficient
  K-flat-resolution module, `KFlatRingedToposPullback`, and `ProEtaleConstantRingMap`.
  Sheaf tensor/change-of-rings and `Adjunction.comp` are available through the
  public dependency modules; their full definitions/signatures were read.

Edge cases checked before writing: h need not be proper; h=id and φ=id retain
all comparison factors and specialize to the original counits. The empty scheme
is allowed, with its unique module maps. Zero coefficient rings are allowed by
`CommRing` (no `Nontrivial` assumption). A nonflat quotient such as Z/4 → Z/2 is
allowed. Arbitrarily unbounded H and r_Z H, including r_Z H of infinite Tor
amplitude, remain in the domain. The resolution clause assumes K-injectivity of
J and of its chosen replacement I separately, not of the restricted J.
All variables and the universe are explicitly bound; there are no local notations,
private copies, chosen arbitrary functors, or data definitions containing sorry.

Searches made (2026-10-24):

- msearch LeanFinder: `proper direct image scalar counit square`: eight generic
  ordinary pushforward/restriction/counit hits, none stating this normalized
  unbounded comparison theorem.
- msearch LeanSearch: `Derived direct image restriction of scalars comparison scalar
  counit compatibility`: ordinary module extension/restriction counit and presheaf
  restriction results, not this theorem.
- msearch Loogle: `Adjunction counit natural transformation derived direct image
  restriction scalar` returned no hits (unqualified identifier not recognized).
  Refined `CategoryTheory.mateEquiv_counit` found the expected generic mate-counit
  equation. It supplies the first clause categorically but neither the specified
  coefficient counit square nor its resolution identification.
- msearch grep in Mathlib CategoryTheory: `mateEquiv.*counit|counit.*mateEquiv`:
  generic `mateEquiv_counit` and its inverse version. Read Mates.lean 123–132.
- msearch grep in Mathlib Algebra/Category/ModuleCat:
  `restrictScalars.*counit|counit.*restrictScalars`: seven ordinary module hits,
  no full derived pro-etale statement.
- rg of project `lean/WeilConjectures` for the node id, `ScalarCounit` and
  `scalarCounit`: no matching normalized pro-etale theorem.
- rg of `lean/Sheaf` for `proper.*scalar|scalar.*counit|ProperScalar|CounitSquare|counitSquare`
  and scalar/direct-image names located `DirectImageScalarOperations`, `FourCorners`
  and the recorded ring-sheaf change module. These provide the constructions reused
  here; no declaration states all the item's clauses. The initial broad rg included
  a nonexistent root-level WeilConjectures path and was repeated on `lean/WeilConjectures`.
- Read the current blueprint det-sp-tower-gluing Levels paragraph and Stacks
  sites-cohomology.tex lemma-adjoint and lemma-derived-pushforward-composition.

Validation: server compilation and the delivery preflight are run through the
prescribed wrappers. The only postponed proof is `properScalarCounitSquare`.
No `STATEMENT-DISPUTED` or source-statement fault was found.

## Second reading by Q115

No independent worker was started, as the dispatcher explicitly forbids delegation.
The maintainer's independent review reads this direct delivery. An additional rereading by the same author checked the order of χ versus χ⁻¹, D versus d, the domain of every
counit, and the direction of the final resolution equation against the node.

## New nodes

`def-sp-direct-image-scalar-adjunction-mate` is an existing:true ownership node for
`AlgebraicGeometry.ProEtale.directImageConstantAdjunction` and
`AlgebraicGeometry.ProEtale.directImageScalarComparison`, both already defined in
`Sheaf.SecSmoothPurity.DirectImageScalarOperations`. No new Lean module is needed.
The first definition specializes the canonical ringed derived adjunction to the
actual constant rings and canonical coefficient comparison. The second is literally
`mateEquiv` of the two such adjunctions and `directImageScalarPullbackIso.hom`.
Its displayed unit/comparison/counit composite is precisely that mate, with arbitrary
commutative rings and arbitrary scheme morphism, and makes no isomorphism assertion.
The scalar/pullback constructors and constant-ring map have their existing definition
owners, cited explicitly. The generic mate is Mathlib `CategoryTheory.mateEquiv`,
recorded by `def-weil-pbc-adjunction-mate` (status mathlib).

The new node records the repair searches: LeanSearch and LeanFinder each returned
8 generic sheaf-module/adjunction hits; Loogle returned unknown identifier and
0 hits; msearch grep returned 0 Mathlib hits. Project grep found no WeilConjectures
occurrence and the two exact definitions at DirectImageScalarOperations lines 52
and 84. DAG exact-name search and a scan of all definition-node lean records found
no definition owner. `blueprint_refs.py search 'direct-image scalar'` returned
0 nodes; its ancestor command returned `det-sp-tower-gluing`. Hence the new node
binds existing data without copying a definition. Sources reread: Stacks
`lemma-adjoint`, `remark-base-change`, and the current blueprint gluing proof's
Levels paragraph. Edge cases are the identity morphism, identity coefficient map,
empty scheme, zero ring, nonflat scalar map and unbounded complexes, all retained.

## Repair of returned delivery

H2 of immutable head `9538609d1e34` is repaired: remove the two added theorem
statement dependencies `lem-fix-direct-image-scalar-exchange` and
`lem-sp-stratum-scalar-extension`; cite the two already landed definition owners
and the new definition ownership node above; retain `def-weil-pbc-four-corners`.
The Lean file is unchanged, as permitted by the independent review, which checked
its mathematics and all displayed directions. Compared with current main, only
the item's lean and stmt_deps fields change, plus the new node and this report.

For the advisories, the second reading remains an explicit same-author rereading
under the no-delegation dispatcher policy. Proof-only imports remain plain imports.
The Prop proof `proEtaleConstantInverseImageMap_naturality`, owned by
`lem-weil-pbc-profinite-coefficient-inverse-image`, supplies D's coefficient square;
it adds no coefficient compatibility premise or chosen data.
The repair rereading matched finite A and B and arbitrary h, each transpose,
naturality, both counit equations and the final K-injective clause to the unchanged
Lean signature. It reconfirmed that r_Z J is not assumed K-injective and that D is
the inverse class of h_*(j), with all localization factors retained. No mathematical
change or disputed statement was found.
