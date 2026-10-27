## Worker report

The delivery states `WeilConjectures.SfWeilChosenDuality.chosen_duality_hom` in
`Sheaf.SixFunctors.WeilChosenDualityHom`. Its only postponed proof is this named theorem,
whose docstring contains the four steps of the node's proof. All other declarations
are actual compositions, abbreviations or predicates packaging this assertion. There
are no new nodes, dependency repairs, or changes to the mathematical statement.

Read the item, all four statement dependencies and their recorded Lean declarations,
the two additional proof-dependency interfaces, the stage-2 brief, the stage document,
delivery-errors H, and the compact-object example (the old Sheaf example is withdrawn,
so its recorded upstream `WeilConjectures.CategoryTheory.CompactObject` was also read).
Read the current blueprint equivariance proof paragraphs 1--2, the ancestor's local
boundary duality proof Step 2, and the current general-biduality unit statement.
There is no released repair note for this item in the read repository.

### Hypotheses and objects

* The finite base field, its characteristic, and its chosen algebraic closure are
  `D : FiniteFieldDatum.{u}`. The record supplies the prime p, positive exponent,
  finite field of cardinality p^a, and `IsAlgClosure D.k₀ D.k`; it does not replace
  the finite field by an arbitrary characteristic-p field.
* The prime distinct from the characteristic is `(l : ℕ) [Fact l.Prime]
  (hl : l ≠ D.p)`. The geometric prime-invertibility proof comes from the recorded
  `sfWeilPrimeInvertible`; it is not a new hypothesis.
* The coefficient field is `(Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]`. Its universe v is independent of the scheme universe u.
* The separated finite-type base scheme is `T₀ : Over (Spec (.of D.k₀))` with
  `[LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom]`.
  The geometric scheme is exactly `(D.geometricFiber T₀).left`.
* `Carrier D l Ω T₀` abbreviates the recorded
  `generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber T₀).left`.
  Thus the coefficient category is the literal common-stage pair category, without
  a Karoubi completion or a replacement by a category of abstract coefficients.
* `Pairs D l hl Ω T₀` abbreviates `sfCommonStageWeilComplex D l hl T₀ Ω`.
  Its endofunctor is the recorded geometric-Frobenius `commonStageDerivedPullback`.
  Its objects are `IsoAlgebra` fixed pairs and its arrows are commuting underlying
  derived arrows, not Ext groups in the derived category of Weil sheaves. Every
  category and Hom in the conclusion uses these pair categories.
* The structure morphism is `CoefVerdierWeil.structureModel D T₀`; the target is
  `CoefVerdierWeil.pointModel D`. For every compactification c₀ of this structure map,
  A is the existing coefficient exceptional system and Z is its recorded canonical
  Frobenius/mate lift. This exposes the construction parameter of the dependency;
  there is no compactifiability assumption or properness restriction added to T₀.
* `structureLeft` is `IsoAlgebra.mapOfNatIso Z.common.left` and `structureRight` is
  `IsoAlgebra.mapOfNatIso Z.common.right`. These are precisely the lifted compact
  support and its canonical exceptional right adjoint. `FrobeniusAdjunctions` includes
  the finite/common-stage normalization to the canonical Frobenius exchange, so Z
  cannot replace compact support by an arbitrary commuting functor.
* `adjCan` is an adjunction between these lifted functors. The next two clauses
  identify its unit and counit, after forgetting Frobenius, with those of the actual
  `A.adjunction`, rather than choosing an unrelated adjunction on the same functors.
* `unit` is a pair at the finite-field point satisfying `IsCoefficientUnit`. This
  says its carrier is the dependency's `commonUnit`, with theta satisfying exactly
  the tensor-unit normalization from `DualizingMate`. The Frobenius structure on
  the coefficient object is therefore canonical, rather than an arbitrary scalar.
* B, IH and W are the dependency's geometric Verdier duality, its identification
  with actual internal Hom, and its Weil equivariance package. The main theorem
  supplies these as conclusions, together with `DualizingNormalization`; they are
  not additional assumptions the caller must supply. The geometric dualizing pair
  is `geometricOmega B W`, identified by the Weil isomorphism iω with
  `structureRight.obj unit`.
* The canonical dual in the item is the functor C. `IsHomLift` fixes its carrier
  on every K to actual `CoefQbarVerdier.homDual` into `structureRight.obj unit`, and
  fixes its arrow map to that Hom functor's arrow map. `CanonicalHomComparison`
  identifies C with the existing geometric dual by H(identity,iω inverse), followed
  by `IH.comparison.inv`. Since it is an isomorphism in pair functor categories,
  this also pins C's standard Weil structure. The generic `pairDual` constructor
  uses `IsoAlgebra.opFunctor` and `IsoAlgebra.mapOfNatIso`, so the first Hom variable
  carries the inverse Frobenius structure as required.
* The chosen adjoint is universally quantified as J between the specified pair
  categories, together with **every** `adj : structureLeft ⊣ J`. There is no
  assumption that J equals the canonical right adjoint, and no assumption of
  fully faithfulness, biduality, or preservation by the chosen dual.

### Each clause of the conclusion

`ChosenConclusion` expands as follows.

1. The chosen dualizing pair is literally `J.obj unit`, and the canonical one is
   literally `structureRight.obj unit`. The normalization n is an isomorphism
   between these two **pairs**, with equality
   `n = (adj.rightAdjointUniq adjCan).app unit`. The whole natural right-adjoint
   isomorphism is the recorded Mathlib construction; its counit equation is
   `Adjunction.rightAdjointUniq_hom_app_counit`. Thus the normalization includes
   the adjunction, not just the two underlying functors.
2. The existential `permitted` establishes that internal Hom into `J.obj unit`
   lies in the recorded constructible Hom domain for every underlying K. V is a
   contravariant functor on pairs. `IsHomLift` fixes its objects to the existing
   `homDual` functor into this literal chosen dualizing object and its maps to
   that functor applied to `f.hom.f.op`. This states preservation and the specified
   arrow action, not only the existence of some anti-equivalence.
3. The natural Weil isomorphism `c : V ≅ C` has components whose underlying arrow
   is exactly `commonStageDerivedInternalHom.map (identity,n)`. The equalities in
   `IsHomLift` identify the endpoints; HEq merely avoids inserting transports
   into the displayed arrow. The comparison is not an arbitrary isomorphism of
   the two functors. Its equivariance fixes the chosen Hom's standard Weil lift
   from the already normalized canonical one. There are no independent auxiliary
   Frobenius actions on V.
4. `V.IsEquivalence` means that this same functor from the opposite pair category
   is an equivalence, i.e. the stated anti-equivalence.
5. `Nonempty (𝟭 (Pairs ...) ≅ V.rightOp ⋙ V)` is natural Weil biduality from K to
   V(V(K)). Naturality and invertibility are those of a natural isomorphism;
   equivariance follows from its components being morphisms in the pair category.
6. `∀ K M, Function.Bijective (fun f : K ⟶ M ↦ V.map f.op)` is exactly the required
   Hom bijection, with specified forward map u ↦ D(u). The target type is inferred
   as `V.obj (op M) ⟶ V.obj (op K)`.
7. The final equation for a₁ : K' → K and b₁ : M → M' states
   `V.map (a₁ ≫ f ≫ b₁).op = V.map b₁.op ≫ V.map f.op ≫ V.map a₁.op`.
   This is the two-variable naturality of these very Hom bijections.

The helper predicates and functors belong to the owning node's normalization and
conclusion. They introduce no independent operation, copy no coefficient category
or internal Hom construction, and every one is listed in `lean.declarations`.
The only local `letI` terms occur inside helper-definition bodies and supply inherited
geometric-fibre properties. There is no file-local notation, instance, or private API,
and no `let` binder in the theorem signature.

### Dependencies used

* `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `WeilConjectures.generalAlgebraicallyClosedConstructibleCategory`.
* `Sheaf.Paper.DerivedPullbackTensorHom`:
  `WeilConjectures.commonStageHomPairs`, `commonStageDerivedInternalHom`,
  and `commonStageDerivedTensor`. The published full-subcategory and common-stage
  representative action are used; no arbitrary bifunctor replaces internal Hom.
* `Sheaf.Paper.SfWeilSheafComplex`:
  `sfCommonStageWeilComplex`, `sfCommonStageWeilFrobeniusPullback`,
  and `sfWeilPrimeInvertible`.
* `Sheaf.SixFunctors.CoefVerdierWeilEquivariance`:
  `CoefVerdierWeil.FiberDuality`, `FiberInternalHom`, `Coefficients`,
  `DualizingNormalization`, `FiberExceptional`, `FrobeniusAdjunctions`,
  `structureModel`, `pointModel`, `commonUnit`, `commonMu`, `commonUnitor`,
  and the inherited fibre-property interfaces. The main proof input is
  `WeilConjectures.coef_verdier_weil_equivariance`.
* `Sheaf.SixFunctors.CoefQbarVerdier` (publicly exposed by the previous dependency):
  `WeilConjectures.CoefQbarVerdier.homDual` and the permitted-pair/internal-Hom
  identification carried by `FiberInternalHom`.
* `WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra` (publicly exposed
  by the pair-category dependency): `IsoAlgebra.opFunctor`, `mapOfNatIso`, `mk`,
  and the actual forgetful/carrier/arrow operations.
* `Mathlib.CategoryTheory.Adjunction.Unique`:
  `CategoryTheory.Adjunction.rightAdjointUniq`, the declaration recorded by
  `det-sp-unique-right-adjoint`, and its exact counit-normalization equation.
* `WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius` is a plain proof import
  for `lem-fix-weil-operations`, whose current recorded declaration is
  `AlgebraicGeometry.Etale.isWeilPairing_mixedSupportCupProduct`. That attachment
  only covers the cup-product clause; it is not used as a supposed complete
  internal-Hom interface. The needed actual dual Frobenius comparison already
  resides in the base statement dependency's `Coefficients.common` and the
  existing fixed-pair op/map constructors. The standard-lift computation in
  this item's proof is elementary and written out in its docstring.

### Edge cases checked before writing

* At the point with the canonical adjunction, n is the component of
  `rightAdjointUniq adjCan adjCan`; the dual Hom maps and biduality reduce to the
  usual ones. No arbitrary scalar comparison is substituted.
* At the point with the same right functor and a rescaled unit/counit, adj is
  still quantified independently. The right-adjoint comparison, hence n and
  H(identity,n), changes accordingly. The statement never asserts n = identity.
* The empty scheme and zero objects are allowed: there are no nonempty,
  nonzero-support, smoothness, properness, or dimension hypotheses.
* Morphisms of Weil pairs are their actual commuting derived arrows, including
  nonsemisimple Frobenius actions and rational Frobenius data with no stable
  integral lattice. No finite-stage lattice for theta is assumed.
* The coefficient closure and scheme universes remain independent. Inherited
  separatedness and prime invertibility are supplied from the dependency's
  actual base-change lemmas, not assumed with a new universe equality.
* The first variable is opposite: `opFunctor` uses theta inverse. In the displayed
  naturality equation, applying V reverses the order of a₁, f and b₁ as required.
* Identity choices and arbitrary chosen adjunctions are included. The canonical
  compactification parameter ranges over all compactifications of the fixed
  structure morphism; it does not restrict the scheme to one chart or one map.

### Searches for an existing statement

All searches used the prescribed `msearch.py Q39 lem-sf-weil-chosen-duality-hom`
wrapper, or read-only rg in the named source directories.

* LeanFinder query: `Verdier duality on Weil fixed pairs for a chosen structure
  right adjoint with natural Hom bijections`. Eight unrelated hits: condensed
  constant/free functor adjunctions and a general categorical bijection. No
  chosen structure-adjoint Weil duality statement.
* Loogle query: `CategoryTheory.Adjunction.rightAdjointUniq,
  CategoryTheory.Functor.FullyFaithful`. Zero hits. The explicit known
  `rightAdjointUniq` source was then read and used for its separate normalization
  clause, not mistaken for this complete geometric theorem.
* Mathlib grep query: `chosenDuality|verdier.*hom|Weil.*duality` in
  `CategoryTheory`. Zero hits.
* LeanSearch query: `Weil fixed pairs chosen Verdier duality right adjoint Hom
  bijection`. Eight generic adjunction/partial-adjoint/dual-order hits, none
  stating the assertion.
* rg queries `chosen.*[Dd]ual|[Dd]uality.*[Hh]om|lem-sf-weil-chosen-duality-hom`
  and `sfWeilChosenDuality|ChosenDualityHom|chosen-duality-hom` in the named
  `lean/WeilConjectures` and `lean/Sheaf` trees, plus the upstream-name index.
  The first query found existing geometric/coherent duality files, which do not
  state the chosen-adjoint theorem on these fixed pairs; the exact-name query
  found no existing declaration. The upstream WeilSheaf VerdierDual interface
  uses different sheaf/derived-of-Weil objects, so it is not this assertion.

No STATEMENT-DISPUTED flag or correction is needed. Validation uses only the
prescribed server scompile.py and deliver2.py wrappers; no global build or direct
Git command is run in the read-only repository.

## Second reading by Q39

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
