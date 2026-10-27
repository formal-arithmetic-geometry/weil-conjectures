## Worker report

Q99 states `lem-sf-native-weil-open-proper-forgetting` in
`Sheaf.WeilSheaf.NativeOpenProperForgetting`. This is a statement-only delivery:
each theorem has exactly `by sorry`; every comparison and helper definition has
real data. The declarations listed in the node's `lean.declarations` jointly
render the several clauses of this large node. There is no statement correction, dependency replacement, or disputed statement.
The repair adds two definition ownership nodes for existing constructions; no
Lean definition is copied or duplicated.

### Objects and hypotheses

The native framework fixes `AlgebraicClosure k₀` as the model of the algebraic
closure and `PadicAlgCl l` as the model of Omega. The global binders are
`(k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]` and, for native
geometric constructions, `[Fact (ringChar k₀ ≠ l)]`. This inequality is equivalent
to the node's `l ≠ char(k₀)` and is the convention required by the existing
framework. No algebraic closure or coefficient object is chosen from a new
existence axiom. `Scheme.Hom.geometricFiber`, `geometricGaloisFrobenius`, and
`Scheme.Hom.geometricFiberMap` are exactly the native framework's objects.

`[T.Over (Spec (CommRingCat.of k₀))]` supplies the structural morphism.
Separated finite type is rendered by `IsSeparated`, `LocallyOfFiniteType`, and
`QuasiCompact` of that morphism. The same three hypotheses for `f`, `X`, and `Y`
appear explicitly in `open_proper`; `[f.IsOver ...]` says the map is over k₀.
The explicit `(c : Compactification f)` is the chosen native compactification,
not an arbitrary factorization with extra unrecorded properties. Its middle
scheme has the canonical over-structure `c.over`; this is introduced inside
constructions with `letI`, not as a competing global instance. The more general
helper assertions about a coefficient sheaf or an open immersion require only
the data used there; the node is their stated separated finite-type case.

`ProEtale.AdicSheaf l T` is the actual native coefficient heart. It is not
replaced by an ad hoc category. `ProEtaleWeilSheaf k₀ l T` is exactly
`IsoAlgebra (WeilSheaf.frobeniusPullback k₀ l T)`, and `IsoAlgebra.forget` is U.
`DerivedCategory` throughout is the ordinary localization of complexes of these
abelian hearts. `WeilComplex.objectProperty` gives the existing bounded
constructible full subcategory, including its full derived-category morphisms;
there is no use of fixed pairs formed only after deriving.

### Every clause and its Lean rendering

- The ring of locally finite-dimensional-span functions equals the sheaf of
  locally finite-extension-valued continuous functions: `coefficient_sections`
  quantifies every scheme, pro-etale object, continuous function, and point;
  `s ∈ PadicAlgCl.locallyFiniteFunctions ...` is equivalent to a neighbourhood
  and `PadicAlgCl.FiniteIntermediateField` containing every value there.
- The canonical identification is multiplicative and unital:
  `coefficient_modules` asserts `IsMonHom` for the existing normalized
  `nativeModuleCoefficientIso`. Its `nativeToOrdinaryModules.IsEquivalence`
  identifies internal module objects with the sectionwise module category. The
  displayed equality after `SheafOfModules.toSheaf` identifies the underlying
  sheaf, retaining the existing sectionwise actions, rather than selecting an
  unrelated equivalence.
- All restrictions and all finite coefficient-field inclusions are retained:
  `coefficient_naturality` gives the actual pushforward coefficient square for
  every scheme map, followed by the section formula for every finite
  intermediate field, pro-etale object, section, and point. Restriction inside
  a site is built into the sheaf morphism. These are the exact normalized legs
  of `locallyFiniteCoefficientRing_realization`.
- A and B are Grothendieck abelian: the first two conjuncts of `hearts` are
  `IsGrothendieckAbelian.{u + 1}` for the actual native module and pair hearts.
  Their abelian structures are the existing instances.
- P is an exact equivalence: `hearts` gives `IsEquivalence` and preservation of
  finite limits and colimits. `frobenius_reindexing` identifies P with the
  functor of `adicLowerStarEquivalence` for geometric Frobenius inverse and
  gives exactness of that equivalence's inverse. This is coefficient-preserving
  reindexing: the equivalence is the one constructed from native coefficient
  maps, not a bare categorical witness.
- U is exact and conservative: `hearts` gives its preservation of finite
  limits/colimits and `ReflectsIsomorphisms`.
- The free-action adjoint is the actual `IsoAlgebra.Free.functor P`:
  `hearts` gives its adjunction to U, exactness, and its carrier as the coproduct
  of `IsoAlgebra.Free.obj P M`, the framework's integer-power family. Hence this
  is the specified integer-indexed free action, not an unspecified left adjoint.
- U preserves K-injectives: `hearts` includes `PreservesKInjectiveComplexes`.
- D(U) is conservative, commutes with cohomology and shifts, and preserves cone
  triangles: the next conjuncts give `ReflectsIsomorphisms`, `CommShift ℤ`,
  `IsTriangulated`, and a natural homology-functor isomorphism for every integer.
  `Nonempty` encloses the data-valued structures/isomorphisms, not a weakened
  objectwise equality. The functor itself is fixed to `U.mapDerivedCategory`.
- Boundedness is detected after forgetting: `hearts` quantifies every native
  derived K and asserts the iff of `DerivedCategory.TStructure.t.bounded`.
- The stated constructibility is detected after forgetting: its final iff is
  `WeilComplex.objectProperty ... K` iff forgotten K is bounded and every
  cohomology sheaf satisfies `IsAdicStratifiedLisseSheaf`. That existing notion
  requires a finite global locally closed constructible partition and pro-etale
  locally finite-free restrictions. Thus the condition is not merely local
  constructibility on an unspecified cover.
- Open extension is exact on the ordinary and native hearts: `open_exact`
  explicitly gives finite limits and colimits for both existing functors. Its
  final functor equality is `j!W ⋙ U = U ⋙ j!`, including arrows. The actual
  derived `openComparison` is constructed from that fixed-pair sheaf comparison
  and the exact-functor composition isomorphisms.
- The proper lift is the actual `ProEtaleWeilSheaf.lowerStar`, defined upstream
  by `IsoAlgebra.mapOfNatIso` for
  `adicLowerStarGeometricFiberMapCompFrobeniusIso`. Its structure is a followed
  by the direct image of theta. `ordinaryFrobeniusChain` writes those exact
  components `a.hom.app (I.X n).carrier ≫ p_*.map (I.X n).str.hom`, with the
  inherited chain-map commutativity certificate. It is a concrete construction.
- The proper comparison `properComparison` is the existing
  `rightDerivedFunctorMapOfNatIsoCompForgetIso`, not a chosen arbitrary iso.
  `properLeftUnit` and `properRightUnit` are the existing exact-square unit maps,
  specialized to the literal sheaf-functor equality `rfl`.
  `proper_normalization` states their equality after the comparison, for every
  complex, and their invertibility on every native K-injective complex. This
  is precisely the identity identification on the common `Q(p_* UI)`.
- On that representative both Frobenius maps agree: `proper_frobenius` equates
  `DerivedCategory.Q.map` of the actual native structure chain map with
  `DerivedCategory.Q.map (ordinaryFrobeniusChain p I)`. The latter's component
  formula is explicit in its definition; no arbitrary Frobenius arrow is used.
- The ordered open/proper c⁰: `comparison` precomposes the canonical proper
  comparison with exact native open extension and then `openComparison`.
  `ordinaryCompactSupport` is literally geometric `j!` followed by derived
  geometric `p_*`. `compactificationComparison` relates the actual native
  `rightDerivedLowerShriek ... f c` to that ordered ordinary construction, using
  only the associator and `comparison` for `c.i`, `c.g`.
- Compatibility with shifts and every localized derived morphism:
  `open_proper` asserts `compactificationComparison.hom.CommShift ℤ` and its
  naturality equation for every `K L : DerivedCategory (ProEtaleWeilSheaf ...)`
  and every derived `v : K ⟶ L`. It is not restricted to maps from sheaves or
  to maps known in advance to be chain maps. Frobenius compatibility is a separate explicit conjunct for every K: applying
  D(P_Y) to c⁰_K and then the ordinary action equals the native action followed
  by c⁰_K. `nativeCompactSupportFrobenius` is the localized actual `strNatIso`
  at the native output. `ordinaryCompactSupportFrobenius` uses independently
  derived `ordinaryProperFrobenius`, `ordinaryOpenFrobenius`, and F^c of the
  input's `nativeDerivedStructure`. None of the ordinary-action definitions
  references `compactificationComparison`, `properComparison`, or the native
  output action. This is the substantive square missing in the first delivery. The constructions use no
  exceptional adjoint or six-functor package as an assumption.

### Dependency declarations read and used

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and its
  `geometricFiber`; `Sheaf.AlgebraicGeometry.FrobeniusDetailed`:
  `WeilConjectures.FiniteFieldDatum.geometricFrobenius`. These supply the
  geometric interpretation; the actual functors use the fixed native model.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the sectionwise module category used by `NativeOrdinaryModules`.
- `WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra`:
  `IsoAlgebra`, `IsoAlgebra.forget`, `Free.functor`, `Free.obj`, `mapOfNatIso`,
  and `mapOfNatIso_obj_str`.
- Mathlib `Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; Mathlib's Grothendieck-category interface:
  `CategoryTheory.IsGrothendieckAbelian`.
- `WeilConjectures.WeilSheaf.LowerShriek`, and its public imports Category,
  OpenImmersion and LowerStar: `WeilSheaf.frobeniusPullback`,
  `ProEtaleWeilSheaf`, `WeilComplex.objectProperty`, native `extensionByZero`,
  `lowerStar`, `rightDerivedLowerShriek`, and `Compactification.over`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`:
  `Scheme.sfIntrinsicCompactSupport` supplies the dependency's compactification
  convention. Its torsion-coefficient construction is not substituted for the
  Omega-valued functor; the native framework's ordered construction is used.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  the unit-normalized universal meaning of right derivation; the actual native
  `Functor.rightDerivedFunctor` and `rightDerivedFunctorUnit` are its concrete
  framework instances used here.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicAlgClCondensedRing`, `padicAlgClRingObj`, and the finite-field
  legs; `Sheaf.Paper.CompletedCondensedCoefficients`: completed integral,
  rational and algebraic-closure coefficient constructions.
- `Sheaf.Paper.LocallyFiniteCoefficientRingRealization`:
  `AlgebraicGeometry.ProEtale.locallyFiniteCoefficientRing_realization`,
  including its monoid-map, section-leg, and morphism-naturality clauses.
- Definition ownership node `def-sf-native-sectionwise-module-presentation`,
  `Sheaf.Paper.NativeModuleConstructibilityComparison`:
  `nativeModuleCoefficientIso`, `nativeToOrdinaryModules`, and their existing
  sectionwise module presentation. This avoids duplicate module definitions.
- Definition ownership node `def-sf-exact-square-derived-unit-arrows`,
  `Sheaf.CategoryTheory.KInjectiveExactSquareComparison`:
  `KInjectiveExactSquare.leftUnit`, `rightUnit`, and the normalization interface.
  These ownership nodes cite the definitions from which their constructions are
  made, not the theorem nodes that previously happened to contain the helpers.
- `Sheaf.CategoryTheory.FixedPairDerivedForgetComparison`:
  `fixedPair_forget_properties`, `exists_fixedPairDerivedForgetComparison`;
  native `RightDerivedFunctor.IsoAlgebra`:
  `rightDerivedFunctorMapOfNatIsoCompForgetIso`. Exact derived localization and
  its composition isomorphisms are the existing `mapDerivedCategory` API.
- Proof imports retain the cited Grothendieck ringed-site, K-injective,
  pro-etale localization, exact localized-module, module-adjunction, and
  compactification-middle results. The unresolved DAG Frobenius-resolutions
  theorem is not assumed as extra data or copied into an untracked sorry.

### Edge cases and searches

Checked the empty scheme/site object: coefficient sections and the finite-span
condition are vacuous; a finite intermediate field still exists. The zero module,
rank-zero lisse sheaf, empty stratification of the empty scheme, and zero complex
are permitted by the existing notions. Every cohomological degree and shift is
an integer; no nonnegative or bounded-below condition is imposed on the ambient
derived category. Identity open/proper maps and their compactifications are not
excluded. No new equality of site, coefficient, and localization universes is
assumed: the native small site has object universe u+1 and the existing coefficient
heart has morphisms u+1 and objects u+2. The explicit small coproduct instances in
`properComparison` shrink the existing Grothendieck colimits, without mathematical
hypotheses or new category instances. The characteristic condition excludes only
the prime required by the node. Naturality quantifies all derived arrows, including
arbitrary roofs represented after localization.

Searches actually run with the prescribed `msearch.py` wrapper:

- LeanFinder: “Forgetting Frobenius on native sheaf derived categories commutes
  with open extension by zero and derived proper pushforward normalized on
  K injective complexes”. It returned general sheaf pushforward composition
  comparisons (including `SheafOfModules.pushforwardComp`), no exact aggregate
  statement of this node.
- Loogle: `CategoryTheory.Endofunctor.IsoAlgebra.forget,
  CategoryTheory.Functor.mapDerivedCategory`. No match; the indexed Mathlib did
  not know the upstream `IsoAlgebra.forget` identifier.
- Mathlib grep: `rightDerivedFunctorMapOfNatIsoCompForgetIso|mapOfNatIsoCompForgetIso`
  under `CategoryTheory`: no Mathlib match.
- Repository `rg` searches for these names, coefficient realization, native
  forgetting, and constructibility found the canonical general derived comparison,
  coefficient realization, and landed sectionwise module comparison used above.
  `grep -rn 'lem-sf-native-weil-open-proper-forgetting' lean/WeilConjectures`
  and the upstream-name-map search found no existing declaration for this item.
  `rg` over `lean/Sheaf` found related native comparisons, not the complete
  normalized open/proper statement. No duplicate definition node is needed.

The current blueprint was read at
`literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/cor-coef-verdier-weil-equivariance.proof.md`,
especially the Frobenius-equivariance paragraph and its distinction between native
derived constructions and exceptional adjoints. No blueprint-unit correction is
needed. The node's source path is historical metadata and is left unchanged.

### Validation

All compilation uses the prescribed `scompile.py`; no direct library edit or
local/global build is performed. Initial elaboration repairs made the base field
explicit, supplied existing small coproduct instances without increasing any
limit, retained the explicit native over-structure for compactifications, and
expressed the common Frobenius chain map using its actual degreewise formula.
The final clean compile and delivery preflight are recorded by the delivery tool.

## Second reading by Q99

The dispatch explicitly forbids starting other agents and assigns the independent
review to the maintainer. This section therefore records the worker's second
reading, not a fabricated independent-worker review. I reopened the node and
compared it with each declaration above. I checked each finite-field, characteristic,
separatedness and finite-type hypothesis, the actual native ordinary derived
categories, finite global stratification in every degree, the exact integer-power
free functor, both derived-unit arrows and their common source, the formula for
the proper Frobenius chain map, and the order of the chosen compactification.
The first self-reading missed the distinction between the elementary lift formula
and the derived commuting square; the maintainer's return correctly identified it.
The repaired reading checks the actual source and target of both actions:
D(P_Y) U_Y F^W K to U_Y F^W K, and D(P_Y) F^c U_X K to F^c U_X K.
The c⁰ square has those actions as its two vertical arrows, c⁰_K below, and
D(P_Y)(c⁰_K) above, for every native derived K. The ordinary action's definition
uses only derived a, the open comparison, and the input theta; it cannot be a
conjugate of the native action by definition. The node gains only its Lean record
and the two definition-owner statement dependencies.


## Repair of returned head 9fe287dcfc8f

1. The maintainer is right that the former `proper_frobenius` is an elementary
   degreewise lift formula and does not state compatibility between the two
   derived actions. It remains only as that elementary formula. The repair adds
   `nativeDerivedStructure`, obtained by exact localization of `IsoAlgebra.strNatIso`;
   `ordinaryProperFrobenius`, obtained by deriving the actual sheaf comparison a
   and its two unit-normalized composition factors; and `ordinaryOpenFrobenius`,
   obtained by exact localization of the actual open sheaf comparison.
   `ordinaryFrobeniusComparison` assembles these in the chosen j!/Rp_* order.
   `ordinaryCompactSupportFrobenius` then applies the ordinary functor to the
   input localized theta. `nativeCompactSupportFrobenius` instead applies the
   localized native structure at F^W K. The new middle conjunct of `open_proper`
   is exactly D(P_Y)(c⁰_K) followed by the ordinary action equals the native
   action followed by c⁰_K, for every derived K. It is not merely an equation
   of termwise maps, and the ordinary action is not defined using c⁰. The main
   docstring now explains descent of that square from common K-injective
   representatives via the derived units and the independently derived a.
2. Removed the two theorem nodes added solely as helper ownership from stmt_deps.
   Added the existing-definition ownership records described below and moved the normalized coefficient iso under the presentation definition
   ownership node, which cites `lem-sf-locally-finite-coefficient-ring-realization`.
   The latter is necessary because the normalized coefficient isomorphism is
   chosen from that theorem. Its finite-field normalization determines the
   actual coefficient map; no new choice or hollow object is introduced.
   The existing theorem modules are left unchanged. Searches and declaration
   signatures for the new ownership records were checked against current live
   source. The sandbox item statement, proof and proof_deps are identical to
   current main; the original return's mathematically correct clauses remain.

Advisories: the naturality conjunct is the automatic naturality of a constructed
natural isomorphism, and is retained only to expose the node's all-derived-maps
clause. It supplies no substitute for Frobenius equivariance. No independent
second worker was started, as the dispatch forbids this; the maintainer's
independent return is incorporated explicitly above.

## New nodes

`def-sf-exact-square-derived-unit-arrows` owns the existing definitions
`KInjectiveExactSquare.sourceIso`, `leftUnit`, `rightUnit`, and `delta` in
`Sheaf.CategoryTheory.KInjectiveExactSquareComparison`, with `existing: true`.
It specifies additive H', H, exact r, s, a strict square, arbitrary candidate
right-derived functors and their unit maps. It defines the two actual arrows
with their exact-localization factors, and their quotient when the first is
invertible; it asserts no normalized-comparison theorem. Source: Stacks 070I,
070Y and 070K, the explicit module formulas at lines 57--104. LeanSearch found
the general totalRightDerivedUnit/CatCommSq APIs; LeanFinder found generic
derived-adjunction units and derivability squares; Mathlib grep found no
specialization. Repository search located precisely these real definitions
under a theorem record, with no definition owner. Blueprint searches returned
no exact node. It reuses the declarations, creating no Lean module or duplicate.
The definition accepts arbitrary compatible unit maps, so no K-injectivity,
enough resolutions, or invertibility premise is silently required to define
a and b; delta alone takes the IsIso witness it needs.

`def-sf-native-sectionwise-module-presentation` owns the existing definitions
`nativeModuleCoefficientIso`, its `IsMonHom` instance, `nativeOrdinaryPresentation`,
`NativeOrdinaryModules`, and `nativeToOrdinaryModules` in
`Sheaf.Paper.NativeModuleConstructibilityComparison`, with `existing: true`.
It specifies the coefficient realization and the functor consisting of native
scalar forgetting, action restriction along the normalized coefficient iso,
and the already existing internal/sectionwise equivalence. It does not assert
the constructibility-comparison theorem. Source: Stacks 03CW/03CY and the
native module presentation in the blueprint equivariance argument; the actual
formulas are at module lines 57--101. LeanSearch returned unrelated ordinary
module presentations and adic completions; LeanFinder returned tilde,
forgetToSheafModuleCat, condensed modules, and pushforwardCongr, not this
native specialization. Mathlib grep returned no match; repository grep located
these existing declarations, with no definition-node ownership. Blueprint
search returned no exact node. The general internal/sectionwise equivalence
already has `def-weil-pbc-internal-abelian-sheaf-module-equivalence`, which this
node cites instead of redefining. It cites coefficient realization directly, while the item cites this definition
owner; this uses the second alternative requested in the return. Empty T and the zero module are retained; the construction
has no finite-type assumption and its equivalence is not assumed by definition.

Dry-run repair: the live new-node schema also requires `import_flags: []`; both
ownership records supply it. Existing declaration signatures omit the
`noncomputable` modifier, as requested by preflight. The coefficient iso is moved
under its definition ownership node (the return's allowed alternative), rather
than making the theorem a direct statement dependency of the item.
