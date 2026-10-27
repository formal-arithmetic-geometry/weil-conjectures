## Worker report

Delivered module: `Sheaf.Paper.NativeEncodingDerivedOperations`. The primary theorem is
`AlgebraicGeometry.ProEtale.NativeEncoding.native_encoding_derived_operations`; the
`lean.declarations` list records the constructions and component statements which together
render the complete node. All ten named theorem proofs are `sorry`; no definition contains
`sorry`. Every component is part of this node's specified encoding/comparisons, rather than
an independent new notion. No statement correction, new node or dependency repair is needed.

Source reading: Bhatt--Scholze PDF, Definitions 6.8.1 and 6.8.3, read with pdftotext;
these supply coefficient modules, not the encoding theorem. The latter is the agent-formulated
comparison in the assigned node. Read the actual native Adic/Module.lean, Adic/AdicSheafForgetAb,
WeilSheaf/Category.lean, LowerStar.lean, and RightDerivedFunctor/IsoAlgebra.lean signatures
and docstrings, including the fact that Frobenius pullback is implemented by direct image
along inverse geometric Frobenius. Read the current coefficient-ring realization, finite-span
comparison and derived module pushpull modules. The current blueprint search found no imported
unit stating this theorem; the node itself records no imported blueprint ancestor. The required
CompactObject example has been withdrawn and now has no declarations; its node uses an
existing Mathlib match. The delivery follows the current module-mode header conventions.

The following table matches every hypothesis and conclusion. Names in the Lean column are
in `AlgebraicGeometry.ProEtale.NativeEncoding` unless qualified.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Finite field k0 | `(k₀ : Type u) [Field k₀] [Finite k₀]` in the primary theorem. |
| Algebraic closure k and geometric base change | The recorded native framework uses `AlgebraicClosure k₀`; `(T ↘ Spec (CommRingCat.of k₀)).geometricFiber` is its geometric base change, and `Scheme.Hom.geometricFiberMap f (comp_over f (Spec (CommRingCat.of k₀)))` is the base-changed map. This uses the framework's algebraic-closure model, with no additional field or descent hypothesis. |
| Prime ell, different from characteristic | `(l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]`. |
| Omega with its native topology | Existing `PadicAlgCl l`, lifted to `ULift.{u + 1}` in the native vector coefficient category; existing `adicConstantSheaf` carries the locally finite continuous-function coefficient. |
| X0,Y0 separated finite-type k0-schemes | `X.Over`, `Y.Over` and `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` on both structure maps. Finite type is the latter two conditions. |
| f0 separated finite type over k0 | `(f : X ⟶ Y) [f.IsOver ...] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`. |
| Common larger module universe / small pro-etale sites | Schemes in `Scheme.{u}`, the recorded `Scheme.ProEt` site with object universe u+1 and morphism universe u, and both native and internal coefficients/modules in u+1. No equality between site object and morphism universes is imposed. |
| Native B,A,F,W | Existing `adicConstantSheaf`, `AdicSheaf`, `WeilSheaf.frobeniusPullback`, and `ProEtaleWeilSheaf`, with no private replacements. |
| R = p* condensed Omega, internal R-modules | Existing `condensedRingObj (Profinite.padicAlgClRingObj l) T` and `Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) ...`. |
| Canonical theta | `coefficientIso` is the actual composite used in the proof of `locallyFiniteCoefficientRing_realization`: underlying `globalCoefficientIso` followed by `padicAlgClSheafIsoAdicConstantSheaf`. It is not an arbitrary ring isomorphism. `coefficientIsoMon` states its ring compatibility. |
| Reinterpret native action, transport by theta, internal encoding | `encoding := AdicSheaf.forgetAb l T ⋙ Mod.comap (coefficientIso l T).hom`. The existing mapMod lax tensorator converts the balanced native vector action to its internal abelian action; scalar restriction is the forward R-to-B map. |
| Exact heart equivalence E | `encodingAdditive`, `encoding_isEquivalence`, `equivalence := encoding.asEquivalence`, and the two exactness clauses of `encoding_exact_derived`. The data functor is defined before its properties, without a hypothetical encoding parameter. |
| Unchanged underlying abelian sheaf and restrictions | `encoding_underlying` is equality of functors to abelian sheaves. Equality retains both section restrictions and the action on morphisms. |
| Inverse via constants Omega -> B | `native_constant_action` states the action formula for every native module, including `equivalence.inverse.obj M`. It uses the actual presheaf tensorator and the monoid unit evaluated at a vector scalar to make the constant function. Together with the canonical equivalence counit (a morphism of R-modules), the inverse B-action is the transported action through theta inverse, and its vector action is exactly restriction to constants. There is no assumption that tensor sheaf sections equal tensors of section modules. |
| Preserve and reflect K-injectives | The final iff of `encoding_exact_derived` uses `CochainComplex.IsKInjective` for the actual degreewise encoding. This is precisely the recorded null-homotopy condition. |
| D(E), unbounded equivalence | `derivedEncoding := encoding.mapDerivedCategory` and its `IsEquivalence` clause. The inverse is the descended termwise inverse of E. |
| Ordinary native direct image identified with internal pushforward | `encoding_ordinary_operations` supplies p between the actual `adicLowerStar` and `CondensedRing.lowerStar`, fixing its value to the identity on every section. `pushComparison` selects this uniquely determined map. |
| Module pullback identified, tensor formula and exactness | The same theorem supplies q between actual `adicUpperStar` and `CondensedRing.upperStar`. Its mate under the two actual module adjunctions is p, which uniquely fixes q. The internal functor is the recorded mapMod followed by `Mod.extendScalars` along the forward coefficient map: precisely R_X tensor over inverse-image R_Y with inverse-image M. Both finite-limit and finite-colimit preservation are stated. Native pullback is already exact in the framework and is also exact through this equivalence. |
| Frobenius and coefficient precomposition | The ordinary theorem applies to EVERY scheme map, hence to Frobenius and its inverse. Its last equation is the actual `condensedPushforwardHom` / `adicConstantSheafToLowerStar` ring-realization square. Taking its mate gives the inverse-image square. |
| U and V = D(E)D(U) | `realization` is literally `(IsoAlgebra.forget ...).mapDerivedCategory ⋙ derivedEncoding ...`. |
| First displayed ambient natural isomorphism | `weilDerivedPullComparison` constructs it by localizing `IsoAlgebra.mapOfNatIsoCompForgetIso` for the ACTUAL `adicUpperStarGeometricFiberMapCompFrobeniusIso`, then localizing q. The first primary-theorem conjunct repeats its existence in the exact stated setting. |
| Second displayed ambient natural isomorphism | `weilDerivedPushComparison` constructs it from `rightDerivedFunctorMapOfNatIsoCompForgetIso` for the ACTUAL `adicLowerStarGeometricFiberMapCompFrobeniusIso`, composed with `derivedPushComparison`. The second primary-theorem conjunct records its existence. |
| Rf_R* is total ordinary right derivation | The functor is the recorded `moduleObjectDerivedPushforward`, definitionally the generic `.rightDerivedFunctor` of the full internal module direct image. The recorded arbitrary-quasi-isomorphism interface is imported; native functors use their existing K-injective total-right-derived implementation. Both are the ordinary universal right-derived functor, not a different derived category or completion. |
| Same resolutions and given Frobenius transport | `weil_resolution_comparison` states preservation of K-injectivity by the actual U then E. `derivedPushComparison_unit` gives the commuting normalization equation on such models with the actual `rightDerivedFunctorUnitQ` and exact-localization factors. The constructed Weil comparison explicitly composes the native IsoAlgebra transport comparison; no Frobenius action is postulated. |
| Lf_R* equals termwise pullback | The last primary-theorem conjunct identifies recorded `moduleObjectDerivedPullback` with `CondensedRing.upperStar ... .mapDerivedCategory`. |
| No constructibility restriction | All these functors use `DerivedCategory (ProEtaleWeilSheaf ...)` or the full module category. No `WeilComplex`, bounded subcategory, constructibility predicate or boundedness hypothesis occurs. |

Dependency declarations used, with their owning modules:

- `def-sf-native-weil-derived-framework`: `WeilConjectures.WeilSheaf.LowerShriek` is
  the recorded public entry module. Its imported `Category` and `LowerStar` supply
  `ProEtaleWeilSheaf`, `WeilSheaf.frobeniusPullback`, `ProEtaleWeilSheaf.upperStar`,
  `ProEtaleWeilSheaf.lowerStar`, and the native Frobenius comparisons. Adic/Module supplies
  `AdicSheaf`, `adicUpperStar`, `adicLowerStar`, `adicUpperStarLowerStarAdjunction`;
  Adic/AdicSheafForgetAb supplies `AdicSheaf.forgetAb` and `weilCoefficientsForgetAb`.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`, `Scheme.ProEt`
  and its topology. These are inherited public imports of the framework.
- `sk-def-sfb-qlbar-condensed`: `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`,
  `Profinite.padicAlgClRingObj`, whose underlying ring is `padicAlgClCondensedRing`.
- `sk-def-sfb-pulled-back-coefficients`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `condensedRingObj` (the unbundled underlying object of recorded `coefficientRing`).
- `lem-sf-locally-finite-coefficient-ring-realization`:
  `Sheaf.Paper.LocallyFiniteCoefficientRingRealization`, `locallyFiniteCoefficientRing_realization`.
  We use its actual defining composite, not choose an arbitrary existential witness.
- `sk-def-sfb-module-objects`: `Mathlib.CategoryTheory.Monoidal.Mod`, `CategoryTheory.Mod`.
- `def-sfb-right-derived-functor`:
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`, imported as the recorded
  universal arbitrary-quasi-isomorphism interface. Existing native `.rightDerivedFunctor`
  supplies the same total right derivation with its existing K-injective resolutions.
- `sk-def-sfb-module-pushforward-pullback`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`,
  `CondensedRing.lowerStar`, `upperStar`, and `upperStarLowerStarAdjunction`.
- `sk-def-sfb-module-derived-pushpull`: `Sheaf.Paper.CondensedModuleDerivedPushpull`,
  `moduleObjectDerivedPushforward` and `moduleObjectDerivedPullback`.

The existing proof-dependency modules are imported privately, including the finite-span,
fixed-pair, cartesian-coefficient, ringed-site Grothendieck, tensor and exact-square modules.
Mathlib's `Functor.mapDerivedCategoryFactors` is used in the computational normalization.
The extra public imports expose the canonical coefficient construction, derived units,
localization functoriality and adjunction mates used in actual declaration bodies/signatures.

Searches actually run:

- msearch LeanFinder: `Exact equivalence between module objects in vector space sheaves and
  modules in abelian sheaves compatible with derived pushforward and Frobenius` returned
  eight hits concerning generic SheafOfModules pushforward and condensed modules, no match.
- msearch LeanSearch: `Equivalence of native adic sheaves as modules in vector space sheaves
  with internal module objects in abelian sheaves` returned generic module/sheaf declarations,
  including Scheme.Modules and SheafOfModules.instAbelian, no native equivalence.
- msearch Loogle: `CategoryTheory.Functor.mapMod,CategoryTheory.Mod.comapEquivalenceOfIsIso`
  returned zero hits and reported unknown identifier `CategoryTheory.Functor.mapMod`.
  The upstream mapMod and comap equivalence were subsequently read directly in source.
- msearch Mathlib grep: `mapMod.*[Ee]quivalence|[Ee]quivalence.*mapMod` under CategoryTheory
  returned zero hits.
- rg of native/encoding names and the item id in `lean/WeilConjectures`, `lean/Sheaf`,
  and `dag/lean_names_upstream.json` found no declaration of this item. The native
  `AdicSheaf.forgetAb` gives the needed forward functor; the finite-span comparison
  treats section-module/internal-module encoding, not the vector-module equivalence.
  EtaleConstantModuleTensor's private nativeEncoding is a different presheaf construction.
- `python3 tools/blueprint_refs.py search 'native encoding'` returned zero blueprint nodes.
  rg of `literature/blueprint/latest/blueprint` found no imported statement for this item.

Edge cases checked before and during drafting:

- Empty scheme, empty site objects and zero module: constant functions and both module
  action unit identities still make sense, with no nonempty/positive-rank assumptions.
- Zero complex and complexes unbounded in either direction: the K-injective condition
  and all localizations use cochain complexes indexed by all integers.
- Identity and arbitrary geometric maps: the ordinary comparison is stated for every map;
  the Frobenius/inverse-Frobenius instances are covered without additional descent data.
- No assumption that a local finite-function image lies in one finite field globally on
  a non-quasi-compact site object; the coefficient realization remains the existing sheaf.
- Every prime ell distinct from the base characteristic is included, including ell = 2.
- The larger module universe is u+1, retaining the pro-etale site's different object and
  morphism universes. No universe equality or smaller test universe is introduced.

Validation: scompile.py compiles the complete module in module mode, both in the private
sandbox module and at its actual library name. The last completed compile before packaging
was clean (12.9 seconds sandbox / 9.8 seconds library). The dry run passed server preflight and compilation at commit `caf9ccf775b`. The
delivery wrapper reruns these checks before pushing. No global build or direct git command
was run.

## Second reading by Q91

This is the author's second pass; the maintainer supplies the independent review as specified
by the dispatcher brief. I reread the node statement against the complete module and the
native operation bodies. The first draft had only an existential ordinary pullback comparison;
I fixed it to be the mate of the identity-on-sections direct-image comparison, so its
normalization is determined. I also replaced bare existence of the displayed ambient
comparisons as the only interface by real constructed `weilDerivedPullComparison` and
`weilDerivedPushComparison` definitions, using the recorded Frobenius transports explicitly.
`derivedPushComparison_unit` now states the actual comparison on K-injective models.
The constant scalar formula uses the presheaf tensorator, addressing the node's warning
against an unjustified sectionwise tensor identification. The finite-field, characteristic,
separatedness and finite-type assumptions are all matched above; no constructibility or
boundedness assumption was introduced. No remaining mismatch or statement dispute was found.
