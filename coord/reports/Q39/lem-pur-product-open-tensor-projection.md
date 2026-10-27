## Worker report

This delivery states `WeilConjectures.ProductOpenTensorProjection.productOpenTensorProjection`
in `Sheaf.Paper.ProductOpenTensorProjection`. Its sole postponed theorem is that statement.
The other declarations construct its objects, specified maps, coordinate transports and
conclusion predicate `Assertion`; every definition has actual data. No source statement,
proof step, dependency list or stage-1 review field is changed. Q55's completed stage-1
split remains the plan for this stage-2 statement. There was no previously recorded Lean
statement for this node and no repair note for this item.

### Hypotheses and objects

- The fixed finite-field and positive finite coefficient datum is `S : PurityFiniteSetting`.
  `S.Coefficient` is the existing standard size lift of O_E/(varpi_E^n), not a newly chosen
  coefficient ring; its finiteness is `FiniteOpenProduct.settingCoefficientFinite`.
- The five schemes are `Over (Spec (CommRingCat.of S.field.k))`. Each has the separated,
  locally finite-type and quasi-compact structure-morphism hypotheses, expressing separated
  finite type over k. An `Over` morphism retains the map over k, not just a bare scheme map.
- `a : Xb ⟶ B`, `b : Zb ⟶ B` have `IsProper a.left` and `IsProper b.left`;
  `j : X ⟶ Xb`, `k : Z ⟶ Zb` have the two `IsOpenImmersion` hypotheses.
  These are exactly the chosen compactifications, with f=j≫a and g=k≫b.
  Conversely an arbitrary compactification of f or g supplies these objects and maps,
  using the structure map of its proper factor. Thus no choice of compactification is
  discarded. Compactifying schemes are separated finite type because they are proper
  over the separated finite-type base. The composites f and g are separated finite type:
  all morphisms between these separated finite-type k-schemes have those properties.
  No equation identifying f or g with a separately supplied redundant variable is needed.
- `M` and `N` are `DerivedCategory.Plus` objects on the respective small pro-etale sites,
  with `ModuleCat.{u+1} S.Coefficient` coefficients. The two `FixedEtaleOriginWitness`
  binders retain the actual bounded-below etale antecedent and its comparison isomorphism.
  They are not replaced by existence or constructibility assumptions. `.obj` passes the
  inputs into the ambient unbounded category; all subsequent tensors occur there.
- Quasi-compactness of k needed by the existing proper/open mate is supplied by
  `finiteTypeOpenQuasiCompact S Zb k.left`: a finite-type scheme over a field is locally
  Noetherian, hence its open immersions are quasi-compact. It is not an extra hypothesis.
- `product a b`, `product (j≫a) (k≫b)` and `product a (k≫b)` are respectively C, P and W.
  These reuse the dependency's named, irreducible wrapper of Mathlib's chosen pullback.
  `first a b`, `second a b`, `second a (k≫b)` are r, t and v. The first and second
  projections of P are p and q. `rightOpen a b k`, `leftOpen a (k≫b) j` and
  `productOpen a b j k` are i, j_q and u. `openComposition` is j_q≫i=u.
  Thus h=fp=gq and c=bt=ar are the common composites given by the pullback equations.
- `H`, `J`, `D`, `F`, `K`, `KD`, `m` and `L0` render exactly the corresponding notation.
  L is `(ProperOpenPush A a).obj (H A j M)`, and E is `(pull A i).obj (F A a b j M)`.
  The finite direct-image composition dependency is imported as prescribed; there is no
  R_c term in these conclusions requiring a further use of its compositor.

### Specified maps

`tensor`, `tensorMap`, `pull`, `gamma`, `rho`, `beta`, `square`, `composeEq` and `compTo`
are the existing `FiniteOpenProduct` constructions, not copies of their definitions.
`finiteShriek` is the normalized fixed-scalar presentation of the recorded intrinsic
extension by zero. The intrinsic realization equivalences and canonical K-flat/termwise
pullback comparisons are those already used by the open-product dependency.

`projection` is `properOpenProjection` followed by direct image of the canonical
left-derived-to-exact pullback comparison in the second tensor factor. Consequently its
pi is the counit-defined map, never an arbitrary projection isomorphism. `exchange` is
the analogous canonical endpoint transport of `derivedBaseChangeMap`, the Ex_* of the
exchange/projection definition. `A0` specializes this to (a,b,H). `B0` composes the
k/b pullback compositor, the exchange for (a,k≫b,H), and direct image of the normalized
open beta for j. This is precisely Ex_! for the chosen (j,a) and its base change
(j_q,v), not a new compact-support operation.

`betaI` is beta:E≅K, first using the canonical projection compositor and then the
recorded unit-normalized open base change. `chi` extends its inverse by i_! and then
applies the counit of i_!⊣P_i. No inverse of chi appears anywhere. `d` is gamma for
j_q followed by the j_q/v projection compositor. `iTensorSecond` identifies P_iP_tJ
with P_vN by the pullback square and the inverse unit N≅P_k k_!N. `w` is gamma_i,
extension of this identification and d, and the canonical open compositor to u_!D.

`nu` is exactly the existing `rho A k L0 N`, which is sigma, delta_k, and extension of
the second signed sigma. `eta` is the k-counit on L0 tensored with 1_J. `delta` is
gamma_k followed by the stated P_kJ=N open-unit identification. `Gamma` is the
recorded normalized `properOpenMate` on (i,v,k,t), with no supplied replacement map.
Its properness hypotheses come from base change of a; `rightOpenQuasiCompact` is
quasi-compact base change of k. `s` is k_!(B0) then Gamma_K. `GammaD` includes only
Gamma_KD and the specified open compositor. `projectionTail` and `Psi` expand the
four actual factors in the displayed definition of Psi, with that compositor.

### Every conclusion clause

Unfolding the ordinary Prop definition `Assertion` gives these fifteen conjuncts,
in the order in the file. Composition `≫` is left to right, reversing the node's
juxtaposition convention.

1. `IsIso (eta ...)` is the invertibility assertion.
2. `eta ... ≫ nu ... = delta ...` is nu eta=delta, after the stated open units.
3. `w ... = tensorMap ... (chi ...) (𝟙 ...) ≫ e ...` is w=e(chi tensor 1).
   The e is exactly `FiniteOpenProduct.comparison`, the two-stage comparison through
   X times Zbar from the recorded open-product lemma.
4. `delta ... ≫ projectionTail ... = tensorMap ... (Gamma.app K) (𝟙 J) ≫
   projection ... ≫ push.map w` is the third displayed identity. The target compositor
   in `projectionTail` only identifies i_!j_q!D with u_!D, as the node instructs.
5. `eta ≫ nu ≫ Psi = tensorMap s (𝟙 J) ≫ projection ... ≫ push.map w` is the
   fourth displayed identity Psi nu eta=R_t(w) pi_t(s tensor 1).
6. `pull k |>.map eta` followed by `restrictNu.hom` equals `restrictEta.hom`:
   restriction of eta is identity on T=P_kL0 tensor N.
7. `pull k |>.map nu` followed by the inverse unit on T equals `restrictNu.hom`:
   restriction of nu is identity under exactly those same unit identifications.
8. Restriction of normalized delta followed by the inverse unit on T equals
   `restrictEta.hom`: the third identity-restriction clause.
9. `Nonempty ((finiteShriek A k).FullyFaithful)` expresses the fully faithful image.
10. The source of eta/delta is isomorphic to k_!T.
11. The target of eta/source of nu is isomorphic to k_!T. The remaining targets
    already are k_!T by definition, so these give the complete supported-image clause.
12. The common source of w and e(chi tensor 1) is isomorphic to u_!D. The target
    is literally u_!D. `mSupport` and `restrictW` construct the canonical compositor
    and open-unit identifications independently of either map being compared.
13. `IsIso e` retains the stated two-stage open tensor isomorphism, including its
    own source F tensor P_tJ. This does not assert invertibility of chi.
14. `restrictW.inv ≫ pull u |>.map w = openUnit_u_D.hom` says w restricts to 1_D.
15. The same equation for the actual composite `(chi tensor 1) ≫ e` says that the
    other map in the equality also restricts to 1_D. No equation is made tautological
    by defining a source identification from w or e.

There is no constructibility, finite Tor amplitude, invertibility of a projection map,
or invertibility of chi in the statement. The arbitrary unbounded comparison tools
are merely specialized to the node's bounded-below etale-origin inputs. Universes
retain the small-site object universe u+1 and morphism universe u, without equating them.

### Recorded dependencies read and used

- `def-pur-conventions`: `Sheaf.Paper.PurityFiniteSetting`,
  `WeilConjectures.PurityFiniteSetting` and its `Coefficient`.
- `def-pc-fibre-product`: Mathlib `Limits.pullback`, `pullback.fst`, `pullback.snd`,
  via the existing `FiniteOpenProduct.product`, `first`, `second`.
- `def-weil-compactifications-refinements`: upstream
  `WeilConjectures.Compactification.RefinementCategory`, `Compactification.Refinement`
  and its ambient `Compactification` open/proper factorization. Imported unchanged.
- `def-weil-derived-pullback-tensor-hom`: `Sheaf.Paper.DerivedPullbackTensorHom`,
  including `finiteDerivedPullback`, `finiteIntrinsicDerivedTensor` and its K-flat
  normalization; the existing open-product dependency exposes their fixed-scalar
  coordinates with `pull`, `tensor`, `tensorPullIso` and signed `sigma`.
- `def-weil-extension-by-zero`: `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`,
  `sfIntrinsicExtensionByZero` and `sfIntrinsicModuleEquivalence`; the already recorded
  open normalization uses `finiteShriek` in the equivalent fixed-scalar coordinates.
- `def-weil-pbc-etale-origin-witness`: `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`,
  `Scheme.FixedEtaleOriginWitness` with its retained `.complex` and `.iso`.
- `def-exchange-projection`: `Sheaf.Paper.ExchangeProjectionSuppliedDomains`,
  `SuppliedExchangeProjection.ExchangeProjectionStage`; at this finite level the
  prescribed original finite components are upstream `derivedBaseChangeMap` and
  `rightDerivedLowerStarProjectionMap`, as recorded in the dependency's note and
  original `finiteExchangeProjection`. Only canonical endpoint transports are added.
- `lem-sf-open-tensor-normalization`: `Sheaf.SixFunctors.OpenTensorNormalization`,
  `SheafOfModules.openTensorNormalization` and its public data, notably `finiteShriek`,
  `finiteGamma`; the actual fixed-scalar beta and open adjunction are reused.
- `lem-pur-finite-open-product-swap`: `Sheaf.Paper.FiniteOpenProductSwap`,
  `FiniteOpenProduct.finiteOpenProductSwap`, `comparison`, `restrictionSource` and
  the geometric/tensor helpers listed above.
- `lem-sf-proper-open-tensor-compatibility`: `Sheaf.SixFunctors.ProperOpenProjectionMate`,
  `ProEtale.properOpenProjectionMate`, `properOpenMate`, `properOpenProjection`.
- `lem-weil-derived-direct-image-composition`: `Sheaf.Paper.FiniteDirectImageComposition`,
  `ProEtale.finiteDirectImageComposition`, imported for the prescribed canonical convention.
- Proof dependencies `lem-cbc-extension-zero-composition` and
  `lem-weil-pbc-proper-base-change`: respectively the recorded
  `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence` module (already
  imported by FiniteOpenProductSwap), its canonical adjunction compositor, and Mathlib
  `AlgebraicGeometry/Morphisms/Proper` proper pullback instance. All other proof
  dependencies are listed above.

### Edge cases and searches

Identity opens make eta, nu, delta and the open comparators identities under their
specified units. Empty opens and zero inputs give the zero supported objects; no
nonempty, nonzero, or invertibility assumption excludes them. A nontrivial complement
leaves chi a possibly noninvertible counit, while its tensor with the supported factor
is compared as stated. Odd cohomological shifts retain the dependency's Koszul sigma
in rho, with two cancelling symmetries. Tensor values may be unbounded below and
remain in `FiniteD`, rather than being incorrectly forced into D+. Level n=1 is
included by the recorded positive-level datum. Arbitrary choices of both
compactifications and both etale-origin witnesses are retained.

Searches run with the prescribed msearch wrapper:

- LeanFinder: "Open tensor normalization and proper open projection identity for product
  compactifications in unbounded derived sheaves": eight results about sheaf sections on
  unions and scheme normalization coproducts; none states this map identity.
- Loogle: "derivedOpenImmersionLowerShriekProjectionIso, rightDerivedLowerStarProjectionMap":
  zero results; the first identifier is unknown in the Mathlib service. Its actual
  upstream declarations were found and read locally, and are reused.
- Mathlib grep: "productOpenTensorProjection|openTensorProjection|properOpenProjectionMate":
  zero results. A further grep for
  "properOpenProjectionMate|openTensorNormalization|rightDerivedLowerStarProjectionMap"
  also returned zero Mathlib results.
- Local rg of both `lean/WeilConjectures` and `lean/Sheaf` for the item tag and expected
  product-open-tensor names found no declaration for the node. The broader open tensor
  query found OpenImmersionTensorPiece.openTensorProjectionComponent/exists and an
  IntegralOpenExtensionReduction private helper; these concern one open or integral
  coefficient reduction, not the four product-compactification map identities.
  The existing generic proper/open mate and two-stage comparison were read and reused.
  A literal grep for the item id in WeilConjectures also returned no result.

No statement dispute, new node or dependency repair is needed. The theorem proof is
`sorry`, with all five natural-language proof steps in its docstring. Compilation
uses only scompile.py against the live library; the completed module is within the
60-second per-file limit, with no non-sorry warnings.

## Second reading by Q39

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
