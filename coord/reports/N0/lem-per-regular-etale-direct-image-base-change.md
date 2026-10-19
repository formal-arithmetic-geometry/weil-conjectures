## Worker report

The module `Sheaf.AlgebraicGeometry.RegularEtaleDirectImageBaseChange` states
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_regular`, with proof
`sorry`. It introduces no definition and changes only the item's `lean` record.
There are no new nodes, dependency repairs, statement corrections or disputed claims.

Source checked directly: Illusie--Laszlo--Orgogozo, Travaux de Gabber,
Expose XVII, Proposition 4.2.1, printed p. 281 (PDF page 287). Its locally
Noetherian regular base-change statement specializes to the node's Noetherian
schemes and prime-power coefficient integer. The source's square and canonical
exchange have the same orientation as the Lean statement.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Prime ell | `(ℓ n : ℕ) (hprime : ℓ.Prime)` |
| n at least one | `(hn : 1 ≤ n)` |
| Lambda = Z/ell^n Z | `ULift.{u + 1} (ZMod (ℓ ^ n))`; the canonical ring equivalence `ULift.ringEquiv` merely implements the established coefficient size convention |
| Noetherian schemes X and Y | `{X Y V : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]`; Mathlib's Noetherian scheme class is equivalent to a finite affine cover with Noetherian section rings (`isNoetherian_iff_of_finite_iSup_eq_top`) |
| h : Y to X | `(h : Y ⟶ X)` |
| ell invertible on both schemes | `hX : IsUnit (ℓ : Γ(X, ⊤))` and `hY : IsUnit (ℓ : Γ(Y, ⊤))`; invertibility is local and the unique local inverses glue, so this is exactly invertibility on the schemes |
| h flat | `[Flat h]` |
| Every finite extension of every residue-field fibre is regular | `hreg` quantifies over `x : X`, `L : Type u`, `[Field L]`, `[Algebra (X.residueField x) L]`, `[Module.Finite (X.residueField x) L]`, and asserts `IsRegularScheme (pullback (h.fiberToSpecResidueField x) (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) L))))` |
| g any qcqs morphism | `(g : V ⟶ X) [QuasiCompact g] [QuasiSeparated g]` |
| V_Y and its two projections | `pullback g h`, `pullback.fst g h`, `pullback.snd g h` |
| K any bounded-below complex of constant Lambda-module etale sheaves | `K : DerivedCategory.Plus (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ n)))))` |
| Canonical module-adjunction derived exchange | `derivedBaseChangeMapPlus (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ n))))` on the canonical pullback commutative square, applied to K |
| Exchange is an isomorphism | `IsIso (... .app K)` |
| No constructibility, finite-type h, or Noetherian V requirement | No corresponding binders or conditions occur |

The regular-fibre condition uses the recorded scheme-theoretic fibre and its
canonical map to the residue-field spectrum, followed by actual base extension.
It does not replace a canonical map by an arbitrary comparison. Finite extension
fields are quantified in the same universe as the residue field and schemes;
all finite extensions have such representatives. In particular this is not a
smaller, potentially vacuous test universe.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; Noetherian schemes
  use `AlgebraicGeometry.IsNoetherian` and its finite-affine-cover equivalence in
  `Mathlib.AlgebraicGeometry.Noetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, with
  its documented stalkwise criterion.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`,
  namely `IsLocallyNoetherian X ∧ IsRegular X`, retaining both parts.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber` and
  `Scheme.Hom.fiberToSpecResidueField` (the canonical second projection).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: the locally-finite-type
  node's `QuasiCompact` notion, defined in `Morphisms.QuasiCompact`; no
  `LocallyOfFiniteType` hypothesis is imposed.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`:
  `AlgebraicGeometry.QuasiSeparated`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `pullback`, `pullback.fst`, `pullback.snd`, and `pullback.condition`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: the recorded module
  encoding and `DerivedCategory.Plus`. This module's current source was read
  through `scompile.py --source` because it is absent from the older checkout.
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients` supplies the underlying
  `Etale.DerivedCategoryModule` convention.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.upperStar`,
  `Etale.lowerStar`, and `Etale.upperStarLowerStarAdjunction`; the derived
  direct images in the canonical exchange are `rightDerivedFunctorPlus`.
- `WeilConjectures.SixFunctors.BaseChange.Derived`:
  `Etale.derivedBaseChangeMapPlus`, the recorded canonical derived exchange.
- `Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients`:
  `Etale.exchange_forget_coefficients`; its full signature identifies this
  exact ModuleCat-valued map with the abelian exchange, including the endpoint
  comparisons and the equivalence of isomorphism predicates.

The module also imports the stated proof dependencies
`EtaleLocalityBaseChange`, `GRing`, `PopescuSmoothing`,
`ExistsDirectedReindexing`, and `SmoothBaseChangeLimit`. The theorem docstring
carries all six steps of the DAG proof with their node names, including the
coefficient comparison, affine localization, regular ring-map criterion,
Popescu approximation, directed smooth inverse limit and final assembly.

Edge cases checked: n = 1 is included; n = 0 is excluded exactly as in the
node. Ell = 0 or 1 is excluded by primality. Empty X, Y or V are allowed;
regularity of empty fibres is vacuous and the extended fibres are honest
pullbacks. The identity extension of each residue field is included in `hreg`.
The zero complex and complexes with arbitrarily negative lower bounds are
included by `DerivedCategory.Plus`. No affine, separated, finite type or
Noetherian condition has slipped onto V. No finite presentation or finite type
condition has slipped onto h. There is no bound on cohomological degree and no
constructibility condition.

Searches made with `msearch.py` for this item:

- LeanFinder: `Regular base change for bounded below etale module sheaves along
  flat geometrically regular morphisms`: eight hits, concerning stability of
  etale/smooth morphisms and ring etaleness; no derived direct-image theorem.
- Loogle: `"baseChange", "regular"`: four hits, concerning regular sequences,
  flat modules and regular categories; none is this statement.
- Grep: `regular.*baseChange|baseChange.*regular|regularBaseChange|geometricallyRegular`:
  nine Mathlib hits, all regular categories or regular sequences/modules.
- LeanSearch: `Derived direct image of etale torsion module sheaves commutes
  with regular base change of Noetherian schemes`: eight hits concerning
  structure-sheaf modules, flat scalar extension or etale stability; no match.
- `rg` on `WeilConjectures/` and `lean/Sheaf/` for regular/base-change patterns
  and the node id: only unrelated ring-theoretic base change and hypercohomology
  couple regularity in existing Sheaf modules. No occurrence of this node id
  upstream. `dag/lean_names_upstream.json` and both source libraries have no
  `regularBaseChange`, `baseChange_of_regular`, or proposed theorem-name match.
- The exact proposed name `isIso_derivedBaseChangeMapPlus_of_regular` was
  searched in Mathlib, upstream and Sheaf sources, with no hit.

Validation: `scompile.py N0 lem-per-regular-etale-direct-image-base-change`
compiled the delivered file in sandbox and library modes, cleanly, in 2.5 and
2.4 seconds respectively. Every universe and binder is explicit, with
`autoImplicit false`; the sole theorem proof remains `sorry` as required.

## Second reading by N0

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
