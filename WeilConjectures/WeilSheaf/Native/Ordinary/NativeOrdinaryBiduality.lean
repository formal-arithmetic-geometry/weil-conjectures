/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.BifunctorHomBidual
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Bidual
public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
public import WeilConjectures.WeilSheaf.SixFunctors.WeilGeometricHomConstructibility
public import WeilConjectures.PoincareDuality.Verdier

/-!
# The double-dual morphism of `ℓ`-adic sheaves

The biduality morphisms `M ⟶ 𝓗om(𝓗om(M, N), N)` of sheaves of `ℚ̄_ℓ,X`-modules
(`CategoryTheory.Mod.bidual`) are natural in `M` and dinatural in `N`; they form an evaluation
(`CochainComplex.BifunctorEvaluation`) for the internal hom
`AlgebraicGeometry.ProEtaleWeilSheaf.ordinaryIhomBifunctor`
(`AlgebraicGeometry.ProEtaleWeilSheaf.ordinaryBifunctorEvaluation`), hence define the double-dual
morphism `M ⟶ Hom(Hom(M, I), I)` of hom complexes of `ℓ`-adic sheaves
(`CochainComplex.bifunctorHomBidual`).
-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})

/-- The biduality morphisms `M ⟶ 𝓗om(𝓗om(M, N), N)` of `ℓ`-adic sheaves, as an evaluation for
the internal hom bifunctor. -/
noncomputable def ordinaryBifunctorEvaluation :
    CochainComplex.BifunctorEvaluation (ordinaryIhomBifunctor l Y) where
  ev M N := Mod.bidual M N
  naturality f N := Mod.bidual_naturality f N
  dinaturality M _ _ g := Mod.bidual_comp_ihom_map M g

variable {l} {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  (Z : Over (Spec (.of k))) [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

/-- The comparison `D(ℓ-adic sheaves on Z) ⥤ D(condensed ℚ̲̄_ℓ-modules on Z)` of the two models of
`ℓ`-adic complexes: forget the `ℚ̄_ℓ`-linear structure and restrict scalars along the
identification of the coefficient rings. -/
noncomputable abbrev ordinaryToCondensed :
    DerivedCategory (ProEtale.AdicSheaf l Z.left) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
        (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj l) Z.left)) :=
  (ProEtale.AdicSheaf.forgetAb l Z.left ⋙
    Mod.comap (ProEtale.nativeModuleCoefficientIso l Z.left).hom).mapDerivedCategory

/-- **Verdier biduality for `ℓ`-adic complexes, at the level of hom complexes** (blueprint:
`det-pd-biduality-coefficients`, case (iv), for the model of `ℓ`-adic sheaves as sheaves of
`ℚ̄_ℓ,Z`-modules). Let `Z` be a separated scheme of finite type over a field `k` of characteristic
`≠ ℓ`, `I` a K-injective complex of `ℓ`-adic sheaves representing the dualizing complex
`ω_Z = Ra_Z^! ℚ̄_ℓ` (`ProEtale.CondensedRing.dualizingComplex`), and `M` a complex of `ℓ`-adic
sheaves which is bounded with constructible cohomology. Then the double-dual morphism
`M ⟶ Hom(Hom(M, I), I)` of hom complexes is a quasi-isomorphism.

This is the constructible biduality `ProEtale.CondensedRing.isIso_verdierBiduality` of the
condensed model, read in the model of `ℓ`-adic sheaves. The missing input is the comparison of
the two models for the double-dual morphism: the coefficient equivalence `ordinaryToCondensed`
identifies the derived internal homs (`lem-sf-native-geometric-hom-comparison`, see
`ProEtaleWeilSheaf.nonempty_nativeGeometricForget_derivedHom_iso`), but it is not known yet to
carry the hom-complex double-dual morphism to `ProEtale.CondensedRing.verdierBiduality`, the
transpose of the Koszul-braided evaluation in the closed structure of `Dᵇc` (blueprint:
`cor-coef-verdier-weil-equivariance`, "evaluation, biduality ... are Weil equivariant"). -/
theorem quasiIso_bifunctorHomBidual_ordinary {M I : CochainComplex (ProEtale.AdicSheaf l Z.left) ℤ}
    [I.IsKInjective]
    (eI : Nonempty ((ordinaryToCondensed Z).obj (DerivedCategory.Q.obj I) ≅
      (ObjectProperty.ι _).obj (ProEtale.CondensedRing.dualizingComplex l Z)))
    (hM : ProEtale.constantModelBoundedConstructible (Profinite.padicAlgClRingObj l) Z.left
      ((ordinaryToCondensed Z).obj (DerivedCategory.Q.obj M))) :
    QuasiIso (CochainComplex.bifunctorHomBidual (ordinaryBifunctorEvaluation l Z.left) M I) :=
  sorry

end AlgebraicGeometry.ProEtaleWeilSheaf
