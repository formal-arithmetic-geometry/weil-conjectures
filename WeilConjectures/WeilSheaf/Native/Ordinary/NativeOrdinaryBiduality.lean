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
import WeilConjectures.Algebra.Homology.BifunctorHomMonoidal
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDescentTwoColimit
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgetting
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgettingMonoidal
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.BifunctorHomBidualTransport
import WeilConjectures.CategoryTheory.Monoidal.Mod.IhomIso
import WeilConjectures.CategoryTheory.Monoidal.Closed.DualFullyFaithfulSubcategory
import WeilConjectures.PoincareDuality.Biduality.Constructible
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory

/-!
# The double-dual morphism of `ℓ`-adic sheaves

The biduality morphisms `M ⟶ 𝓗om(𝓗om(M, N), N)` of sheaves of `ℚ̄_ℓ,X`-modules
(`CategoryTheory.Mod.bidual`) are natural in `M` and dinatural in `N`; they form an evaluation
(`CochainComplex.BifunctorEvaluation`) for the internal hom
`AlgebraicGeometry.ProEtaleWeilSheaf.ordinaryIhomBifunctor`
(`AlgebraicGeometry.ProEtaleWeilSheaf.ordinaryBifunctorEvaluation`), hence define the double-dual
morphism `M ⟶ Hom(Hom(M, I), I)` of hom complexes of `ℓ`-adic sheaves
(`CochainComplex.bifunctorHomBidual`).

Into a K-injective model of the dualizing complex, this morphism is a quasi-isomorphism on bounded
constructible complexes
(`AlgebraicGeometry.ProEtaleWeilSheaf.quasiIso_bifunctorHomBidual_ordinary`): this is Verdier
biduality of the condensed model, `ProEtale.CondensedRing.isIso_verdierBiduality`.
-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

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

attribute [local instance] ProEtale.CondensedRing.boundedConstructibleBraiding in
/-- **Verdier biduality for `ℓ`-adic complexes, at the level of hom complexes** (blueprint:
`det-pd-biduality-coefficients`, case (iv), for the model of `ℓ`-adic sheaves as sheaves of
`ℚ̄_ℓ,Z`-modules). Let `Z` be a separated scheme of finite type over a field `k` of characteristic
`≠ ℓ`, `I` a K-injective complex of `ℓ`-adic sheaves representing the dualizing complex
`ω_Z = Ra_Z^! ℚ̄_ℓ` (`ProEtale.CondensedRing.dualizingComplex`), and `M` a complex of `ℓ`-adic
sheaves which is bounded with constructible cohomology. Then the double-dual morphism
`M ⟶ Hom(Hom(M, I), I)` of hom complexes is a quasi-isomorphism.

This is the constructible biduality `ProEtale.CondensedRing.isIso_verdierBiduality` of the
condensed model, read in the model of `ℓ`-adic sheaves. The coefficient equivalence `U` from
`ℓ`-adic sheaves to condensed `ℚ̲̄_ℓ`-modules is monoidal, so it carries the internal hom of
`ℓ`-adic sheaves to that of condensed modules (`CochainComplex.BifunctorMapIso.ofMonoidal`), and
the derived hom `RHom(-, I)` of hom complexes to the internal hom `RHom(-, ω)` of the derived
category (`DerivedCategory.bifunctorRHomOfComplexMapIso`). Condensed biduality makes the latter
fully faithful on `Dᵇc`; since the hom-complex double dual satisfies the triangle identity, it is
then invertible (`DerivedCategory.quasiIso_bifunctorHomBidual_of_bijective`). The evaluation and
the braidings of the two models are never compared. -/
theorem quasiIso_bifunctorHomBidual_ordinary {M I : CochainComplex (ProEtale.AdicSheaf l Z.left) ℤ}
    [I.IsKInjective]
    (eI : Nonempty ((ordinaryToCondensed Z).obj (DerivedCategory.Q.obj I) ≅
      (ObjectProperty.ι _).obj (ProEtale.CondensedRing.dualizingComplex l Z)))
    (hM : ProEtale.constantModelBoundedConstructible (Profinite.padicAlgClRingObj l) Z.left
      ((ordinaryToCondensed Z).obj (DerivedCategory.Q.obj M))) :
    QuasiIso (CochainComplex.bifunctorHomBidual (ordinaryBifunctorEvaluation l Z.left) M I) := by
  classical
  obtain ⟨eI⟩ := eI
  obtain ⟨c⟩ := ProEtale.nativeScalarForgetting_monoidal l Z.left
  let : (ProEtale.AdicSheaf.forgetAb l Z.left).Monoidal := c
  have : (ProEtale.AdicSheaf.forgetAb l Z.left).IsEquivalence :=
    ProEtale.nativeScalarForgetting_isEquivalence l Z.left
  have : (Mod.comap (ProEtale.nativeModuleCoefficientIso l Z.left).hom).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso
      (ProEtale.nativeModuleCoefficientIso l Z.left).hom).isEquivalence_functor
  let U := ProEtale.AdicSheaf.forgetAb l Z.left ⋙
    Mod.comap (ProEtale.nativeModuleCoefficientIso l Z.left).hom
  let : U.Monoidal := inferInstanceAs (_ ⋙ _).Monoidal
  have : U.IsEquivalence := inferInstance
  let φ := CochainComplex.BifunctorMapIso.ofMonoidal (H := ordinaryIhomBifunctor l Z.left) U
    (fun a ↦ Mod.ihomIsoIhom a) (fun f ↦ Mod.ihomMap_comp_ihomIsoIhom_hom f)
  -- the bounded constructible complexes, on which the condensed Verdier dual is fully faithful
  let P := ProEtale.boundedConstructible
    (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj l) Z.left)
  let W := DerivedCategory.Q.obj ((U.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
  let eW : W ≅ (ObjectProperty.ι _).obj (ProEtale.CondensedRing.dualizingComplex l Z) :=
    (U.mapDerivedCategoryFactors.app I).symm ≪≫ eI
  have hP (X : DerivedCategory _) (hX : P X) : P ((CategoryTheory.ihom X).obj W) :=
    ObjectProperty.prop_ihom P hX (P.prop_of_iso eW.symm
      (ProEtale.CondensedRing.dualizingComplex l Z).property)
  have hbij (X X' : DerivedCategory _) (hX : P X) (hX' : P X') :
      Function.Bijective (fun f : X ⟶ X' ↦ (MonoidalClosed.pre f).app W) := by
    have : IsIso (MonoidalClosed.toIhomIhom (ProEtale.CondensedRing.dualizingComplex l Z)
        (⟨X', hX'⟩ : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj l⟧)) :=
      ProEtale.CondensedRing.isIso_verdierBiduality l _
    exact MonoidalClosed.bijective_pre_app_of_iso_right eW.symm X X'
      (ObjectProperty.bijective_pre_app_of_isIso P _ hX hX')
  have : LocallyOfFiniteType (Z.left ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType Z.hom)
  have : QuasiCompact (Z.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact Z.hom)
  have : IsSeparated (Z.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated Z.hom)
  have hEq := (ProEtale.finiteCoefficientDescentTwoColimit k (ringChar k) l
    (Fact.out : (ringChar k).Prime).pos (Fact.out : ringChar k ≠ l) Z.left).2.2.2.2.1.1
  have := ProEtale.CondensedRing.isLeftDerivabilityStructure_localizerMorphismKFlat
    (Profinite.padicAlgClRingObj l) Z.left
  exact DerivedCategory.quasiIso_bifunctorHomBidual_of_bijective φ I
    (ordinaryBifunctorEvaluation l Z.left) (fun a b ↦ Mod.bidual_comp_ihomMap_bidual a b) P hP
    hbij M (by rw [hEq] at hM; exact hM)

end AlgebraicGeometry.ProEtaleWeilSheaf
