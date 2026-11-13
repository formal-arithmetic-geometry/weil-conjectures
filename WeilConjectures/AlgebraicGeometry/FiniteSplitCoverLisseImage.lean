/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.PullbackFiniteLocallyConstant
import WeilConjectures.AlgebraicGeometry.DisjointUniversalHomeomorphismsLisseImage
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.SixFunctors.Finite.BaseChange
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteStalksComparison

/-!
# Lissity of a finite direct image on a splitting cover
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem isLisse_of_iso {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology (Type (u + 1))} (e : F ≅ G)
    (hF : IsLisseEtaleSheafOfSets F) : IsLisseEtaleSheafOfSets G := by
  obtain ⟨𝒰, h𝒰⟩ := hF.1
  refine ⟨⟨𝒰, fun i ↦ ?_⟩, ?_⟩
  · have := h𝒰 i
    exact Sheaf.isConstant_congr _
      ((X.smallEtaleTopology.overPullback (Type (u + 1))
        (𝒰.etalePrecoverageToEtale i)).mapIso e)
  · refine isFiniteSheaf_of_finite_algClosed_stalks _ fun Ω _ _ t ↦ ?_
    have := hF.finite_sheafFiber Ω t
    exact Finite.of_surjective
      (((pointSmallEtale t).sheafFiber.mapIso e).hom)
      (ConcreteCategory.bijective_of_isIso
        (((pointSmallEtale t).sheafFiber.mapIso e).hom)).2

private theorem finiteStalks_finite_directImage
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hE : IsLisseEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj E))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    Finite ((pointSmallEtale y).sheafFiber.obj
      ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.lowerStar AddCommGrpCat.{u + 1} f).obj E))) := by
  let forgetA := CategoryTheory.forget AddCommGrpCat.{u + 1}
  have : PreservesFilteredColimitsOfSize.{u, u} forgetA :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} forgetA
  let F := fun t : f.GeometricFiber y ↦ (pointSmallEtale t.1).sheafFiber.obj E
  have hfinite (t : f.GeometricFiber y) : Finite (forgetA.obj (F t)) := by
    have : Finite ((pointSmallEtale t.1).sheafFiber.obj
        ((sheafCompose X.smallEtaleTopology forgetA).obj E)) := hE.finite_sheafFiber Ω t.1
    let e : (pointSmallEtale t.1).sheafFiber.obj
        ((sheafCompose X.smallEtaleTopology forgetA).obj E) ≅ forgetA.obj (F t) :=
      ((pointSmallEtale t.1).sheafFiberCompIso forgetA).app E
    exact Finite.of_surjective e.hom (ConcreteCategory.bijective_of_isIso e.hom).2
  let := hfinite
  let e := ((pointSmallEtale y).sheafFiberCompIso forgetA).app
      ((Etale.lowerStar AddCommGrpCat.{u + 1} f).obj E) ≪≫
    forgetA.mapIso (Etale.stalkIsoPi AddCommGrpCat.{u + 1} f y E) ≪≫
    PreservesProduct.iso forgetA F ≪≫ Types.productIso.{u, u + 1} (fun t ↦ forgetA.obj (F t))
  exact Finite.of_equiv _ e.toEquiv.symm

/-- On an étale cover where a finite source is a disjoint union of universal
homeomorphisms, the direct image of a lisse restriction is lisse on the cover.
This is the sheaf-theoretic part of generic lisse preservation; it makes no
integrality, Noetherian, or generic-open assumption on the base. -/
theorem isLisse_pullback_finite_directImage_of_split_cover
    {S Z : Scheme.{u}} (g : Z ⟶ S) [IsFinite g] (V : S.Opens)
    {T : Scheme.{u}} (p : T ⟶ V.toScheme) [Etale p]
    (n : ℕ) (W : Fin n → (pullback g (p ≫ V.ι)).Opens)
    (hcover : (⨆ i, W i) = ⊤)
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (W i) (W j)))
    (hW : ∀ i, IsUniversalHomeomorphism
      ((W i).ι ≫ pullback.snd g (p ≫ V.ι)))
    (E : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hE : IsLisseEtaleSheafOfSets
      ((sheafCompose (g ⁻¹ᵁ V).toScheme.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.upperStar AddCommGrpCat.{u + 1} (g ⁻¹ᵁ V).ι).obj E))) :
    IsLisseEtaleSheafOfSets
      ((etaleSetPullback p).obj
        ((etaleSetPullback V.ι).obj
          ((sheafCompose S.smallEtaleTopology
            (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
              ((Etale.lowerStar AddCommGrpCat.{u + 1} g).obj E)))) := by
  let q := p ≫ V.ι
  let a := pullback.fst g q
  let b := pullback.snd g q
  have hrange : Set.range a ⊆ Set.range (g ⁻¹ᵁ V).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change g (a x) ∈ V
    have h := congrArg (fun m ↦ m x) (pullback.condition (f := g) (g := q))
    change g (a x) = q (b x) at h
    rw [h]
    exact (p (b x)).property
  let r := IsOpenImmersion.lift (g ⁻¹ᵁ V).ι a hrange
  have hr : r ≫ (g ⁻¹ᵁ V).ι = a := IsOpenImmersion.lift_fac _ _ _
  have hA := (pullback_finite_locally_constant r (g ⁻¹ᵁ V).ι E hE).2
  rw [hr] at hA
  have hlocal := isLocallyConstant_finite_disjoint_universalHomeomorphism_directImage
    b n W hcover hdisjoint hW ((Etale.upperStar AddCommGrpCat.{u + 1} a).obj E) hA
  have hB : IsLisseEtaleSheafOfSets
      ((sheafCompose T.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.lowerStar AddCommGrpCat.{u + 1} b).obj
            ((Etale.upperStar AddCommGrpCat.{u + 1} a).obj E))) :=
    ⟨hlocal, isFiniteSheaf_of_finite_algClosed_stalks _ fun Ω _ _ y ↦
      finiteStalks_finite_directImage b
      ((Etale.upperStar AddCommGrpCat.{u + 1} a).obj E) hA Ω y⟩
  obtain ⟨eV, _, _, _, _, _, _⟩ :=
    (AlgebraicGeometry.etaleInverseImageAlgebraicStructures V.toScheme S V.ι).2
  obtain ⟨ep, _, _, _, _, _, _⟩ :=
    (AlgebraicGeometry.etaleInverseImageAlgebraicStructures T V.toScheme p).2
  let F := (Etale.lowerStar AddCommGrpCat.{u + 1} g).obj E
  let forgetT := sheafCompose T.smallEtaleTopology
    (CategoryTheory.forget AddCommGrpCat.{u + 1})
  have := AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isFinite
    AddCommGrpCat.{u + 1} (IsPullback.of_hasPullback g q)
  let e := (etaleSetPullback p).mapIso (eV.app F).symm ≪≫
    (ep.app ((Etale.upperStar AddCommGrpCat.{u + 1} V.ι).obj F)).symm ≪≫
    forgetT.mapIso ((Etale.upperStarComp AddCommGrpCat.{u + 1} p V.ι).app F).symm ≪≫
    forgetT.mapIso (asIso ((Etale.baseChangeMap AddCommGrpCat.{u + 1}
      (IsPullback.of_hasPullback g q).toCommSq).app E))
  exact isLisse_of_iso e.symm hB

end AlgebraicGeometry.Scheme
