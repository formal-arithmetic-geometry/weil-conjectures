/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFreeCompactSupport.FiniteFreeCompactSupportData
import WeilConjectures.AlgebraicGeometry.FiniteFreeCompactSupport.FiniteFreeCompactSupportData
import WeilConjectures.AlgebraicGeometry.Proper.ProperFiniteCoefficientExtension

/-! # Finite-free compact-support composition

The canonical constructions are re-exported unchanged from the data module.
Source: blueprint sk-thm-purity-transport, Steps 1 and 3
(blueprint: lem-pur-finite-free-compact-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
open AlgebraicGeometry
open WeilConjectures.FiniteFreeCoefficients
open AlgebraicGeometry.FiniteCoefficientAdjoints
namespace AlgebraicGeometry.FiniteFreeCompactSupport

private theorem coefficientMap_naturality (pro : Bool)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {K K' : Sites.D pro A X} (v : K ⟶ K') :
    (Sites.scalar pro φ Y).map ((support pro A c).map v) ≫
        coefficientMap pro φ c K' =
      coefficientMap pro φ c K ≫
        (support pro B c).map ((Sites.scalar pro φ X).map v) := by
  cases pro
  · let J := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
    let R := (Etale.lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor
    change (Etale.scalarExtension φ Y).map
        ((Etale.lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.map (J.map v)) ≫
        (Etale.scalarMate φ c.g).app (J.obj K') ≫
          R.map ((Etale.ExceptionalCoefficients.openIso φ c.i).hom.app K') =
      ((Etale.scalarMate φ c.g).app (J.obj K) ≫
        R.map ((Etale.ExceptionalCoefficients.openIso φ c.i).hom.app K)) ≫
          R.map ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} B)
            c.i).mapDerivedCategory.map ((Etale.scalarExtension φ X).map v))
    have hp := (Etale.scalarMate φ c.g).naturality (J.map v)
    dsimp only [Functor.comp_map] at hp
    rw [← Category.assoc, hp]
    simp only [Category.assoc]
    rw [← R.map_comp, ← R.map_comp]
    congr 1
    have hj := (Etale.ExceptionalCoefficients.openIso φ c.i).hom.naturality v
    dsimp only [Functor.comp_map] at hj
    exact congrArg R.map hj
  · let aX := Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ)
    let aY := Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ)
    let F := ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
    let G := ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c
    let ρ := ProEtale.compactSupportRestrictionIso φ c
    change (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ).leftAdjoint.map
        (F.map v) ≫ (aY.homEquiv _ _).symm
          (F.map (aX.unit.app K') ≫ ρ.hom.app
            ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).leftAdjoint.obj K')) =
      (aY.homEquiv _ _).symm (F.map (aX.unit.app K) ≫ ρ.hom.app
        ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).leftAdjoint.obj K)) ≫
          G.map ((Sheaf.derivedRestrictScalars
            (Scheme.ProEt.topology X) φ).leftAdjoint.map v)
    apply (aY.homEquiv _ _).injective
    rw [aY.homEquiv_naturality_left, aY.homEquiv_naturality_right]
    simp only [Functor.id_obj, Equiv.apply_symm_apply]
    have hu := aX.unit.naturality v
    have hr := ρ.hom.naturality
      ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).leftAdjoint.map v)
    dsimp only [Functor.id_map, Functor.comp_map] at hu hr
    change F.map v ≫ F.map (aX.unit.app K') ≫ _ = _
    rw [← Category.assoc, ← F.map_comp, hu, F.map_comp]
    simp only [Category.assoc]
    exact congrArg (fun w ↦ F.map (aX.unit.app K) ≫ w) hr

private theorem origin (pro : Bool) (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) (K : Sites.D pro A X) (hK : Sites.Ctf pro A X K) :
    ∃ L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)),
      Nonempty ((realization pro A X).obj L.obj ≅ K) := by
  cases pro
  · obtain ⟨a, b, _, hz⟩ := hK.1.2
    have hb : _root_.DerivedCategory.TStructure.t.plus K :=
      ⟨a, (_root_.DerivedCategory.isGE_iff _ a).mpr fun q hq ↦ hz q (Or.inl hq)⟩
    exact ⟨⟨K, hb⟩, ⟨Iso.refl _⟩⟩
  · obtain ⟨L, hL, e⟩ := hK.plusEtaleOrigin
    exact ⟨⟨L, hL⟩, e⟩

end AlgebraicGeometry.FiniteFreeCompactSupport
