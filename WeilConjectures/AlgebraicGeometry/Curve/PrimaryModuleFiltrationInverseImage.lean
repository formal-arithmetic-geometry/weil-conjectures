/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.PrimaryModuleFiltrationFixedFieldComparison
import WeilConjectures.AlgebraicGeometry.Curve.PrimaryModuleFiltrationBaseChange
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.FieldTheory.GaloisAutomorphismExtension

/-!
# Inverse image and restriction of the stalk representation

Source: Stacks Project, Tags 03QT, 03SF and 04JQ.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits ZeroObject Opposite
namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Tags 03QT, 03SF and 04JQ. -/
theorem primary_inverseImage_restriction
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (M : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (R : Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ (Gal(Ks/K)))
    (i : AddCommGrpCat.of R.obj.V ≅
      ((pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj M)
    (haction : ∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
      (_hτ : (algebraMap Ks Ω).comp g.toRingHom =
        τ.toRingHom.comp (algebraMap Ks Ω))
      (X : (Spec (.of K)).Etale)
      (x x' : (pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X)
      (_hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left)
      (z : M.obj.obj (op X)),
      i.hom (R.obj.ρ g (i.inv ((pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber X x M.obj z))) =
      (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber
        X x' M.obj z)
    (H : OpenSubgroup (Gal(Ks/K)))
    [FiniteDimensional K (IntermediateField.fixedField H.toSubgroup)]
    (C : PrimaryFixedFieldEquivalence K Ks H)
    (hC : PrimaryFixedFieldComparison K Ks H Ω C)
    (T : Scheme.{u}) (e : Spec (.of (IntermediateField.fixedField H.toSubgroup)) ≅ T) :
    Nonempty ((Etale.upperStar AddCommGrpCat.{u + 1}
      (e.inv ≫ Spec.map (CommRingCat.ofHom
        (algebraMap K (IntermediateField.fixedField H.toSubgroup))))).obj M ≅
      primaryAssociatedSheaf K Ks H Ω C T e (primaryRestrictedModule K Ks H R)) := by
  obtain ⟨hM⟩ := primary_fixedField_pullback_iso K Ks Ω M R i haction H C hC
  let f := e.inv
  let g := Spec.map (CommRingCat.ofHom
    (algebraMap K (IntermediateField.fixedField H.toSubgroup)))
  let fg := f ≫ g
  let hc := Etale.upperStarComp AddCommGrpCat.{u + 1} f g fg rfl
  exact ⟨(hc.app M) ≪≫ (Etale.upperStar AddCommGrpCat.{u + 1} f).mapIso hM⟩

end AlgebraicGeometry.Scheme
