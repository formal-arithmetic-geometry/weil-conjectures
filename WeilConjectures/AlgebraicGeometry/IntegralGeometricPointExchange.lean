/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.BaseChange.Square
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.IntegralGeometricFibreSections
import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Integral exchange over a geometric point

## References

* Stacks Project, Tag 0EYP, specialized to a geometric point.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Integral exchange for base change to the spectrum of an algebraically closed field.
(Stacks, Tag 0EYP) -/
theorem isIso_baseChangeMap_app_of_isIntegralHom_geometricPoint
    (Λ : Type (u + 1)) [CommRing Λ] {X' X Y : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : IsPullback g' f' f s) [IsIntegralHom f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F)  := by
  obtain ⟨Θ, hΘ, hGerms⟩ := integralGeometricFibreSections Λ sq F
  let : IsIso Θ := hΘ
  obtain ⟨b, hb⟩ := geometricFibreExchange_germs Λ sq F Θ hGerms
  let φ := (baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F
  let p := Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))
  have hφ : IsIso (p.sheafFiber.map φ) := by
    have hcomp : IsIso (p.sheafFiber.map φ ≫ b.hom) := by
      rw [hb]
      infer_instance
    exact (isIso_comp_right_iff _ b.hom).mp hcomp
  have hcover : (⋃ _ : PUnit.{u + 1}, Set.range (𝟙 (Spec (.of Ω)))) = Set.univ := by
    ext x
    simp
  have hc := Scheme.isConservativeFamilyOfPoints_ulift_pointSmallEtale_of_iUnion_range_eq_univ
    (Spec (.of Ω)) (Ω := fun _ : PUnit.{u + 1} ↦ Ω) (fun _ ↦ 𝟙 _) hcover
  apply ((hc.jointlyReflectIsomorphisms (ModuleCat.{u + 1} Λ)).isIso_iff φ).2
  rintro ⟨_, ⟨i⟩⟩
  rw [NatIso.isIso_map_iff ((Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).uliftSheafFiberIso
    (ModuleCat.{u + 1} Λ))]
  exact hφ

end AlgebraicGeometry.Etale
