/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.Modules.Dual

import WeilConjectures.AlgebraicGeometry.SelfTorConormalDualChart
import WeilConjectures.AlgebraicGeometry.SelfExtTorDualChart

/-! # Naturality of the regular affine Koszul comparisons

## References

* Stacks Project, Tags 0BQY and 062I.
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Restriction preserves composition, hence invertibility of both factors. -/
private theorem over_comp_isIso {X : Scheme.{u}} {M N P : X.Modules}
    (f : M ⟶ N) (g : N ⟶ P) (W : X.Opens)
    [IsIso (f.over W)] [IsIso (g.over W)] : IsIso ((f ≫ g).over W) := by
  change IsIso (f.over W ≫ g.over W)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Inverses of restrictions of one morphism agree on every common subopen. -/
private theorem compatible_inverse_family
    {X : Scheme.{u}} {F T : X.Modules} {I : Type*}
    (W : I → X.Opens) (φ : T ⟶ F) (hφ : ∀ j, IsIso (φ.over (W j))) :
    ∃ c : ∀ j, F.over (W j) ≅ T.over (W j),
      ∀ (j k : I) (A : X.Opens) (hj : A ≤ W j) (hk : A ≤ W k),
        (c j).hom.val.app (op (Over.mk (homOfLE hj))) =
          (c k).hom.val.app (op (Over.mk (homOfLE hk))) := by
  let c := fun j ↦ (@asIso _ _ _ _ (φ.over (W j)) (hφ j)).symm
  refine ⟨c, ?_⟩
  intro j k A hj hk
  let gj : F.val.obj (op A) ⟶ T.val.obj (op A) :=
    (c j).hom.val.app (op (Over.mk (homOfLE hj)))
  let gk : F.val.obj (op A) ⟶ T.val.obj (op A) :=
    (c k).hom.val.app (op (Over.mk (homOfLE hk)))
  let f := φ.val.app (op A)
  have hjf : gj ≫ f = 𝟙 (F.val.obj (op A)) :=
    congrArg (fun t ↦ t.val.app (op (Over.mk (homOfLE hj)))) (c j).hom_inv_id
  have hfk : f ≫ gk = 𝟙 (T.val.obj (op A)) :=
    congrArg (fun t ↦ t.val.app (op (Over.mk (homOfLE hk)))) (c k).inv_hom_id
  change gj = gk
  calc
    gj = gj ≫ (f ≫ gk) := by rw [hfk, Category.comp_id]
    _ = gk := by rw [← Category.assoc, hjf, Category.id_comp]

/-- The normalized chart comparisons respect inclusions of regular affine charts
(Stacks, Tags 0BQY, 062I). -/
theorem koszulRegularImmersion_self_ext_conormal_nested_charts
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (V : Z.Opens) (n : ℕ) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    let G := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (n : ℤ)).obj
        (H.obj (op (S.obj B), S.obj B))
    let T := (Scheme.Modules.restrictFunctor V.ι).obj
      ((Scheme.Modules.tensorPullback i).obj G)
    let F := (Scheme.Modules.restrictFunctor V.ι).obj
      (Scheme.Modules.dual (Scheme.Modules.exteriorPower
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules) n))
    ∃ c : ∀ (U : Y.affineOpens)
      (_hU : ∃ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f),
        F.over (V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1)) ≅ T.over (V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1)),
      ∀ (U₀ U₁ : Y.affineOpens)
        (h₀ : ∃ (m : ℕ) (f : Fin m → Γ(Y, U₀.1)),
          Ideal.span (Set.range f) = i.ker.ideal U₀ ∧
            RingTheory.Sequence.IsKoszulRegular f)
        (h₁ : ∃ (m : ℕ) (f : Fin m → Γ(Y, U₁.1)),
          Ideal.span (Set.range f) = i.ker.ideal U₁ ∧
            RingTheory.Sequence.IsKoszulRegular f)
        (_h : U₀.1 ≤ U₁.1) (A : V.toScheme.Opens)
        (hA₀ : A ≤ V.ι ⁻¹ᵁ (i ⁻¹ᵁ U₀.1))
        (hA₁ : A ≤ V.ι ⁻¹ᵁ (i ⁻¹ᵁ U₁.1)),
        (c U₀ h₀).hom.val.app (op (Over.mk (homOfLE hA₀))) =
          (c U₁ h₁).hom.val.app (op (Over.mk (homOfLE hA₁))) := by
  classical
  intro B S H G T F
  obtain ⟨τ, hκ⟩ := selfTor_conormal_dual_chart.{u, w} i n
  let κ := Scheme.Modules.dualMap τ
  obtain ⟨ε, hε⟩ := selfExt_tor_dual_chart.{u, w} i n
  let R := Scheme.Modules.restrictFunctor V.ι
  let φ : T ⟶ F := R.map ε ≫ R.map κ
  have hφ (U : Y.affineOpens)
      (hU : ∃ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f) :
      IsIso (φ.over (V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1))) := by
    have := hκ V U hU
    have := hε V U hU
    exact over_comp_isIso (R.map ε) (R.map κ) _
  let I := {U : Y.affineOpens // ∃ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
    Ideal.span (Set.range f) = i.ker.ideal U ∧ RingTheory.Sequence.IsKoszulRegular f}
  obtain ⟨d, hd⟩ := compatible_inverse_family
    (fun U : I ↦ V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.val.1)) φ (fun U ↦ hφ U.val U.property)
  refine ⟨fun U hU ↦ d ⟨U, hU⟩, ?_⟩
  intro U₀ U₁ h₀ h₁ _h A hA₀ hA₁
  exact hd ⟨U₀, h₀⟩ ⟨U₁, h₁⟩ A hA₀ hA₁

end AlgebraicGeometry
