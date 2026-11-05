/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
import WeilConjectures.AlgebraicGeometry.FlatComplexDerivedPullback
import WeilConjectures.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Computing derived pullback on a local strictly perfect model

Source: Stacks Project, Tags 09UA, 08DW and 06YJ.
(blueprint: lem-pc-localized-pullback-perfect-model).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Ordinary pullback between the localized module sites, constructed by transporting
scheme-module pullback across the open-site equivalences.
Source: Stacks Project, Tags 0095 and 08DW
(blueprint: lem-pc-localized-pullback-perfect-model). -/
noncomputable def Scheme.Modules.localizedPullback {T X : Scheme.{u}} (g : T ⟶ X)
    (U : X.Opens) :
    SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ⥤
      SheafOfModules.{u} ((moduleRings T.toRingedSpace).over (g ⁻¹ᵁ U)) :=
  (Scheme.Modules.overEquiv U).functor ⋙
    Scheme.Modules.pullback (g.resLE U (g ⁻¹ᵁ U) le_rfl) ⋙
      (Scheme.Modules.overEquiv (g ⁻¹ᵁ U)).inverse

instance {T X : Scheme.{u}} (g : T ⟶ X) (U : X.Opens) :
    (Scheme.Modules.localizedPullback g U).Additive := by
  have : (Scheme.Modules.overEquiv U).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (Scheme.Modules.overEquiv (g ⁻¹ᵁ U)).inverse.Additive :=
    Functor.additive_of_preserves_binary_products _
  unfold Scheme.Modules.localizedPullback
  infer_instance

/-- A finite-free retract is flat by flatness of coproducts and retracts. -/
private theorem flat_retract (Y : Scheme.{u})
    (M : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (m : ℕ)
    (i : M ⟶ SheafOfModules.free (R := moduleRings Y.toRingedSpace) (ULift.{u} (Fin m)))
    (r : SheafOfModules.free (R := moduleRings Y.toRingedSpace) (ULift.{u} (Fin m)) ⟶ M)
    (h : i ≫ r = 𝟙 M) : SheafOfModules.IsFlat M := by
  let := SheafOfModules.monoidalCategory Y.sheaf
  let := SheafOfModules.symmetricCategory Y.sheaf
  obtain ⟨⟨mp⟩, ⟨mc⟩, _⟩ := SheafOfModules.tensorClosed Y.sheaf
  let := mp
  let := mc
  have := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  have hf : ObjectProperty.flat
      (SheafOfModules.free (R := moduleRings Y.toRingedSpace) (ULift.{u} (Fin m))) :=
    ObjectProperty.flat_coproduct _ (fun _ ↦ ObjectProperty.prop_unit _)
  exact (ObjectProperty.flat_of_retract ⟨i, r, h⟩ hf).2

/-- Identify the tensor pullback and module pullback by uniqueness of left adjoints. -/
private theorem ordinaryPullback_Q_iso {T X : Scheme.{u}} (g : T ⟶ X)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hb : ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (P.X n))
    (hf : ∀ n : ℤ, SheafOfModules.IsFlat (P.X n)) :
    Nonempty ((derivedPullback g).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        (((Scheme.Modules.pullback g).mapHomologicalComplex (.up ℤ)).obj P)) := by
  obtain ⟨F, hF, hm, ha, ε, hd, e, he⟩ := flatComplexDerivedPullback g P hb hf
  have hEq : F = Scheme.Modules.tensorPullback g :=
    CategoryTheory.Functor.ext hF (fun _ _ a ↦ hm a)
  subst F
  have : (Scheme.Modules.tensorPullback g).Additive := ha
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction g
  let η := adj.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction g)
  exact ⟨(derivedPullback g).mapIso ((DerivedCategory.quotientCompQhIso _).app P).symm ≪≫
    e.symm ≪≫
    DerivedCategory.Qh.mapIso
      (((Scheme.Modules.tensorPullback g).mapHomotopyCategoryFactors (.up ℤ)).app P) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _ ≪≫
    DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex η (.up ℤ)).app P)⟩


end AlgebraicGeometry
