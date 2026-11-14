/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitQuotient
import WeilConjectures.AlgebraicGeometry.Square.SquareZeroTensorPowerBoundary

/-! # The obstruction-and-lifting conjunct

Source: Stacks Project, Cohomology of Schemes, Lemma 09MS.
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
universe u

private theorem nsmul_addHom_zero {A B : Type*} [AddZeroClass A] [AddMonoid B]
    (b : A →+ B) (k : ℕ) : k • b 0 = 0 := by
  rw [b.map_zero, nsmul_zero]

/-- Core obstruction and lifting criterion, omitting quasi-coherence.

Source: Stacks Project, Cohomology of Schemes, Lemma 09MS. -/
theorem square_zero_section_power_obstruction_core
    {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j]
    (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n : ℕ) (s : (((tensorPullback j).obj L).tensorPow n).val.presheaf.obj
      (Opposite.op ⊤)) :
    let F := (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n)
    ∃ (xi : (RingedSpace.moduleCohomology Z.toRingedSpace 1).obj F),
      ∀ e : ℕ, (RingedSpace.moduleCohomology Z.toRingedSpace 1).map
        ((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection
          (((tensorPullback j).obj L).tensorPow n) s) e) xi = 0 →
      ∃ t : (L.tensorPow (n * (e + 1))).val.presheaf.obj (Opposite.op ⊤),
        ∃ a : (tensorPullback j).obj (L.tensorPow (n * (e + 1))) ≅
            (((tensorPullback j).obj L).tensorPow n).tensorPow (e + 1),
          homOfGlobalSection ((tensorPullback j).obj (L.tensorPow (n * (e + 1))))
              (((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
                (L.tensorPow (n * (e + 1)))).val.app (Opposite.op ⊤) t) ≫ a.hom =
            tensorPowSection (homOfGlobalSection
              (((tensorPullback j).obj L).tensorPow n) s) (e + 1) := by
  classical
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let := HasDerivedCategory.standard
    (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (Opposite.op ⊤)))
  have hη (d : ℕ) : Epi ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
      (L.tensorPow d)) := by
    obtain ⟨_, h, _⟩ := closedImmersion_unit_quotient j
    let adj := Classical.choice (nonempty_tensorPullbackAdjunction j)
    have : Epi (adj.unit.app (L.tensorPow d)) := (h (L.tensorPow d)).1
    let adj' := Classical.choose (exists_tensorPullbackAdjunction j)
    change Epi (adj'.unit.app (L.tensorPow d))
    rw [← Adjunction.unit_leftAdjointUniq_hom_app adj adj' (L.tensorPow d)]
    infer_instance
  have hshort (d : ℕ) :
      (CategoryTheory.ShortComplex.kernelSequence
        ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
          (L.tensorPow d))).ShortExact :=
    CategoryTheory.ShortComplex.ShortExact.mk'
      (CategoryTheory.ShortComplex.kernelSequence_exact _) inferInstance (hη d)
  obtain ⟨xi, hxi⟩ := square_zero_tensor_power_boundary j L hI n s hshort
  refine ⟨xi, ?_⟩
  intro e he
  obtain ⟨a, b, hb⟩ := hxi e
  have hz := congrArg (fun x ↦ (e + 1) • b x) he
  have hz' := nsmul_addHom_zero b (e + 1)
  have hb0 := hb.trans (hz.trans hz')
  obtain ⟨t, ht⟩ := (RingedSpace.moduleSectionBoundary_eq_zero_iff X.toRingedSpace
    (CategoryTheory.ShortComplex.kernelSequence
      ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
        (L.tensorPow (n * (e + 1)))))
    (hshort (n * (e + 1))) _).mp hb0
  refine ⟨t, a, ?_⟩
  let q := tensorPowSection (homOfGlobalSection
    (((tensorPullback j).obj L).tensorPow n) s) (e + 1) ≫ a.inv
  have hq : homOfGlobalSection _ (q.app ⊤ (1 : Γ(Z, ⊤))) = q := by
    apply (SheafOfModules.unitHomEquiv _).injective
    apply Subtype.ext
    funext U
    change (homOfGlobalSection _ _).app U.unop (1 : Γ(Z, U.unop)) =
      q.app U.unop (1 : Γ(Z, U.unop))
    rw [homOfGlobalSection_app_one, ← Hom.app_presheaf_map]
    exact congrArg (q.app U.unop)
      (map_one (Z.presheaf.map (homOfLE
        (le_top : U.unop ≤ ⊤)).op).hom :)
  change ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
    (L.tensorPow (n * (e + 1)))).val.app (Opposite.op ⊤) t =
      q.app ⊤ (1 : Γ(Z, ⊤)) at ht
  rw [ht, hq]
  simp only [q, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.Scheme.Modules
