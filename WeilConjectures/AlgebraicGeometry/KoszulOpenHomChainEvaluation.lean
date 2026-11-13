/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulOpenHomChainRepresentatives
import WeilConjectures.AlgebraicGeometry.KoszulOpenHomIdentityEvaluation
import WeilConjectures.AlgebraicGeometry.KoszulOpenHomChainClassNaturality
import WeilConjectures.AlgebraicGeometry.AffinePerfectKoszulPrincipalUnit
import WeilConjectures.AlgebraicGeometry.KoszulCechComparisonConstruction
import WeilConjectures.AlgebraicGeometry.KoszulOpenSystem

/-! # Evaluation at one and the chain-level Koszul restriction comparison

## References

* Stacks Project, Tags 08DC, 08DD, 08D1 and 09M1.
-/

@[expose] public section

universe u w v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
-- Derived restriction and nested homology functors require extra elaboration steps.
/-- Evaluation at one is natural and agrees with the fraction comparison on chain maps.
The statement concerns chain maps into `F`; it does not identify arbitrary stage derived
maps with Hom-complex homology. -/
theorem koszulOpenHom_chain_evaluation
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))]
    [HasDerivedCategory.{v} (ModuleCat.{u} A)] :
    let R := ((SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) (koszulOpen A r f)) ⋙
      Equivalence.functor
        (C := SheafOfModules.{u}
          ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
        (D := SheafOfModules.{u}
          (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
    let G := (affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor
    ∃ b : ∀ E : schemeDerivedCategory (Spec (.of A)),
      (R.obj (koszulOpenStructure A) ⟶ R.obj E) ≃ H.obj (G.obj E),
      (∀ (E E' : schemeDerivedCategory (Spec (.of A))) (g : E ⟶ E')
        (ψ : R.obj (koszulOpenStructure A) ⟶ R.obj E),
        b E' (ψ ≫ R.map g) = H.map (G.map g) (b E ψ)) ∧
      ∀ (F : CochainComplex
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
        (_hF : ∀ n : ℤ, (F.X n).IsQuasicoherent)
        (e : ℕ) (t : koszulOpenSheafComplex A r f e ⟶ F)
        (ψ : R.obj (koszulOpenStructure A) ⟶ R.obj (DerivedCategory.Q.obj F)),
        R.map (koszulOpenUnit A r f e) ≫ ψ = R.map (DerivedCategory.Q.map t) →
        b (DerivedCategory.Q.obj F) ψ =
          H.map (koszulCechDerivedComparison A r f F)
            (H.map (DerivedCategory.Q.map (colimit.ι
              (koszulCechHomDiagram A r f
                (((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj F)) e))
                  (koszulOpenHomStageClass A r f F e t)) := by
  classical
  dsimp only
  let F₀ := SheafOfModules.overFunctor.{u}
    (moduleRings (Spec (.of A)).toRingedSpace) (koszulOpen A r f)
  let G₀ := Equivalence.functor
    (C := SheafOfModules.{u}
      ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
    (D := SheafOfModules.{u}
      (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
    (Scheme.Modules.overEquiv (koszulOpen A r f))
  let R := (F₀ ⋙ G₀).mapDerivedCategory
  obtain ⟨b, hb, hid⟩ := koszulOpenHom_identity_evaluation.{u, w, v} A r f
  refine ⟨b, hb, ?_⟩
  intro F _hF e t ψ hψ
  have hi : IsIso (F₀.mapDerivedCategory.map (koszulOpenUnit A r f e)) := by
    have h := (affine_perfect_koszul_principal_unit A r f (e + 1)
      (Nat.le_add_left 1 e)).2
    have hU : (⨆ i : Fin r, (Spec (.of A)).basicOpen
        ((Scheme.ΓSpecIso (.of A)).inv (f i))) = koszulOpen A r f := by
      unfold koszulOpen
      congr 1
      funext i
      exact basicOpen_eq_of_affine (R := .of A) (f i)
    rw [hU] at h
    exact h
  have hiso : IsIso (R.map (koszulOpenUnit A r f e)) := by
    apply (NatIso.isIso_map_iff (Functor.mapDerivedCategoryCompIso F₀ G₀) _).1
    change IsIso (G₀.mapDerivedCategory.map
      (F₀.mapDerivedCategory.map (koszulOpenUnit A r f e)))
    infer_instance
  let v := inv (R.map (koszulOpenUnit A r f e))
  have hv : R.map (koszulOpenUnit A r f e) ≫ v = 𝟙 _ := IsIso.hom_inv_id _
  have hfac : ψ = v ≫ R.map (DerivedCategory.Q.map t) := by
    rw [← hψ, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rw [hfac, hb, hid e v hv]
  have hn := koszulOpenHom_chain_class_naturality.{u, w, v} A r f
    (koszulOpenSheafComplex A r f e) F e (𝟙 _) t
  rw [Category.id_comp] at hn
  convert hn using 1

end AlgebraicGeometry
