module

public import Sheaf.AlgebraicGeometry.KoszulOpenSystem
import Sheaf.Paper.AffinePerfectKoszulPrincipalUnit
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.AlgebraicGeometry.AffinePerfectOpenRepresentCohomologyCore
import Sheaf.AlgebraicGeometry.KoszulOpenHomRestrictionSurjective
import Sheaf.AlgebraicGeometry.KoszulOpenHomRestrictionEventuallyZero
import Mathlib.CategoryTheory.Limits.Types.Filtered

@[expose] public section
universe uMain wMain
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option maxHeartbeats 1000000 in
-- Repeated derived restriction expressions require more elaboration steps.
set_option backward.isDefEq.respectTransparency false in
/-- Intermediate representability and colimit assertion; source Tags 08DC and 08DD.
(blueprint: lem-sc-affine-perfect-open-represent-cohomology-colimit) -/
theorem affine_perfect_open_represent_cohomology_colimit
    (A : Type uMain) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} ((moduleRings (Spec (.of A)).toRingedSpace).over V))]
    [HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))]
    (E : schemeDerivedQCohCategory (Spec (.of A))) :
    ∃ v : ∀ e : ℕ,
      ((SheafOfModules.overFunctor.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)
                (koszulOpen A r f)) ⋙
              Equivalence.functor
                (C := SheafOfModules.{uMain}
                  ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
                (D := SheafOfModules.{uMain}
                  (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
                (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory.obj
        (koszulOpenStructure A) ⟶
      ((SheafOfModules.overFunctor.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)
                (koszulOpen A r f)) ⋙
              Equivalence.functor
                (C := SheafOfModules.{uMain}
                  ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
                (D := SheafOfModules.{uMain}
                  (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
                (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory.obj
        (koszulOpenObject A r f e),
      (∀ e : ℕ,
        ((SheafOfModules.overFunctor.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)
                  (koszulOpen A r f)) ⋙
                Equivalence.functor
                  (C := SheafOfModules.{uMain}
                    ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
                  (D := SheafOfModules.{uMain}
                    (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
                  (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory.map
          (koszulOpenUnit A r f e) ≫ v e = 𝟙 _) ∧
      (∀ e : ℕ, v e ≫
        ((SheafOfModules.overFunctor.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)
                  (koszulOpen A r f)) ⋙
                Equivalence.functor
                  (C := SheafOfModules.{uMain}
                    ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
                  (D := SheafOfModules.{uMain}
                    (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
                  (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory.map
          (koszulOpenUnit A r f e) = 𝟙 _) ∧
      ∃ ι : koszulOpenHomDiagram A r f E.1 ⟶
        (Functor.const ℕ).obj
          (((SheafOfModules.overFunctor.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)
                     (koszulOpen A r f)) ⋙
                   Equivalence.functor
                     (C := SheafOfModules.{uMain}
                       ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
                     (D := SheafOfModules.{uMain}
                       (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
                     (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory.obj
              (koszulOpenStructure A) ⟶
           ((SheafOfModules.overFunctor.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)
                     (koszulOpen A r f)) ⋙
                   Equivalence.functor
                     (C := SheafOfModules.{uMain}
                       ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
                     (D := SheafOfModules.{uMain}
                       (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
                     (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory.obj E.1),
        (∀ (e : ℕ) (φ : koszulOpenObject A r f e ⟶ E.1),
          ι.app e φ = v e ≫
            ((SheafOfModules.overFunctor.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)
                      (koszulOpen A r f)) ⋙
                    Equivalence.functor
                      (C := SheafOfModules.{uMain}
                        ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
                      (D := SheafOfModules.{uMain}
                        (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
                      (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory.map φ) ∧
        Nonempty (IsColimit (Cocone.mk _ ι)) := by
  classical
  let F := SheafOfModules.overFunctor.{uMain}
    (moduleRings (Spec (.of A)).toRingedSpace) (koszulOpen A r f)
  let G := Equivalence.functor
    (C := SheafOfModules.{uMain}
      ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
    (D := SheafOfModules.{uMain}
      (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
    (Scheme.Modules.overEquiv (koszulOpen A r f))
  have hi (e : ℕ) : IsIso (F.mapDerivedCategory.map (koszulOpenUnit A r f e)) := by
    have h := (affine_perfect_koszul_principal_unit A r f (e + 1)
      (Nat.le_add_left 1 e)).2
    have hU : (⨆ i : Fin r, (Spec (.of A)).basicOpen
        ((Scheme.ΓSpecIso (.of A)).inv (f i))) = koszulOpen A r f := by
      unfold koszulOpen
      congr 1
      funext i
      exact basicOpen_eq_of_affine (R := .of A) (f i)
    rw [hU] at h
    change IsIso (F.mapDerivedCategory.map (koszulOpenUnit A r f e)) at h
    exact h
  have hiso (e : ℕ) : IsIso ((F ⋙ G).mapDerivedCategory.map
      (koszulOpenUnit A r f e)) := by
    have := hi e
    apply (NatIso.isIso_map_iff (Functor.mapDerivedCategoryCompIso F G) _).2
    change IsIso (G.mapDerivedCategory.map
      (F.mapDerivedCategory.map (koszulOpenUnit A r f e)))
    infer_instance
  let v := fun e ↦ @inv _ _ _ _ ((F ⋙ G).mapDerivedCategory.map
    (koszulOpenUnit A r f e)) (hiso e)
  let R := (F ⋙ G).mapDerivedCategory
  have : R.Additive := by
    change (F ⋙ G).mapDerivedCategory.Additive
    infer_instance
  have hv₁ (e : ℕ) : R.map (koszulOpenUnit A r f e) ≫ v e = 𝟙 _ := by
    have := hiso e
    exact IsIso.hom_inv_id _
  have hv₂ (e : ℕ) : v e ≫ R.map (koszulOpenUnit A r f e) = 𝟙 _ := by
    have := hiso e
    exact IsIso.inv_hom_id _
  have hmap := (affine_perfect_open_represent_cohomology_core A r f E).2.2
  have hvmap (a b : ℕ) (h : a ≤ b) :
      v b ≫ R.map (koszulOpenMap A r f a b h) = v a := by
    calc
      v b ≫ R.map (koszulOpenMap A r f a b h) =
          v b ≫ R.map (koszulOpenMap A r f a b h) ≫
            R.map (koszulOpenUnit A r f a) ≫ v a := by
        rw [hv₁ a, Category.comp_id]
      _ = v b ≫ R.map (koszulOpenUnit A r f b) ≫ v a := by
        rw [← Category.assoc (R.map _) (R.map _) (v a), ← R.map_comp, hmap a b h]
      _ = v a := by rw [← Category.assoc, hv₂ b, Category.id_comp]
  let ι : koszulOpenHomDiagram A r f E.1 ⟶
      (Functor.const ℕ).obj (R.obj (koszulOpenStructure A) ⟶ R.obj E.1) :=
    { app := fun e ↦ TypeCat.ofHom (fun φ ↦ v e ≫ R.map φ)
      naturality := by
        intro a b h
        ext φ
        change v b ≫ R.map (koszulOpenMap A r f a b (leOfHom h) ≫ φ) =
          v a ≫ R.map φ
        rw [R.map_comp, ← Category.assoc, hvmap] }
  have hι (e : ℕ) (φ : koszulOpenObject A r f e ⟶ E.1) :
      ι.app e φ = v e ≫ R.map φ := rfl
  have hsurj := koszulOpenHom_restriction_surjective A r f E v hv₁ hv₂
  have hzero := koszulOpenHom_restriction_eventually_zero A r f E
  refine ⟨v, hv₁, hv₂, ι, hι, ⟨Types.FilteredColimit.isColimitOf' _ _ ?_ ?_⟩⟩
  · intro ψ
    obtain ⟨e, φ, hφ⟩ := hsurj ψ
    exact ⟨e, φ, (hι e φ).trans hφ |>.symm⟩
  · intro e φ ψ heq
    change (koszulOpenObject A r f e ⟶ E.1) at φ ψ
    have heq' := congrArg (fun k ↦ R.map (koszulOpenUnit A r f e) ≫ k) heq
    rw [hι, hι] at heq'
    simp only [← Category.assoc, hv₁ e, Category.id_comp] at heq'
    have hz : R.map (φ - ψ) = 0 := by
      rw [Functor.map_sub, heq', sub_self]
    obtain ⟨b, h, hb⟩ := hzero e (φ - ψ) hz
    refine ⟨b, homOfLE h, ?_⟩
    change koszulOpenMap A r f e b h ≫ φ = koszulOpenMap A r f e b h ≫ ψ
    simpa only [Preadditive.comp_sub, sub_eq_zero] using hb

end AlgebraicGeometry
