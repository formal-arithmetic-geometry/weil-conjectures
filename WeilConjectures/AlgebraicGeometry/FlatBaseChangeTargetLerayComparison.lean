/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtPullbackComparison
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeModuleLerayComparison

/-! # Target Leray comparison normalized against a natural source comparison

## References

* Stacks Project, Tags 01XK, 01E4, 03FD and 02KH
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives

private theorem equiv_transport_commutative_square
    {A B C D : Type*} (e : A ≃ B) {a : A → C} {k : B → C}
    {b : C → D} {r : A → D}
    (hk : ∀ x, a x = k (e x)) (hb : ∀ x, b (a x) = r x) :
    ∀ y, b (k y) = r (e.symm y) := by
  intro y
  exact (congrArg b ((hk (e.symm y)).trans
    (congrArg k (e.apply_symm_apply y)))).symm.trans (hb (e.symm y))

/-- Choose the natural source module/Ext comparison together with the target affine
Leray equivalence, compatibly with the cohomological pullback. This does not construct
or assume a source tensor comparison, nor assert invertibility of base change
(Stacks, Tags 03FD, 01XK, 01E4 and 02KH). -/
theorem exists_flatBaseChange_target_leray_comparison
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent]
    (I : InjectiveResolution F)
    (J : InjectiveResolution
      ((Scheme.Modules.tensorPullback (pullback.snd g f)).obj F))
    (p : ℕ) (V : S.Opens) (W : S'.Opens) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (eVW : W ≤ g ⁻¹ᵁ V)
    (D : Scheme.Modules.FlatBaseChangeOpenChoices f g F I J V) :
    letI : Algebra Γ(S, V) Γ(S', W) := (g.appLE V W eVW).hom.toAlgebra
    let h := f.resLE V (f ⁻¹ᵁ V) le_rfl ≫ V.toSpecΓ
    let N := (Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj F
    let Q := ((Scheme.Modules.pushforward (pullback.fst g f)).rightDerived p).obj
      ((Scheme.Modules.tensorPullback (pullback.snd g f)).obj F)
    ∃ E : ∀ M : (f ⁻¹ᵁ V).toScheme.Modules,
        ((RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj M) ≃+
          H M p,
      (∀ (M M' : (f ⁻¹ᵁ V).toScheme.Modules) (φ : M ⟶ M')
        (x : (RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj M),
        E M' (((RingedSpace.moduleCohomology
          (f ⁻¹ᵁ V).toScheme.toRingedSpace p).map φ).hom x) = H.map φ p (E M x)) ∧
      (∃ e0 : ((RingedSpace.moduleCohomology
            (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj
            ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F)) ≃+ HOver h N p,
         e0 = (E ((restrictFunctor (f ⁻¹ᵁ V).ι).obj F)).trans
            (H.mapLinearEquiv ((restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app F) p).toAddEquiv ∧
       ∃ b : HOver (baseChangeSnd (S := Γ(S', W)) h)
           (baseChangedModule (S := Γ(S', W)) h N) p ≃ₗ[Γ(S', W)] Γ(Q, W),
         ∀ xi : HOver h N p,
           b (H.baseChangeLinear (S := Γ(S', W)) h N p xi) =
             Q.presheaf.map (homOfLE eVW).op
               (D.targetClass p
                 (moduleCohomologyFMap ((pullback.snd g f).resLE (f ⁻¹ᵁ V)
                   ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl) D.psi p (e0.symm xi)))) := by
  classical
  let : Algebra Γ(S, V) Γ(S', W) := (g.appLE V W eVW).hom.toAlgebra
  intro h N Q
  let c := (restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app F
  refine (exists_moduleCohomology_ext_pullback_comparison (B := Γ(S', W)) h p).elim
    fun E comparison ↦ ?_
  refine comparison.elim fun E' compatibility ↦ ?_
  have hE := compatibility.1
  have hE' := compatibility.2.1
  have hmap := compatibility.2.2
  let e0 : ((RingedSpace.moduleCohomology
      (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj
        ((restrictFunctor (f ⁻¹ᵁ V).ι).obj F)) ≃+ HOver h N p :=
    (E ((restrictFunctor (f ⁻¹ᵁ V).ι).obj F)).trans
    (H.mapLinearEquiv c p).toAddEquiv
  refine ⟨E, hE, e0, rfl, ?_⟩
  refine (exists_flatBaseChange_module_leray_comparison
    f g F I J p V W hV hW eVW D rfl E' hE').elim fun b hb ↦ ?_
  let L := (restrictFunctor (f ⁻¹ᵁ V).ι).obj F
  let C := RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p
  let M := baseChangedModule (S := Γ(S', W)) h N
  let a : C.obj L → HOver (baseChangeSnd (S := Γ(S', W)) h) M p := fun x ↦
    E' M (moduleCohomologyFMap (baseChangeFst (S := Γ(S', W)) h)
      (baseChangeUnit (S := Γ(S', W)) h N) p ((C.map c.hom).hom x))
  let k : HOver h N p → HOver (baseChangeSnd (S := Γ(S', W)) h) M p :=
    H.baseChangeLinear (S := Γ(S', W)) h N p
  let r : C.obj L → Γ(Q, W) := fun x ↦
    Q.presheaf.map (homOfLE eVW).op
      (D.targetClass p
        (moduleCohomologyFMap ((pullback.snd g f).resLE (f ⁻¹ᵁ V)
          ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl) D.psi p x))
  refine ⟨b, equiv_transport_commutative_square e0.toEquiv
    (a := a) (k := k) (b := b) (r := r) ?_ hb⟩
  intro x
  have hx : E N ((C.map c.hom).hom x) = e0 x := hE _ _ c.hom x
  calc
    a x = k (E N ((C.map c.hom).hom x)) := hmap N ((C.map c.hom).hom x)
    _ = k (e0 x) := congrArg k hx

end AlgebraicGeometry.Scheme.Modules
