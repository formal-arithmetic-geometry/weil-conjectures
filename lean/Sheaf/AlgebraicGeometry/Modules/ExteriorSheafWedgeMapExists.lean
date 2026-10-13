/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension

/-!
# Wedging two exterior sheaves before quotient descent

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph,
exterior-power and tensor universal properties (blueprint: lem-sc-exterior-sheaf-wedge-map).
-/

@[expose] public section

universe v
open CategoryTheory Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

private theorem restriction_wedge {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    {U V : X.Opensᵒᵖ} (g : U ⟶ V) (a : Fin n → M.val.obj U) :
    exteriorSheafRestriction M n g (exteriorPower.ιMulti (X.presheaf.obj U) n a) =
      exteriorPower.ιMulti (X.presheaf.obj V) n (fun i ↦ M.val.map g (a i)) :=
  (Classical.choose_spec (exteriorSheafRestriction_existsUnique M n g)).1 a

private noncomputable def wedgeMul {R M : Type v} [CommRing R] [AddCommGroup M]
    [Module R M] (r s : ℕ) :
    (⋀[R]^r M) →ₗ[R] (⋀[R]^s M) →ₗ[R] (⋀[R]^(r + s) M) where
  toFun x :=
    { toFun := fun y ↦ ⟨x.val * y.val, by
        change x.val * y.val ∈ LinearMap.range (ExteriorAlgebra.ι R) ^ (r + s)
        rw [pow_add]
        exact Submodule.mul_mem_mul x.property y.property⟩
      map_add' := by intro y z; apply Subtype.ext; exact mul_add _ _ _
      map_smul' := by intro c y; apply Subtype.ext; exact mul_smul_comm _ _ _ }
  map_add' := by intro x y; ext z; exact add_mul _ _ _
  map_smul' := by intro c x; ext y; exact smul_mul_assoc _ _ _

private theorem wedgeMul_wedge {R M : Type v} [CommRing R] [AddCommGroup M]
    [Module R M] (r s : ℕ) (a : Fin r → M) (c : Fin s → M) :
    wedgeMul r s (exteriorPower.ιMulti R r a) (exteriorPower.ιMulti R s c) =
      exteriorPower.ιMulti R (r + s) (Fin.append a c) := by
  apply Subtype.ext
  exact ExteriorAlgebra.ιMulti_mul_ιMulti a c

set_option maxHeartbeats 800000 in
-- Comparing the scheme and ring-sheaf scalar structures requires additional elaboration.
set_option backward.isDefEq.respectTransparency false in
/-- Wedge the image of the first tuple with the second tuple, without choosing quotient lifts.
For each open, the concatenated wedge is alternating and multilinear separately in the two
blocks. Linearize each block through the exterior-power universal property and then through
the tensor-product universal property. These maps commute with restriction: on generating
wedges this follows from naturality of `f` and the exterior-power restrictions. First compose
with the target's sheafification unit. Extend to the sheafifications of both source factors
using local representatives; equality on overlaps follows from separatedness of the target.
The tensor sheaf universal property gives the asserted sheaf morphism. Its pure-wedge formula
follows from the defining sectionwise maps. This construction works for arbitrary `f`; it uses
neither exactness nor a rank bound. Empty blocks give multiplication by the degree-zero scalar.
Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph, universal properties
(blueprint: lem-sc-exterior-sheaf-wedge-map). -/
theorem exteriorSheaf_wedgeMap_exists {X : Scheme.{v}} {A B : X.Modules}
    (f : A ⟶ B) (r s t : ℕ) (ht : t = r + s) :
    ∃ ψ : exteriorSheaf A r ⊗ exteriorSheaf B s ⟶ exteriorSheaf B t,
      ∀ (U : X.Opens) (a : Fin r → A.val.obj (op U))
        (c : Fin s → B.val.obj (op U)),
        ψ.val.app (op U)
          (tmulSection (exteriorSheafSection A r U a) (exteriorSheafSection B s U c)) =
          exteriorSheafSection B t U
            (fun i ↦ Fin.append (fun j ↦ f.val.app (op U) (a j)) c (Fin.cast ht i)) := by
  subst t
  let : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (𝟙 X.ringCatSheaf.obj) :=
    Presheaf.isLocallyInjective_of_injective _ _ (fun _ ↦ Function.injective_id)
  let : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (𝟙 X.ringCatSheaf.obj) :=
    Presheaf.isLocallySurjective_of_surjective _ _ (fun _ ↦ Function.surjective_id)
  let η := (PresheafOfModules.sheafificationAdjunction.{v}
    (𝟙 X.ringCatSheaf.obj)).unit
  let b : ∀ U : X.Opensᵒᵖ,
      (exteriorSheafPresheaf A r).obj U →ₗ[X.presheaf.obj U]
        (exteriorSheafPresheaf B s).obj U →ₗ[X.presheaf.obj U]
          (exteriorSheaf B (r + s)).val.obj U := fun U ↦
    (LinearMap.llcomp (X.presheaf.obj U) _ _ _
      ((η.app (exteriorSheafPresheaf B (r + s))).app U).hom).comp
      ((wedgeMul r s).comp
        (exteriorPower.map (R := X.presheaf.obj U) r (f.val.app U).hom))
  have hb (U : X.Opensᵒᵖ) (a : Fin r → A.val.obj U)
      (c : Fin s → B.val.obj U) :
      b U (exteriorPower.ιMulti (X.presheaf.obj U) r a)
        (exteriorPower.ιMulti (X.presheaf.obj U) s c) =
      exteriorSheafSection B (r + s) U.unop
        (Fin.append (fun j ↦ f.val.app U (a j)) c) := by
    change (η.app (exteriorSheafPresheaf B (r + s))).app U
      (wedgeMul r s
        (exteriorPower.map (R := X.presheaf.obj U) r (f.val.app U).hom
          (exteriorPower.ιMulti (X.presheaf.obj U) r a))
        (exteriorPower.ιMulti (X.presheaf.obj U) s c)) = _
    rw [exteriorPower.map_apply_ιMulti, wedgeMul_wedge]
    rfl
  have hbmap : ∀ {U V : X.Opensᵒᵖ} (g : U ⟶ V) (x y),
      b V ((exteriorSheafPresheaf A r).map g x)
        ((exteriorSheafPresheaf B s).map g y) =
      (exteriorSheaf B (r + s)).val.map g (b U x y) := by
    intro U V g x y
    have hpure (a : Fin r → A.val.obj U) (c : Fin s → B.val.obj U) :
        b V ((exteriorSheafPresheaf A r).map g
          (exteriorPower.ιMulti (X.presheaf.obj U) r a))
          ((exteriorSheafPresheaf B s).map g
            (exteriorPower.ιMulti (X.presheaf.obj U) s c)) =
        (exteriorSheaf B (r + s)).val.map g
          (b U (exteriorPower.ιMulti (X.presheaf.obj U) r a)
            (exteriorPower.ιMulti (X.presheaf.obj U) s c)) := by
      change b V (exteriorSheafRestriction A r g
        (exteriorPower.ιMulti (X.presheaf.obj U) r a))
        (exteriorSheafRestriction B s g (exteriorPower.ιMulti (X.presheaf.obj U) s c)) = _
      rw [restriction_wedge A r g a, restriction_wedge B s g c]
      erw [hb V (fun i ↦ A.val.map g (a i)) (fun i ↦ B.val.map g (c i)), hb U a c]
      let d := Fin.append (fun j ↦ f.val.app U (a j)) c
      have hn := PresheafOfModules.naturality_apply
        (η.app (exteriorSheafPresheaf B (r + s))) g
        (exteriorPower.ιMulti (X.presheaf.obj U) (r + s) d)
      apply Eq.trans ?_ hn
      apply congrArg ((η.app (exteriorSheafPresheaf B (r + s))).app V)
      change exteriorPower.ιMulti (X.presheaf.obj V) (r + s)
          (Fin.append (fun j ↦ f.val.app V (A.val.map g (a j)))
            (fun j ↦ B.val.map g (c j))) =
        exteriorSheafRestriction B (r + s) g
          (exteriorPower.ιMulti (X.presheaf.obj U) (r + s) d)
      rw [restriction_wedge B (r + s) g d]
      apply congrArg (exteriorPower.ιMulti (X.presheaf.obj V) (r + s))
      funext i
      refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
      · simp only [d, Fin.append_left]
        exact PresheafOfModules.naturality_apply f.val g (a j)
      · simp only [d, Fin.append_right]
    have hfirst (a : Fin r → A.val.obj U) : ∀ y,
        b V ((exteriorSheafPresheaf A r).map g
          (exteriorPower.ιMulti (X.presheaf.obj U) r a))
          ((exteriorSheafPresheaf B s).map g y) =
        (exteriorSheaf B (r + s)).val.map g
          (b U (exteriorPower.ιMulti (X.presheaf.obj U) r a) y) := by
      intro y
      have hy : y ∈ Submodule.span (X.presheaf.obj U)
          (Set.range (exteriorPower.ιMulti (X.presheaf.obj U) s)) := by
        rw [exteriorPower.ιMulti_span]; trivial
      induction hy using Submodule.span_induction with
      | mem y hy => obtain ⟨c, rfl⟩ := hy; exact hpure a c
      | zero => simp only [map_zero]
      | add y z _ _ hy hz => simp only [map_add, hy, hz]
      | smul k y _ hy =>
        rw [PresheafOfModules.map_smul, (b V _).map_smul,
          (b U _).map_smul, PresheafOfModules.map_smul, hy]
    have hx : x ∈ Submodule.span (X.presheaf.obj U)
        (Set.range (exteriorPower.ιMulti (X.presheaf.obj U) r)) := by
      rw [exteriorPower.ιMulti_span]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact hfirst a y
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | add x z _ _ hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
    | smul k x _ hx =>
      rw [PresheafOfModules.map_smul, (b V).map_smul, LinearMap.smul_apply,
        (b U).map_smul, LinearMap.smul_apply, PresheafOfModules.map_smul, hx]
  obtain ⟨β, ⟨hβ, hβunit⟩, _⟩ :=
    PresheafOfModules.existsUnique_bilinear_sheafification_extension
      X.presheaf X.sheaf (𝟙 X.ringCatSheaf.obj)
      (exteriorSheafPresheaf A r) (exteriorSheafPresheaf B s)
      (exteriorSheaf B (r + s)) b hbmap
  obtain ⟨ψ, hψ, _⟩ := SheafOfModules.tensor_bilinear_universal X.sheaf
    (exteriorSheaf A r) (exteriorSheaf B s) (exteriorSheaf B (r + s)) β hβ
  refine ⟨ψ, ?_⟩
  intro U a c
  exact (hψ (op U) (exteriorSheafSection A r U a)
    (exteriorSheafSection B s U c)).trans
      ((hβunit (op U) (exteriorPower.ιMulti (X.presheaf.obj (op U)) r a)
        (exteriorPower.ιMulti (X.presheaf.obj (op U)) s c)).trans (hb (op U) a c))

end AlgebraicGeometry.Scheme.Modules
