/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Finite
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-! # Constancy of field-valued points of finite schemes -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
namespace AlgebraicGeometry

private theorem finite_alg_factor {k B L : Type u} [Field k] [IsAlgClosed k]
    [CommRing B] [Algebra k B] [Algebra.IsIntegral k B]
    [Field L] [Algebra k L] (f : B →ₐ[k] L) :
    ∃ c : B →ₐ[k] k, (Algebra.ofId k L).comp c = f := by
  let f' : B →ₐ[k] integralClosure k L :=
    f.codRestrict _ (fun b ↦ (Algebra.IsIntegral.isIntegral b).map f)
  let e : k ≃ₐ[k] integralClosure k L :=
    AlgEquiv.ofBijective (Algebra.ofId k (integralClosure k L))
      IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨e.symm.toAlgHom.comp f', ?_⟩
  ext b
  exact congrArg Subtype.val (e.apply_symm_apply (f' b))

private theorem finite_points_surjective {k L : Type u} [Field k] [IsAlgClosed k]
    [Field L] [Algebra k L] (G : Over (Spec (.of k))) [IsFinite G.hom] :
    Function.Surjective (fun s : 𝟙_ (Over (Spec (.of k))) ⟶ G ↦
      toUnit (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L)))) ≫ s) := by
  have : IsAffine G.left := isAffine_of_isAffineHom G.hom
  let := G.hom.ΓAlgebra
  have : Module.Finite k Γ(G.left, ⊤) := by
    apply RingHom.finite_algebraMap.mp
    rw [G.hom.algebraMap_ΓAlgebra]
    exact RingHom.Finite.comp G.hom.finite_appTop
      (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (.of k)).inv).2)
  let ψ : (Γ(G.left, ⊤) →ₐ[k] k) → (Γ(G.left, ⊤) →ₐ[k] L) := (Algebra.ofId k L).comp
  have hψ : Function.Surjective ψ := finite_alg_factor
  have key : (fun s : 𝟙_ (Over (Spec (.of k))) ⟶ G ↦
      toUnit (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L)))) ≫ s) =
      (G.hom.overHomEquivAlgHom L).symm ∘ ψ ∘ pointsEquivAlgHom G := by
    ext1 s
    refine (Equiv.eq_symm_apply _).2 ?_
    have hv : (toUnit (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L)))) ≫
        specAlgebraMapSelfIso.inv).left = Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
      have := Over.w (toUnit (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L)))) ≫
        specAlgebraMapSelfIso.inv)
      exact ((Category.comp_id _).symm.trans
        (congrArg (_ ≫ ·) (Spec.map_id (.of k)).symm)).trans this
    have := G.hom.overHomEquivAlgHom_comp _ hv (specAlgebraMapSelfIso.hom ≫ s)
    simp only [Category.assoc, Iso.inv_hom_id_assoc] at this
    exact this
  rw [key]
  exact (Equiv.surjective _).comp (hψ.comp (Equiv.surjective _))

/-- A point of a finite scheme over an algebraically closed field is constant
on every field extension. On global sections, every image is integral over k,
so lies in k. Factor the algebra homomorphism through the integral closure and
invert its canonical algebra isomorphism with k. The affine point equivalence
transports this factorization back to a constant scheme point.
Source: the constant-torsion argument in the scope counterexample.
(blueprint: lem-sf-finite-scheme-field-points-constant) -/
theorem finiteSchemeFieldPointsConstant {k L : Type u} [Field k] [IsAlgClosed k]
    [Field L] (G : Over (Spec (.of k))) [IsFinite G.hom]
    (g : Spec (.of L) ⟶ Spec (.of k)) (s : Over.mk g ⟶ G) :
    ∃ s₀ : 𝟙_ (Over (Spec (.of k))) ⟶ G, toUnit _ ≫ s₀ = s := by
  obtain ⟨c, rfl⟩ := Spec.map_surjective g
  let : Algebra k L := c.hom.toAlgebra
  exact finite_points_surjective G s

end AlgebraicGeometry
