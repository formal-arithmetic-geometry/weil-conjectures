/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Matching affine covers under field extension

## References

* Stacks Project, Tags 01JR, 01JQ and 01T0
-/

@[expose] public section

universe z

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- A nonempty scheme locally of finite type over a field admits affine covers that
identify scalar extension chartwise with tensor products (Stacks, Tags 01JR, 01JQ, 01T0). -/
theorem exists_field_baseChange_affine_covers
    (k K : Type z) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{z}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [Nonempty X] :
    let Y := pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    Nonempty Y ∧ ∃ (I : Type z) (A : I → Type z) (rings : ∀ i, CommRing (A i)),
      letI := rings
      ∃ (algebras : ∀ i, Algebra k (A i)),
        letI := algebras
        (∀ i, Algebra.FiniteType k (A i)) ∧
          ∃ (U : I → X.Opens) (V : I → Y.Opens),
            (⨆ i, U i) = ⊤ ∧ (⨆ i, V i) = ⊤ ∧
            Nonempty (∀ i, (U i : Scheme.{z}) ≅ Spec (.of (A i))) ∧
            Nonempty (∀ i, (V i : Scheme.{z}) ≅ Spec (.of (A i ⊗[k] K))) := by
  classical
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let : Surjective g := ⟨fun p ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  have hnonempty : Nonempty (pullback f g : Scheme.{z}) := by
    obtain ⟨x⟩ := ‹Nonempty X›
    obtain ⟨y, _⟩ := (pullback.fst f g).surjective x
    exact ⟨y⟩
  refine ⟨hnonempty, ?_⟩
  let C := X.affineCover
  let D := Scheme.Pullback.openCoverOfLeft C f g
  let A (i : C.I₀) := Γ(C.X i, ⊤)
  let a (i : C.I₀) : k →+* A i :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (C.f i ≫ f).appTop).hom
  let : ∀ i, Algebra k (A i) := fun i ↦ (a i).toAlgebra
  refine ⟨C.I₀, (fun i ↦ ↥(A i)), (fun i ↦ inferInstance),
    (fun i ↦ inferInstance), ?_, (fun i ↦ (C.f i).opensRange),
    (fun i ↦ (D.f i).opensRange), C.iSup_opensRange, D.iSup_opensRange,
    ⟨fun i ↦ (C.f i).isoOpensRange.symm ≪≫ (C.X i).isoSpec⟩, ?_⟩
  · intro i
    change (a i).FiniteType
    exact (HasRingHomProperty.appTop (P := @LocallyOfFiniteType)
      (C.f i ≫ f) inferInstance).comp
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).surjective)
  · refine ⟨fun i ↦ (D.f i).isoOpensRange.symm ≪≫ ?_ ≪≫ pullbackSpecIso k (A i) K⟩
    have heq : (C.X i).isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (A i))) = C.f i ≫ f := by
      change (C.X i).toSpecΓ ≫
        Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ (C.f i ≫ f).appTop) = _
      rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
        Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    exact asIso (pullback.map (C.f i ≫ f) g
      (Spec.map (CommRingCat.ofHom (algebraMap k (A i)))) g
      (C.X i).isoSpec.hom (𝟙 _) (𝟙 _) (by simpa using heq.symm) (by simp))

end AlgebraicGeometry
