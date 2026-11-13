/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleFieldPointFunctor
import WeilConjectures.AlgebraicGeometry.EtaleCoproductOfFiniteSeparableFields
import WeilConjectures.AlgebraicGeometry.GaloisSetEmbeddingDecomposition
import WeilConjectures.AlgebraicGeometry.EtaleCoproductEmbeddingPoints

/-!
# Essential surjectivity of the geometric-point functor

Source: Stacks Project, Tag 03QR.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local instance] etaleFieldDiscreteForget₂ etaleFieldActionForget₂

variable (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep]
  [IsSepClosure K Ksep]

/-- Every discrete continuous Galois set is the geometric points of an étale scheme
(Stacks, Tag 03QR). -/
theorem etaleFieldPointFunctor_essSurj :
    (etaleFieldPointFunctor K Ksep).EssSurj := by
  classical
  refine ⟨fun M ↦ ?_⟩
  obtain ⟨I, E, hfinite, hsep, eM, heM⟩ := galoisSet_embedding_decomposition K Ksep M
  let := hfinite
  let := hsep
  let f := Sigma.desc (fun i : I ↦
    Spec.map (CommRingCat.ofHom (algebraMap K (E i))))
  have : Etale f := etale_sigmaDesc_spec_of_finite_separable K I (fun i ↦ E i)
  let X := Scheme.Etale.mk f
  obtain ⟨eX, heX⟩ := etaleCoproduct_embedding_points K Ksep I E
  let e : ((etaleFieldPointFunctor K Ksep).obj X).obj.obj.V ≃ M.obj.obj.V :=
    eX.trans eM.symm
  have he (g : Gal(Ksep/K)) (x : ((etaleFieldPointFunctor K Ksep).obj X).obj.obj.V) :
      e (((etaleFieldPointFunctor K Ksep).obj X).obj.obj.ρ g x) = M.obj.obj.ρ g (e x) := by
    apply eM.injective
    simp only [e, Equiv.trans_apply, Equiv.apply_symm_apply]
    rw [heX, heM, eM.apply_symm_apply]
  let a : (etaleFieldPointFunctor K Ksep).obj X ⟶ M :=
    ⟨⟨{ hom := ↾e,
         comm := fun g ↦ by
           apply ConcreteCategory.hom_ext
           intro x
           exact he g x }⟩⟩
  let b : M ⟶ (etaleFieldPointFunctor K Ksep).obj X :=
    ⟨⟨{ hom := ↾e.symm,
         comm := fun g ↦ by
           apply ConcreteCategory.hom_ext
           intro y
           apply e.injective
           simpa using (he g (e.symm y)).symm }⟩⟩
  refine ⟨X, ⟨⟨a, b, ?_, ?_⟩⟩⟩
  · apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    apply ConcreteCategory.hom_ext
    intro x
    exact e.symm_apply_apply x
  · apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    apply ConcreteCategory.hom_ext
    intro y
    exact e.apply_symm_apply y

end AlgebraicGeometry
