/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedComponentScalarModel.CondensedComponentScalarModelData
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import WeilConjectures.AlgebraicGeometry.CondensedGenericCoverScalarDescent
import WeilConjectures.AlgebraicGeometry.CondensedGenericScalarModel.CondensedGeometricFieldPerfectModel
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedLisseProEtaleLocality
import WeilConjectures.AlgebraicGeometry.ComponentDerivedSquare.ComponentDerivedPullbackSquare
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Generic scalar values and prescribed component covers

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Theorem 4.13,
first paragraph and the irreducible case (4.4).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedComponentScalarModel

private theorem geometric_generic_value
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (X : Scheme.{u}) [IrreducibleSpace X]
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)))
    (hK : Nonempty (HasRightDual K)) :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω)
      (η : Spec (.of Ω) ⟶ X),
      (∃ ξ : X, IsGenericPoint ξ (Set.univ : Set X) ∧ ξ ∈ Set.range η) ∧
      ∃ P : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ.X)),
        DerivedCategory.IsPerfectRingComplex P ∧
        Nonempty ((CondensedRing.upperStar Λ.X η).mapDerivedCategory.obj K ≅
          (condensedScalarRealization Λ.X (Spec (.of Ω))).obj P) := by
  let ξ : X := genericPoint X
  let Ω := AlgebraicClosure (X.residueField ξ)
  let η : Spec (.of Ω) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField ξ) Ω)) ≫
      X.fromSpecResidueField ξ
  refine ⟨Ω, inferInstance, inferInstance, η, ?_, ?_⟩
  · refine ⟨ξ, genericPoint_spec X, ?_⟩
    let y : Spec (.of Ω) := ⟨⊥, Ideal.isPrime_bot⟩
    refine ⟨y, ?_⟩
    dsimp [η]
    exact Scheme.fromSpecResidueField_apply ξ _
  · exact CondensedGenericScalarModel.geometric_field_perfect_model Λ Ω _
      (condensed_derivedPullback_preserves_dualizable Λ η K hK)

/-- Each reduced irreducible component has a perfect generic scalar value and a
w-contractible affine cover carrying that value. No finiteness or connectedness
assumption is made here, and no comparison
between different component values or common scalar value is asserted.

Source: HRS, Definitions 3.3 and 3.5, Lemma 4.1, Proposition 4.3(3), and
Theorem 4.13, first paragraph and irreducible case, pp. 12-13
(blueprint: lem-pod-condensed-component-generic-scalar-models).

Proof:
1. Give each component its reduced induced closed structure and pull K back to it.
It is a nonempty irreducible affine scheme, and inverse image preserves dualizability.
Choose its geometric generic point eta. The profinite point-site comparison and
contractible evaluation at the singleton identify K_eta with the realization of a
perfect complex P over R = Lambda(*). The scalar functor at a geometric point is
fully faithful by the same evaluation theorem and the terminal coefficient comparison.
2. Choose a faithfully flat ind-etale w-contractible affine cover T of this component.
The map on component spaces of T_eta -> T is onto: flat going down lifts a generic
prime below each prime of T, staying in its connected component; the tensor of the
two residue-field extensions is nonzero and has a prime, giving a point of T_eta.
Stonean projectivity supplies a section of this component map.
3. Component pullback is an equivalence on lisse objects on T. On T_eta it is an
equivalence on all derived objects by the affine geometric-point site comparison
and weakly-etale localization. Restrict the fixed generic model to T_eta, descend
through that equivalence, and pull back along the component section. The component
square and scalar pullback comparison give the asserted model on T.
This is performed separately for each component, so no overlap comparison or finite
connected-component argument is needed. If the ambient scheme is empty the indexing
type is empty. The zero coefficient ring is included by the same comparisons. -/
theorem component_generic_scalar_models
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (X : Scheme.{u}) [IsAffine X]
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)))
    (hK : Nonempty (HasRightDual K)) :
    ∃ P : irreducibleComponents X →
        DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ.X)),
      (∀ Z, DerivedCategory.IsPerfectRingComplex (P Z)) ∧
      ∀ Z, ∃ (T : Scheme.{u}) (f : T ⟶ component X Z),
        IsAffine T ∧ IsWContractibleRing Γ(T, ⊤) ∧ WeaklyEtale f ∧ Surjective f ∧
        Nonempty ((CondensedRing.upperStar Λ.X (f ≫ inclusion X Z)).mapDerivedCategory.obj K ≅
          (condensedScalarRealization Λ.X T).obj (P Z)) := by
  classical
  have h (Z : irreducibleComponents X) :
      ∃ P : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ.X)),
        DerivedCategory.IsPerfectRingComplex P ∧
        ∃ (T : Scheme.{u}) (f : T ⟶ component X Z),
          IsAffine T ∧ IsWContractibleRing Γ(T, ⊤) ∧ WeaklyEtale f ∧ Surjective f ∧
          Nonempty ((CondensedRing.upperStar Λ.X
              (f ≫ inclusion X Z)).mapDerivedCategory.obj K ≅
            (condensedScalarRealization Λ.X T).obj P) := by
    let Y := component X Z
    let i := inclusion X Z
    let L := (CondensedRing.upperStar Λ.X i).mapDerivedCategory.obj K
    have hL : Nonempty (HasRightDual L) :=
      condensed_derivedPullback_preserves_dualizable Λ i K hK
    obtain ⟨Ω, hfield, hac, η, hη, P, hP, ⟨e⟩⟩ := geometric_generic_value Λ Y L hL
    let := hfield
    let := hac
    obtain ⟨T, f, hT, hw, hf, hs, ⟨a⟩⟩ :=
      generic_cover_scalar_descent Λ Y L hL Ω η hη P hP e
    exact ⟨P, hP, T, f, hT, hw, hf, hs,
      ⟨(ComponentDerivedSquare.schemeComposition Λ i f).app K ≪≫ a⟩⟩
  choose P hP hcover using h
  exact ⟨P, hP, hcover⟩

end AlgebraicGeometry.ProEtale.CondensedComponentScalarModel
