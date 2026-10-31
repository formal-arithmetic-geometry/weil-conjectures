/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleCoefficientTransportInterfaces
public import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.CategoryTheory.ConstantFiniteFreeExtensionLeftExact
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # Exact finite-free scalar extension at a strict étale level -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

/-- A finite-free coefficient level has exact scalar extension, and every specified
universal derived scalar counit is invertible on every complex.
Source: Stacks Project, Tags 03CZ and 06YY; Zheng, Construction 4.1.
(blueprint: new-pur-strict-etale-finite-free-scalar-exact).

Proof: turn the quotient-ring basis into finite and free module instances. The
constant-sheaf finite-free exactness theorem applies to the actual tensor functor,
whose object and map equations are definitional. Its tensor/restriction adjunction
supplies preservation of finite colimits. Consequently its functor on complexes
preserves quasi-isomorphisms. The universal left-derived counit is therefore an
isomorphism, by uniqueness of localization. This includes rank zero and the zero
coefficient ring; no boundedness assumption occurs.
-/
theorem strictEtaleFiniteFreeScalarExact
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index)
    (T : Scheme.{u}) (n : ℕ) (L : StrictEtaleLevelScalar a T n)
    (hfree : ∃ r : ℕ, Nonempty (Module.Basis (Fin r)
      (O ⧸ Ideal.span {ell} ^ (index n + 1))
      ((ModuleCat.restrictScalars (a.ring n)).obj
        (ModuleCat.of (O' ⧸ Ideal.span {mu} ^ (n + 1))
          (O' ⧸ Ideal.span {mu} ^ (n + 1)))))) :
    PreservesFiniteLimits (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n)) ∧
      IsIso L.counit := by
  let A := O ⧸ Ideal.span {ell} ^ (index n + 1)
  let B := O' ⧸ Ideal.span {mu} ^ (n + 1)
  let : Algebra A B := (a.ring n).toAlgebra
  obtain ⟨r, ⟨b⟩⟩ := hfree
  change Module.Basis (Fin r) A B at b
  let : Module.Free A B := Module.Free.of_basis b
  let : Module.Finite A B := Module.Finite.of_basis b
  let α := (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (algebraMap A B))
  have hlim : PreservesFiniteLimits
      (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n)) := by
    change PreservesFiniteLimits (siteCoefficientTensor.{u + 1, u, u + 1} α)
    apply constantFiniteFree_extensionLeftExact T.smallEtaleTopology
      (CommRingCat.of A) (CommRingCat.of B)
      (siteCoefficientTensor.{u + 1, u, u + 1} α) (fun _ ↦ by
        unfold siteCoefficientTensor
        rfl)
    intro M N f
    unfold siteCoefficientTensor
    change changeOfRingsHom α M f = 𝟙 _ ≫ changeOfRingsHom α M f ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  have hcolim : PreservesFiniteColimits
      (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n)) := by
    let : PreservesColimitsOfSize.{0, 0}
        (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n)) :=
      (siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf T n)).leftAdjoint_preservesColimits
    infer_instance
  refine ⟨hlim, ?_⟩
  let := L.isDerived
  apply Functor.isIso_of_isLeftDerivedFunctor_of_inverts
    (W := HomologicalComplex.quasiIso (strictEtaleLevel T O ell (index n)) (.up ℤ))
    L.derived L.counit
  intro K N f hf
  have : QuasiIso f := hf
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance

end AlgebraicGeometry
