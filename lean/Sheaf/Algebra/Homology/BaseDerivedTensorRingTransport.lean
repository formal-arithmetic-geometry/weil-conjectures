/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Change of all coefficient rings in the localized tensor comparison

Source: Stacks Project, Tags 06Y6 and 08IB, derived tensor functoriality.
(blueprint: lem-pc-base-derived-tensor-ring-transport).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

/-- The localized comparison is natural under compatible coefficient-ring
isomorphisms and a semilinear isomorphism of its input complex.

Proof: restriction along eR and eB gives exact inverse equivalences on module
categories and on their homotopy and derived categories. The two equations on
R identify extension R0 to B0 with extension R to B under these equivalences:
on generators the comparison sends b0 tensor q to eB(b0) tensor alpha(q).
Transport the universal left-derived functor and its counit through these
exact equivalences. Uniqueness of left-derived functors identifies this functor
with N.derived, compatibly with the counits. Applying homology and the two
cohomologyIso maps gives a semilinear isomorphism on base-tensor cohomology.
For a0 in A0, naturality of alpha for multiplication and cohomologyIso_smul
show that it intertwines a0 tensor 1 and eA(a0) tensor 1. Its B0-linearity
intertwines 1 tensor b0 and 1 tensor eB(b0). Tensor induction gives semilinearity
for the tensor of eA and eB over eR. The equations on C identify the two
extensions of these cohomology modules to C0 and C; extending the semilinear
isomorphism yields the additive isomorphism l. The equations comparison_eq
identify the unlocalized comparison with the transported counit. Use localized_eq
and the scalar-extension adjunction to identify the localized maps. The specified
generator formula for tau identifies the resulting ordinary-complex map with
its given tau, by tensor induction. Finally the exact forgetful homology
isomorphisms yield the displayed equality. The comparisons need not be
invertible, the inputs need not be K-flat, and all rings may be zero rings.
Source: Stacks Project, Tag 06Y6, lemma-derived-base-change, and Tag 08IB,
lemma-compare-base-change; the coefficient equivalences are exact.
(blueprint: lem-pc-base-derived-tensor-ring-transport). -/
theorem exists_baseDerivedTensor_ring_transport
    {R₀ A₀ B₀ C₀ R A B C : Type u}
    [CommRing R₀] [CommRing A₀] [CommRing B₀] [CommRing C₀]
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R₀ A₀] [Algebra R₀ B₀] [Algebra (A₀ ⊗[R₀] B₀) C₀]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
    [HasDerivedCategory (ModuleCat.{u} R₀)] [HasDerivedCategory (ModuleCat.{u} B₀)]
    [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} B)]
    (Q₀ : CochainComplex (ModuleCat.{u} A₀) ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (M : BaseDerivedTensorCohomologyModel R₀ A₀ B₀ Q₀ C₀)
    (N : BaseDerivedTensorCohomologyModel R A B Q C)
    (eR : R₀ ≃+* R) (eA : A₀ ≃+* A) (eB : B₀ ≃+* B) (eC : C₀ ≃+* C)
    (hRA : eA.toRingHom.comp (algebraMap R₀ A₀) =
      (algebraMap R A).comp eR.toRingHom)
    (hRB : eB.toRingHom.comp (algebraMap R₀ B₀) =
      (algebraMap R B).comp eR.toRingHom)
    (hCA : eC.toRingHom.comp
        ((algebraMap (A₀ ⊗[R₀] B₀) C₀).comp (algebraMap A₀ (A₀ ⊗[R₀] B₀))) =
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B))).comp eA.toRingHom)
    (hCB : eC.toRingHom.comp ((algebraMap (A₀ ⊗[R₀] B₀) C₀).comp
        Algebra.TensorProduct.includeRight.toRingHom) =
      ((algebraMap (A ⊗[R] B) C).comp
        Algebra.TensorProduct.includeRight.toRingHom).comp eB.toRingHom)
    (α : ((forget₂ (ModuleCat.{u} A₀) AddCommGrpCat.{u}).mapHomologicalComplex
        (.up ℤ)).obj Q₀ ≅
      ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℤ)).obj Q)
    (hα : ∀ (i : ℤ) (a : A₀) (q : Q₀.X i),
      α.hom.f i (a • q) = eA a • (show Q.X i from α.hom.f i q))
    (τ :
      ((forget₂ (ModuleCat.{u} C₀) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℤ)).obj
        (((extendScalars ((algebraMap (A₀ ⊗[R₀] B₀) C₀).comp
          (algebraMap A₀ (A₀ ⊗[R₀] B₀)))).mapHomologicalComplex (.up ℤ)).obj Q₀) ≅
      ((forget₂ (ModuleCat.{u} C) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℤ)).obj
        (((extendScalars ((algebraMap (A ⊗[R] B) C).comp
          (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj Q))
    (hτ : ∀ (i : ℤ) (c : C₀) (q : Q₀.X i),
      τ.hom.f i (c ⊗ₜ[A₀,(algebraMap (A₀ ⊗[R₀] B₀) C₀).comp
          (algebraMap A₀ (A₀ ⊗[R₀] B₀))] q) =
        eC c ⊗ₜ[A,(algebraMap (A ⊗[R] B) C).comp
          (algebraMap A (A ⊗[R] B))] (show Q.X i from α.hom.f i q))
    (i : ℤ) :
    let F₀ := forget₂ (ModuleCat.{u} C₀) AddCommGrpCat.{u}
    let F := forget₂ (ModuleCat.{u} C) AddCommGrpCat.{u}
    let T₀ := ((extendScalars ((algebraMap (A₀ ⊗[R₀] B₀) C₀).comp
      (algebraMap A₀ (A₀ ⊗[R₀] B₀)))).mapHomologicalComplex (.up ℤ)).obj Q₀
    let T := ((extendScalars ((algebraMap (A ⊗[R] B) C).comp
      (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj Q
    ∃ l : F₀.obj ((extendScalars (algebraMap (A₀ ⊗[R₀] B₀) C₀)).obj (M.cohomology i)) ≅
        F.obj ((extendScalars (algebraMap (A ⊗[R] B) C)).obj (N.cohomology i)),
      F₀.map (M.localizedComparison i) ≫ ((T₀.sc i).mapHomologyIso F₀).inv ≫
        HomologicalComplex.homologyMap τ.hom i ≫ ((T.sc i).mapHomologyIso F).hom =
      l.hom ≫ F.map (N.localizedComparison i) := by sorry

end ModuleCat
