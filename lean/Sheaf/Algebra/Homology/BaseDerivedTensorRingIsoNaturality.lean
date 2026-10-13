/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel

/-! # Naturality of the localized tensor counit under ring isomorphisms

Source: Stacks Project, Tag 06Y6, derived change of rings; Tag 0DJ8, equation-bc.
(blueprint: lem-pc-base-derived-tensor-ring-iso-naturality).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
noncomputable section
namespace ModuleCat

/-- Transport the localized tensor comparison through compatible ring isomorphisms.
The target chain isomorphism is fixed on pure tensors, rather than chosen freely.

Proof: restriction along the four ring isomorphisms gives inverse exact module
category equivalences. The two structural-map equations identify base restriction
and extension of scalars under these equivalences. The chain isomorphism q
identifies the input complexes. Transport the universal left-derived R-to-B
extension and its counit and use uniqueness of a left-derived lift to identify it
with the second model. Apply homology. Naturality for multiplication by A and
cohomologyIso_smul give compatibility with the A-action in addition to the B-action;
tensor induction makes this an isomorphism over A tensor_R B, transported through
the tensor of eA and eB. Extend to D, using hD, and forget scalars to obtain l. The equation
comparison_eq identifies the transported unlocalized counits. The pure-tensor
formula for t identifies the ordinary extension map, and localized_eq, followed
by the extension/restriction adjunction, gives the displayed equation. Exact
restriction commutes with homology via mapHomologyIso. No flatness, boundedness,
or invertibility of either comparison is required. The formulas also apply to
zero rings and zero complexes.
Source: Stacks Project, Tag 06Y6, lemma-derived-base-change; Tag 0DJ8, equation-bc.
(blueprint: lem-pc-base-derived-tensor-ring-iso-naturality). -/
theorem exists_baseDerivedTensor_ringIso_square
    {R A B D R0 A0 B0 D0 : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [CommRing R0] [CommRing A0] [CommRing B0] [CommRing D0]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
    [Algebra R0 A0] [Algebra R0 B0] [Algebra (A0 ⊗[R0] B0) D0]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R0)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B0)]
    (eR : R ≃+* R0) (eA : A ≃+* A0) (eB : B ≃+* B0) (eD : D ≃+* D0)
    (hA : ∀ r : R, eA (algebraMap R A r) = algebraMap R0 A0 (eR r))
    (hB : ∀ r : R, eB (algebraMap R B r) = algebraMap R0 B0 (eR r))
    (hD : ∀ (a : A) (b : B),
      eD (algebraMap (A ⊗[R] B) D (a ⊗ₜ[R] b)) =
        algebraMap (A0 ⊗[R0] B0) D0 (eA a ⊗ₜ[R0] eB b))
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (Q0 : CochainComplex (ModuleCat.{u} A0) ℤ)
    (q : Q ≅ ((restrictScalars.{u} eA.toRingHom).mapHomologicalComplex (.up ℤ)).obj Q0)
    (M : BaseDerivedTensorCohomologyModel R A B Q D)
    (M0 : BaseDerivedTensorCohomologyModel R0 A0 B0 Q0 D0)
    (t : (((extendScalars.{u, u, u} ((algebraMap (A ⊗[R] B) D).comp
        (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj Q) ≅
      ((restrictScalars.{u} eD.toRingHom).mapHomologicalComplex (.up ℤ)).obj
        (((extendScalars.{u, u, u} ((algebraMap (A0 ⊗[R0] B0) D0).comp
          (algebraMap A0 (A0 ⊗[R0] B0)))).mapHomologicalComplex (.up ℤ)).obj Q0))
    (ht : ∀ (k : ℤ) (d : D) (x : Q.X k),
      t.hom.f k (d ⊗ₜ[A, (algebraMap (A ⊗[R] B) D).comp
        (algebraMap A (A ⊗[R] B))] x) =
      eD d ⊗ₜ[A0, (algebraMap (A0 ⊗[R0] B0) D0).comp
        (algebraMap A0 (A0 ⊗[R0] B0))] (show Q0.X k from q.hom.f k x))
    (i : ℤ) :
    let V0 := ((extendScalars.{u, u, u} ((algebraMap (A0 ⊗[R0] B0) D0).comp
      (algebraMap A0 (A0 ⊗[R0] B0)))).mapHomologicalComplex (.up ℤ)).obj Q0
    let T := restrictScalars.{u} eD.toRingHom
    let F := forget₂ (ModuleCat.{u} D) AddCommGrpCat.{u}
    let F0 := forget₂ (ModuleCat.{u} D0) AddCommGrpCat.{u}
    ∃ l : F.obj ((extendScalars.{u, u, u} (algebraMap (A ⊗[R] B) D)).obj
        (M.cohomology i)) ≅
        F0.obj ((extendScalars.{u, u, u} (algebraMap (A0 ⊗[R0] B0) D0)).obj
          (M0.cohomology i)),
      l.hom ≫ F0.map (M0.localizedComparison i) ≫
          F.map ((V0.sc i).mapHomologyIso T).inv =
        F.map (M.localizedComparison i) ≫
          F.map (HomologicalComplex.homologyMap t.hom i) := by sorry

end ModuleCat
