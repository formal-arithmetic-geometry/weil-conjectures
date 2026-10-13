/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel

/-! # Derived tensor comparison after restriction to the second coefficient ring

Source: Stacks Project, Tag 06Y6, Lemma 15.61.1, independence of choices.
(blueprint: lem-pc-base-derived-tensor-restricted-ring-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w w'
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

/-- Transport derived tensor cohomology as a module over the second coefficient ring.

Proof: restriction along eR and eB, with restriction along their inverses, gives
exact inverse equivalences of module categories. Applying them termwise gives
inverse equivalences of homotopy categories preserving quasi-isomorphisms. The
localization universal property extends these to the chosen derived categories,
also when their morphism universes differ. The coefficient tensor isomorphism
identifies ordinary extension of scalars, on generators b tensor x. Transport
M.derived and its universal counit through the localization equivalences.
Uniqueness of left derived functors identifies this transported functor with
N.derived, compatibly with the counits. Apply homology to its component at q and
conjugate by M.cohomologyIso and N.cohomologyIso; this gives kB and its inverse.
Naturality at multiplication by a, together with cohomologyIso_smul, gives the
first identity. The counit compatibility, comparison_eq and ordinaryIso_tmul,
followed by exact-restriction homology naturality, give the second identity on
underlying elements. The given generator formula for s identifies the ordinary
complex map appearing there. Restriction along includeRight is faithful, so the
ordinaryIso generator calculation suffices. No tensor-algebra linearity of kB
is asserted here: that is obtained by tensor induction in the caller. No
flatness or invertibility of comparison maps is used. Zero rings and complexes
are permitted, and the maps to C₀ and C do not enter this argument.
Source: Stacks Project, Tag 06Y6, Lemma 15.61.1, independence of choices and
universal derived change of rings; localization uniqueness supplies the
possibly different morphism universes.
(blueprint: lem-pc-base-derived-tensor-restricted-ring-comparison). -/
theorem exists_baseDerivedTensor_restricted_ring_comparison
    {R₀ A₀ B₀ C₀ R A B C : Type u}
    [CommRing R₀] [CommRing A₀] [CommRing B₀] [CommRing C₀]
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R₀ A₀] [Algebra R₀ B₀] [Algebra (A₀ ⊗[R₀] B₀) C₀]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
    [HasDerivedCategory.{w} (ModuleCat.{u} R₀)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B₀)]
    [HasDerivedCategory.{w'} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w'} (ModuleCat.{u} B)]
    (Q₀ : CochainComplex (ModuleCat.{u} A₀) ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (M : BaseDerivedTensorCohomologyModel R₀ A₀ B₀ Q₀ C₀)
    (N : BaseDerivedTensorCohomologyModel R A B Q C)
    (eR : R₀ ≃+* R) (eA : A₀ ≃+* A) (eB : B₀ ≃+* B)
    (hRA : eA.toRingHom.comp (algebraMap R₀ A₀) =
      (algebraMap R A).comp eR.toRingHom)
    (hRB : eB.toRingHom.comp (algebraMap R₀ B₀) =
      (algebraMap R B).comp eR.toRingHom)
    (q : Q₀ ≅ ((restrictScalars.{u} eA.toRingHom).mapHomologicalComplex (.up ℤ)).obj Q)
    (eE : (A₀ ⊗[R₀] B₀) ≃+* (A ⊗[R] B))
    (heE : ∀ (a : A₀) (b : B₀), eE (a ⊗ₜ[R₀] b) = eA a ⊗ₜ[R] eB b)
    (s : ((extendScalars (algebraMap A₀ (A₀ ⊗[R₀] B₀))).mapHomologicalComplex
        (.up ℤ)).obj Q₀ ≅
      ((restrictScalars.{u} eE.toRingHom).mapHomologicalComplex (.up ℤ)).obj
        (((extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
          (.up ℤ)).obj Q))
    (hs : ∀ (j : ℤ) (r : A₀ ⊗[R₀] B₀) (x : Q₀.X j),
      s.hom.f j (r ⊗ₜ[A₀,algebraMap A₀ (A₀ ⊗[R₀] B₀)] x) =
        eE r ⊗ₜ[A,algebraMap A (A ⊗[R] B)] (show Q.X j from q.hom.f j x))
    (i : ℤ) :
    let K := ((extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
      (.up ℤ)).obj Q
    ∃ kB : (restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).obj
        (M.cohomology i) ≅
      (restrictScalars.{u} eB.toRingHom).obj
        ((restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).obj
          (N.cohomology i)),
      (∀ (a : A₀) (x : M.cohomology i),
        kB.hom ((Algebra.TensorProduct.includeLeft (S := R₀) a : A₀ ⊗[R₀] B₀) • x) =
          (Algebra.TensorProduct.includeLeft (S := R) (eA a) : A ⊗[R] B) •
            (show N.cohomology i from kB.hom x)) ∧
      ∀ x : M.cohomology i,
        ((K.sc i).mapHomologyIso (restrictScalars.{u} eE.toRingHom)).inv
            (N.comparison i (show N.cohomology i from kB.hom x)) =
          HomologicalComplex.homologyMap s.hom i (M.comparison i x) := by sorry

end ModuleCat
