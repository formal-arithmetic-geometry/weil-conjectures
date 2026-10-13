/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module

public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel

/-! # Coefficient transport for the ordinary derived tensor comparison

Source: Stacks Project, Tag 06Y6, lemma-derived-base-change.
(blueprint: lem-pc-base-derived-tensor-ordinary-ring-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w w'
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

/-- Transport the ordinary comparison, before extension to the fourth ring.

Proof: compatible eR, eA and eB induce a tensor-ring isomorphism eE, sending
 a tensor b to eA(a) tensor eB(b). Tensoring the input isomorphism gives s,
with the stated generator formula. Restriction along eR and eB gives exact
inverse equivalences on module, homotopy and derived categories. If the chosen
derived categories have different morphism universes, use their localization
universal properties to identify the two category-of-fractions presentations.
Transport M's universal left-derived functor and counit through these
 equivalences. Uniqueness of universal left-derived functors identifies the
result with N's functor, compatibly with the counits. Apply homology and conjugate
by cohomologyIso to obtain the cohomology isomorphism k. Naturality for
multiplication by a and cohomologyIso_smul give eA-semilinearity; B-linearity
gives eB-semilinearity. Tensor induction gives eE-semilinearity, for both k and
its inverse. The comparison_eq identities, counit compatibility and homology
naturality at s give the displayed ordinary comparison square. The ordinaryIso
maps are identified on generators by ordinaryIso_tmul. Neither localizedComparison
nor ordinaryToLocalized occurs in this conclusion. Zero rings and zero complexes
are allowed; no flatness or invertibility of comparisons is used.
Source: Stacks Project, Tag 06Y6, lemma-derived-base-change, independence of
choices and derived change of rings; the two-universe formulation uses
localization uniqueness.
(blueprint: lem-pc-base-derived-tensor-ordinary-ring-comparison). -/
theorem exists_baseDerivedTensor_ordinary_ring_comparison
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
    (i : ℤ) :
    let K₀ := ((extendScalars (algebraMap A₀ (A₀ ⊗[R₀] B₀))).mapHomologicalComplex
      (.up ℤ)).obj Q₀
    let K := ((extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
      (.up ℤ)).obj Q
    ∃ (eE : (A₀ ⊗[R₀] B₀) ≃+* (A ⊗[R] B)),
      (∀ (a : A₀) (b : B₀), eE (a ⊗ₜ[R₀] b) = eA a ⊗ₜ[R] eB b) ∧
      ∃ (s : K₀ ≅ ((restrictScalars.{u} eE.toRingHom).mapHomologicalComplex
          (.up ℤ)).obj K)
        (k : M.cohomology i ≅ (restrictScalars.{u} eE.toRingHom).obj (N.cohomology i)),
        (∀ (j : ℤ) (r : A₀ ⊗[R₀] B₀) (x : Q₀.X j),
          s.hom.f j (r ⊗ₜ[A₀, algebraMap A₀ (A₀ ⊗[R₀] B₀)] x) =
            eE r ⊗ₜ[A, algebraMap A (A ⊗[R] B)] (show Q.X j from q.hom.f j x)) ∧
        k.hom ≫ (restrictScalars.{u} eE.toRingHom).map (N.comparison i) ≫
            ((K.sc i).mapHomologyIso (restrictScalars.{u} eE.toRingHom)).inv =
          M.comparison i ≫ HomologicalComplex.homologyMap s.hom i := by sorry

end ModuleCat
