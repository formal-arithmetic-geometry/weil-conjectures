/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.TestObjectPushforwardSections
public import WeilConjectures.RingTheory.ProEtale.ClosedLiftRetraction

/-!
# Sections of the coefficient sheaf over finite test objects

Let `U ≅ Spec R` be an object of `X_proét` such that every faithfully flat ind-étale
`R`-algebra has an `R`-algebra retraction (e.g. `R` is w-contractible), and `S` a finite set.
Then `LC(S, R) = R^S` has the same retraction property
(`LocallyConstant.exists_retraction_of_discreteTopology`): a faithfully flat ind-étale
`LC(S, R)`-algebra `T` retracts onto `LC(S, R)` by retracting each base change `R ⊗_{LC(S, R)} T`
along the evaluations `LC(S, R) ⟶ R` at points of `S`. As `U[S] ≅ Spec LC(S, R)`, the map from
`V ↦ Λ(π₀ V)` to its sheafification is bijective on sections over `U[S]`
(`AlgebraicGeometry.ProEtale.bijective_toSheafify_testObject_of_finite`), and hence the sections
of `Λ_X` over `U[S]` are `Λ(π₀(U) × S)`
(`AlgebraicGeometry.ProEtale.bijective_sections_testObject_of_finite`).

For an infinite extremally disconnected `S` the retraction property of `LC(S, R)` is not a formal
consequence of that of `R`: for `R` w-contractible it amounts to `π₀(Spec R) × S` being
extremally disconnected, which fails in general (e.g. `βℕ × βℕ`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace LocallyConstant

/-- Let `R` be a ring such that every faithfully flat ind-étale `R`-algebra has a retraction, and
`S` a discrete space. Then every faithfully flat ind-étale `LC(S, R)`-algebra `T` has a retraction:
for each `s : S`, a retraction of the base change `R ⊗_{LC(S, R)} T` along the evaluation at `s`
gives a ring map `T ⟶ R` extending the evaluation at `s`, and these assemble to `T ⟶ LC(S, R)`. -/
theorem exists_retraction_of_discreteTopology {R : Type u} [CommRing R]
    (hR : ∀ (T : Type u) [CommRing T] [Algebra R T] [Algebra.IndEtale R T]
      [Module.FaithfullyFlat R T], ∃ f : T →+* R, f.comp (algebraMap R T) = RingHom.id R)
    (S : Type u) [TopologicalSpace S] [DiscreteTopology S]
    (T : Type u) [CommRing T] [Algebra (LocallyConstant S R) T]
    [Algebra.IndEtale (LocallyConstant S R) T] [Module.FaithfullyFlat (LocallyConstant S R) T] :
    ∃ f : T →+* LocallyConstant S R,
      f.comp (algebraMap (LocallyConstant S R) T) = RingHom.id _ := by
  have hev (s : S) : ∃ g : T →+* R,
      g.comp (algebraMap (LocallyConstant S R) T) = evalRingHom s := by
    let : Algebra (LocallyConstant S R) R := (evalRingHom s).toAlgebra
    have : Algebra.IndEtale R (TensorProduct (LocallyConstant S R) R T) :=
      Algebra.ClosedLift.indEtale_tensorProduct _ R T
    obtain ⟨r, hr⟩ := hR (TensorProduct (LocallyConstant S R) R T)
    refine ⟨r.comp Algebra.TensorProduct.includeRight.toRingHom, RingHom.ext fun h ↦ ?_⟩
    have key : r ((1 : R) ⊗ₜ[LocallyConstant S R] algebraMap (LocallyConstant S R) T h) =
        evalRingHom s h := by
      rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
      exact RingHom.congr_fun hr (evalRingHom s h)
    exact key
  choose g hg using hev
  refine ⟨{ toFun t := ⟨fun s ↦ g s t, IsLocallyConstant.of_discrete _⟩
            map_one' := by ext; simp
            map_mul' _ _ := by ext; simp
            map_zero' := by ext; simp
            map_add' _ _ := by ext; simp }, RingHom.ext fun h ↦ ?_⟩
  ext s
  exact RingHom.congr_fun (hg s) h

end LocallyConstant

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {X : Scheme.{u}} (k : X ⟶ specZ.{u}) (U : X.ProEt) (S : Profinite.{u}) [Finite S]

/-- Let `U ≅ Spec R` be an object of `X_proét` such that every faithfully flat ind-étale
`R`-algebra has a retraction, and `S` a finite set. Then the map from `V ↦ Λ(π₀ V)` to its
sheafification is bijective on sections over the test object `U[S] ≅ Spec LC(S, R)`. -/
theorem bijective_toSheafify_testObject_of_finite
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) {R : CommRingCat.{u}}
    (hR : ∀ (T : Type u) [CommRing T] [Algebra R T] [Algebra.IndEtale R T]
      [Module.FaithfullyFlat R T], ∃ f : T →+* R, f.comp (algebraMap R T) = RingHom.id R)
    (e : U.left ≅ Spec R) :
    Function.Bijective
      ((toSheafify (ProEt.topology X) ((connectedComponentsAlong k).op ⋙ Λ.obj)).app
        (op (testObject k U S))) :=
  bijective_toSheafify_connectedComponentsAlong_of_forall_exists_retraction k Λ
    (U := testObject k U S)
    (R := CommRingCat.of (LocallyConstant S R))
    (fun T _ _ _ _ ↦ LocallyConstant.exists_retraction_of_discreteTopology hR S T)
    (isPullback_specLocallyConstant k U S e).isoPullback.symm

/-- **Sections of the coefficient sheaf over finite test objects.** Let `U` be an affine object
of `X_proét` such that every faithfully flat ind-étale `Γ(U)`-algebra has a retraction (e.g.
`Γ(U)` is w-contractible), and `S` a finite set. Then the map `Λ(π₀(U) × S) ⟶ Λ_X(U[S])` of
`AlgebraicGeometry.ProEtale.bijective_sections_testObject` is bijective. -/
theorem bijective_sections_testObject_of_finite [IsAffine U.left]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    (hR : ∀ (T : Type u) [CommRing T] [Algebra Γ(U.left, ⊤) T] [Algebra.IndEtale Γ(U.left, ⊤) T]
      [Module.FaithfullyFlat Γ(U.left, ⊤) T],
        ∃ f : T →+* Γ(U.left, ⊤), f.comp (algebraMap Γ(U.left, ⊤) T) = RingHom.id _) :
    Function.Bijective (Λ.obj.map (connectedComponentsAlongTestObjectIso k U S).hom.op ≫
      ((upperStarFromPointAlongAdjunction k).unit.app Λ).hom.app
        (op ((connectedComponentsAlong k).obj (testObject k U S))) ≫
      ((pointUpperStar ⋙ (k)^*[Ab.{u + 1}]).obj Λ).obj.map
        ((connectedComponentsAlongAdjunction k).unit.app (testObject k U S)).op) :=
  bijective_sections_testObject k U S Λ
    (bijective_toSheafify_testObject_of_finite k U S Λ hR U.left.isoSpec)

end AlgebraicGeometry.ProEtale
