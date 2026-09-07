/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.RingHom.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Finite étale schemes over a separably closed field

A scheme `X` finite étale over a field `K` is affine, and `Γ(X, ⊤)` is an étale `K`-algebra. If
`K` is separably closed, such an algebra is a finite product of copies of `K`, one factor for
each point of `X` (`Algebra.FormallyEtale.equivPiOfIsSepClosed`). Since `X` is a finite discrete
space of closed points (see `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite`), the
rank of `X` over `K` is exactly the number of points of `X`. If `K` is algebraically closed these
points are moreover exactly the `K`-rational points of `X`.

## Main results

- `AlgebraicGeometry.presheafObjAlgEquivPi`: over a separably closed field `K`, the global
  sections of a finite étale `K`-scheme `X` are the `K`-valued functions on the points of `X`.
- `AlgebraicGeometry.Scheme.Hom.finrank_eq_natCard`: over a separably closed field, the rank of a
  finite étale morphism `X ⟶ Spec K` is the number of points of `X`.
- `AlgebraicGeometry.pointEquiv`: over an algebraically closed field `K`, the `K`-points of a
  finite étale `K`-scheme `X` are in bijection with the points of `X`, so their number is the
  rank of `X` over `K` (`AlgebraicGeometry.natCard_pointHom_eq_finrank`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- The global sections of a scheme étale over `Spec K` form an étale `K`-algebra. -/
instance algebra_etale_presheafObj [X.Over (Spec (.of K))] [IsAffine X]
    [Etale (X ↘ Spec (.of K))] : Algebra.Etale K Γ(X, ⊤) := by
  rw [← RingHom.etale_algebraMap]
  have h : Etale (Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, ⊤)))) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @Etale X.isoSpec.hom,
      isoSpec_hom_comp_specMap_algebraMap]
    infer_instance
  rwa [HasRingHomProperty.Spec_iff (P := @Etale)] at h

section IsSepClosed

variable (K X) [X.Over (Spec (.of K))] [IsAffine X] [IsFinite (X ↘ Spec (.of K))]
  [Etale (X ↘ Spec (.of K))] [IsSepClosed K]

/-- Over a separably closed field `K`, the global sections of a finite étale `K`-scheme `X` are
the `K`-valued functions on the points of `X`. This is
`Algebra.FormallyEtale.equivPiOfIsSepClosed` for `Γ(X, ⊤)`. -/
noncomputable def presheafObjAlgEquivPi : Γ(X, ⊤) ≃ₐ[K] (PrimeSpectrum Γ(X, ⊤) → K) :=
  Algebra.FormallyEtale.equivPiOfIsSepClosed K Γ(X, ⊤)

/-- Over a separably closed field `K`, the `K`-dimension of the ring of global sections of a
finite étale `K`-scheme `X` is the number of points of `X`. -/
lemma finrank_presheafObj : Module.finrank K Γ(X, ⊤) = Nat.card X := by
  have := isArtinianRing_presheafObj K X
  have e : ↥X ≃ₜ PrimeSpectrum Γ(X, ⊤) := Scheme.homeoOfIso X.isoSpec
  have := Fintype.ofFinite (PrimeSpectrum Γ(X, ⊤))
  rw [(presheafObjAlgEquivPi K X).toLinearEquiv.finrank_eq, Module.finrank_pi,
    Nat.card_eq_of_bijective _ e.bijective, Nat.card_eq_fintype_card]

end IsSepClosed

/-- Over a separably closed field `K`, the rank of a finite étale morphism `X ⟶ Spec K` is the
number of points of `X`. -/
lemma Scheme.Hom.finrank_eq_natCard [IsSepClosed K] (f : X ⟶ Spec (.of K)) [IsFinite f] [Etale f]
    (y : Spec (.of K)) : f.finrank y = Nat.card X := by
  let : X.Over (Spec (.of K)) := ⟨f⟩
  have : IsFinite (X ↘ Spec (.of K)) := ‹IsFinite f›
  have : Etale (X ↘ Spec (.of K)) := ‹Etale f›
  have : IsAffine X := isAffine_of_isFinite_over_field f
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, ⊤)))) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite X.isoSpec.hom,
      isoSpec_hom_comp_specMap_algebraMap]
    infer_instance
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, ⊤)))) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @Flat X.isoSpec.hom,
      isoSpec_hom_comp_specMap_algebraMap]
    infer_instance
  have hf : f = X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, ⊤))) :=
    (isoSpec_hom_comp_specMap_algebraMap K X).symm
  rw [hf, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_algebraMap,
    Module.rankAtStalk_eq_finrank_of_free, finrank_presheafObj K X]
  simp

section IsAlgClosed

variable [IsAlgClosed K] (f : X ⟶ Spec (.of K)) [IsFinite f] [Etale f]

/-- Over an algebraically closed field `K`, the `K`-points of a finite étale `K`-scheme `X` are
in bijection with the points of `X`. -/
noncomputable def pointEquiv : {p : Spec (.of K) ⟶ X // p ≫ f = 𝟙 _} ≃ X :=
  (pointEquivClosedPoint f).trans <|
    (Equiv.setCongr (Set.eq_univ_of_forall fun x ↦
      isClosed_singleton_of_isFinite_over_field f x)).trans (Equiv.Set.univ X)

/-- Over an algebraically closed field `K`, the number of `K`-points of a finite étale
`K`-scheme `X` is the rank of `X` over `K`. -/
lemma natCard_pointHom_eq_finrank (y : Spec (.of K)) :
    Nat.card {p : Spec (.of K) ⟶ X // p ≫ f = 𝟙 _} = f.finrank y := by
  rw [Nat.card_congr (pointEquiv f), Scheme.Hom.finrank_eq_natCard f y]

end IsAlgClosed

end AlgebraicGeometry
