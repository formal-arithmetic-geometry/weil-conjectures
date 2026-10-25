/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.DefectExchanges
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersion

/-!

# Embedding a principal divisor of an affine scheme into a coordinate hyperplane

Let `V` be an affine `k`-scheme of finite type and `h` a global function on `V`. Choosing
generators `g₁, …, gₙ` of `Γ(V)` over `k` and appending `h` as the last coordinate gives a closed
immersion `a : V ⟶ 𝔸ⁿ⁺¹_k` with `V(h) = a⁻¹(𝔸ⁿ × {0})` schematically
(`ProEtale.CondensedRing.exists_isClosedImmersion_comap_coordinateHyperplane`; proof of blueprint
`det-sp-zero-section-vanishing`).

This file also defines the affine space `𝔸ⁿ⁺¹_k` as a `k`-scheme
(`ProEtale.CondensedRing.affineSpaceOver`) and its coordinate hyperplane `𝔸ⁿ × {0}`
(`ProEtale.CondensedRing.coordinateHyperplane`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (k : Type u) [Field k]

/-- The affine space `𝔸ⁿ⁺¹_k` as a `k`-scheme. -/
noncomputable def affineSpaceOver (n : ℕ) : Over (Spec (.of k)) :=
  Over.mk (𝔸(ULift.{u} (Fin (n + 1)); Spec (.of k)) ↘ Spec (.of k))

instance (n : ℕ) : IsAffine (affineSpaceOver k n).left :=
  inferInstanceAs (IsAffine 𝔸(ULift.{u} (Fin (n + 1)); Spec (.of k)))

instance (n : ℕ) : LocallyOfFiniteType (affineSpaceOver k n).hom :=
  inferInstanceAs (LocallyOfFiniteType (𝔸(ULift.{u} (Fin (n + 1)); Spec (.of k)) ↘ Spec (.of k)))

instance (n : ℕ) : QuasiCompact (affineSpaceOver k n).hom :=
  inferInstanceAs (QuasiCompact (𝔸(ULift.{u} (Fin (n + 1)); Spec (.of k)) ↘ Spec (.of k)))

instance (n : ℕ) : IsSeparated (affineSpaceOver k n).hom :=
  inferInstanceAs (IsSeparated (𝔸(ULift.{u} (Fin (n + 1)); Spec (.of k)) ↘ Spec (.of k)))

/-- The coordinate hyperplane `𝔸ⁿ × {0} ⊆ 𝔸ⁿ⁺¹_k`, the vanishing locus of the last coordinate. -/
noncomputable def coordinateHyperplane (n : ℕ) : (affineSpaceOver k n).left.IdealSheafData :=
  IdealSheafData.ofIdealTop (Ideal.span {AffineSpace.coord (Spec (.of k)) (ULift.up (Fin.last n))})

variable {k}

/-- **A principal divisor of an affine scheme is the inverse image of a coordinate hyperplane**
(proof of blueprint `det-sp-zero-section-vanishing`): for an affine `k`-scheme `V` of finite type
and a global function `h`, there is a closed immersion `a : V ⟶ 𝔸ⁿ⁺¹_k` with
`a⁻¹(𝔸ⁿ × {0}) = V(h)` schematically. -/
theorem exists_isClosedImmersion_comap_coordinateHyperplane {V : Over (Spec (.of k))}
    [IsAffine V.left] [LocallyOfFiniteType V.hom] (h : Γ(V.left, ⊤)) :
    ∃ (n : ℕ) (a : V ⟶ affineSpaceOver k n), IsClosedImmersion a.left ∧
      (coordinateHyperplane k n).comap a.left =
        IdealSheafData.ofIdealTop (Ideal.span {h}) := by
  have hft : V.hom.appTop.hom.FiniteType :=
    HasRingHomProperty.appTop @LocallyOfFiniteType V.hom inferInstance
  let := V.hom.appTop.hom.toAlgebra
  obtain ⟨s, hs⟩ := hft.out
  let g : Fin s.card → Γ(V.left, ⊤) := fun i ↦ (s.equivFin.symm i).1
  let v : ULift.{u} (Fin (s.card + 1)) → Γ(V.left, ⊤) := fun i ↦ Fin.lastCases h g i.down
  let a : V ⟶ affineSpaceOver k s.card := Over.homMk (AffineSpace.homOfVector V.hom v)
    (AffineSpace.homOfVector_over _ _)
  refine ⟨s.card, a, ?_, ?_⟩
  · refine IsClosedImmersion.of_surjective_of_isAffine _ fun y ↦ ?_
    -- the range of `a^*` is a `k`-subalgebra containing the generators
    let R : Subalgebra Γ(Spec (.of k), ⊤) Γ(V.left, ⊤) :=
      { (a.left.appTop.hom.range) with
        algebraMap_mem' := fun r ↦
          ⟨(𝔸(ULift.{u} (Fin (s.card + 1)); Spec (.of k)) ↘ Spec (.of k)).appTop r,
          by
            change ((𝔸(ULift.{u} (Fin (s.card + 1)); Spec (.of k)) ↘ Spec (.of k)).appTop ≫
              a.left.appTop) r = V.hom.appTop r
            rw [← Scheme.Hom.comp_appTop]
            exact congrArg (fun f ↦ f.appTop r) (Over.w a)⟩ }
    have hR : Algebra.adjoin Γ(Spec (.of k), ⊤) (s : Set Γ(V.left, ⊤)) ≤ R := by
      refine Algebra.adjoin_le fun x hx ↦ ?_
      refine ⟨AffineSpace.coord _ (ULift.up (s.equivFin ⟨x, hx⟩).castSucc), ?_⟩
      change (AffineSpace.homOfVector V.hom v).appTop _ = x
      rw [AffineSpace.homOfVector_appTop_coord]
      simp [v, g]
    have hy : y ∈ R := hR (hs ▸ Algebra.mem_top)
    exact hy
  · refine IdealSheafData.ext_of_isAffine ?_
    rw [IdealSheafData.ideal_top_comap_of_isAffine, coordinateHyperplane,
      IdealSheafData.ideal_top_ofIdealTop, IdealSheafData.ideal_top_ofIdealTop, Ideal.map_span,
      Set.image_singleton]
    congr 2
    change (AffineSpace.homOfVector V.hom v).appTop _ = h
    rw [AffineSpace.homOfVector_appTop_coord]
    simp [v]

variable {ℓ : ℕ} [Fact ℓ.Prime] (k' : Type u) [Field k'] [Algebra k k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- **Vanishing of the defect for a coordinate hyperplane** (blueprint
`det-sp-zero-section-affine-space`): for `X = 𝔸ⁿ⁺¹_k` and `Z = 𝔸ⁿ × {0}`, the defect
`C_{X,Z}(L)` vanishes for every bounded constructible `L`. -/
theorem isZero_specializationDefect_affineSpace (n : ℕ)
    (L : Dᵇc((affineSpaceOver k n).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsZero (specializationDefect (affineSpaceOver k n) (coordinateHyperplane k n) k'
      (Profinite.padicAlgClRingObj ℓ) L.obj) :=
  sorry

variable {k'} in
/-- Over a closed immersion `f : X' ⟶ X`, the map `N_⊥ Z' ⟶ N_⊥ Z` of special fibres of the
constant families of the centres is a closed immersion (it is `f_Z ⊗ k'`). -/
lemma isClosedImmersion_centreSpecialFibreMap {X X' : Over (Spec (.of k))} (f : X' ⟶ X)
    [IsClosedImmersion f.left] (I : X.left.IdealSheafData) :
    IsClosedImmersion (centreSpecialFibreMap f I k').left :=
  sorry

/-- The defect vanishes for the inverse image of a coordinate hyperplane under a closed immersion
`a : V ⟶ 𝔸ⁿ⁺¹_k`: proper exchange gives `C_{𝔸, 𝔸ⁿ × 0}(Ra_* L) ≅ Ra_{Z*} C_{V,a⁻¹(𝔸ⁿ × 0)}(L)`, the
left side vanishes by `ProEtale.CondensedRing.isZero_specializationDefect_affineSpace`, and
`Ra_{Z*}` is fully faithful since `a_Z` is a closed immersion. -/
theorem isZero_specializationDefect_comap_coordinateHyperplane {V : Over (Spec (.of k))}
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom] {n : ℕ}
    (a : V ⟶ affineSpaceOver k n) [IsClosedImmersion a.left]
    (L : Dᵇc(V.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsZero (specializationDefect V ((coordinateHyperplane k n).comap a.left) k'
      (Profinite.padicAlgClRingObj ℓ) L.obj) := by
  set aZ := (centreSpecialFibreMap a (coordinateHyperplane k n) k').left
  set Λ := Profinite.padicAlgClRingObj ℓ
  have e := (nonempty_specializationDefect_lowerStar_iso (ℓ := ℓ) a (coordinateHyperplane k n)
    k' L).some
  have e' := (nonempty_specializationDefect_iso (affineSpaceOver k n) (coordinateHyperplane k n)
    k' Λ ((boundedConstructibleLowerStarCompatibility Λ ℓ a).app L)).some
  have h₀ : IsZero (R((aZ)_*⟦Λ⟧).obj
      (specializationDefect V ((coordinateHyperplane k n).comap a.left) k' Λ L.obj)) :=
    ((isZero_specializationDefect_affineSpace (ℓ := ℓ) k' n
      ((boundedConstructibleLowerStar Λ ℓ a).obj L)).of_iso e'.symm).of_iso e.symm
  have : IsClosedImmersion aZ :=
    isClosedImmersion_centreSpecialFibreMap (k' := k') a (coordinateHyperplane k n)
  have h₁ := L((aZ)^*⟦Λ⟧).map_isZero h₀
  have : IsIso (derivedUpperStarLowerStarAdjunction Λ aZ).counit :=
    isIso_derivedUpperStarLowerStarAdjunction_counit_of_isClosedImmersion Λ aZ
  have e₁ := asIso (Adjunction.counit (derivedUpperStarLowerStarAdjunction Λ aZ) |>.app
    (specializationDefect V ((coordinateHyperplane k n).comap a.left) k' Λ L.obj))
  exact h₁.of_iso e₁.symm

/-- The defect vanishes for a principal divisor `V(h)` of an affine `k`-scheme of finite type
(proof of blueprint `det-sp-zero-section-vanishing`): embed `V(h) ⊆ V` into a coordinate
hyperplane of an affine space by a closed immersion
(`ProEtale.CondensedRing.exists_isClosedImmersion_comap_coordinateHyperplane`). -/
theorem isZero_specializationDefect_ofIdealTop_span_singleton {V : Over (Spec (.of k))}
    [IsAffine V.left] [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (h : Γ(V.left, ⊤)) (L : Dᵇc(V.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsZero (specializationDefect V (IdealSheafData.ofIdealTop (Ideal.span {h})) k'
      (Profinite.padicAlgClRingObj ℓ) L.obj) := by
  obtain ⟨n, a, ha, hI⟩ := exists_isClosedImmersion_comap_coordinateHyperplane h
  exact hI ▸ isZero_specializationDefect_comap_coordinateHyperplane k' a L

end AlgebraicGeometry.ProEtale.CondensedRing
