/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.BoundaryNeighbourhood
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius.Points
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.RingTheory.InertiaIndEtale
public import WeilConjectures.WeilSheaf.BoundaryStalkGaloisInvariants

/-!
# The strict henselization at a boundary point as a pro-étale neighbourhood

Let `C₀` be an integral scheme over a finite field `k₀`, `W` an affine open with Dedekind ring
of sections `R = Γ(C₀, W)`, `x ∈ W` a point with finite residue field, `Ω` a separably closed
Galois extension of the function field `K = k(C₀)` and `Q` a maximal ideal over `x` of the
integral closure `B` of `R` in `Ω`. The ring `A = B_Q^{I_Q}` of inertia invariants is strictly
henselian and ind-étale over `R` (`Ideal.indEtale_inertiaInvariants`).

We show that `Spec A` is a weakly étale neighbourhood of the geometric point `x̄` over `x` of the
geometric fiber `C̄ = C₀ ×_{k₀} k̄`, for a suitable embedding `k̄ ⊆ A`, through the closed point of
`Spec A`. If `j : U₀ ⟶ C₀` is an open immersion with `U₀ ∩ W = D(ϖ)` for some `ϖ` in the prime
of `x`, the punctured part `Spec A ×_C̄ Ū` is the spectrum of the fixed field `K' = Ω^{I_Q}`
(`Ideal.isLocalization_away_inertiaInvariants`), and `Gal(Ω / K')` is the inertia group
(`Ideal.fixingSubgroup_fixedField_inertia`). These are the data required by
`AlgebraicGeometry.WeilSheaf.exists_injective_stalk_directImage_range_eq_invariants`, which
computes the boundary stalk of `j_* F` for a lisse Weil sheaf `F` as Galois invariants
(blueprint `lem-wf-boundary-stalk-invariants`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite IsLocalRing

namespace AlgebraicGeometry

section ClosedPoint

variable {C : Scheme.{u}} {W : C.Opens} (hW : IsAffineOpen W) (x : C.finitePoints)
  (hxW : x.1 ∈ W)

/-- The quotient of the sections over an affine open by the prime of a point with finite residue
field is finite: it embeds in the residue field. -/
lemma IsAffineOpen.finite_quotient_primeIdealOf :
    Finite (Γ(C, W) ⧸ (hW.primeIdealOf ⟨x.1, hxW⟩).asIdeal) := by
  let z : W := ⟨x.1, hxW⟩
  let _ : Algebra Γ(C, W) (C.presheaf.stalk z) := TopCat.Presheaf.algebra_section_stalk _ z
  have := hW.isLocalization_stalk z
  have : Finite (C.residueField x.1) := C.mem_finitePoints.1 x.2
  let f : Γ(C, W) →+* C.residueField x.1 :=
    (IsLocalRing.residue _).comp (algebraMap Γ(C, W) (C.presheaf.stalk z))
  have hker : RingHom.ker f = (hW.primeIdealOf z).asIdeal := by
    rw [← RingHom.comap_ker, IsLocalRing.ker_residue,
      ← Ideal.under_def, IsLocalization.AtPrime.under_maximalIdeal (C.presheaf.stalk z)
        (hW.primeIdealOf z).asIdeal]
  have : Finite (Γ(C, W) ⧸ RingHom.ker f) := Finite.of_injective _ (RingHom.kerLift_injective f)
  exact Finite.of_equiv _ (Ideal.quotEquivOfEq hker).toEquiv

/-- The prime of a point with finite residue field is maximal. -/
lemma IsAffineOpen.isMaximal_primeIdealOf :
    (hW.primeIdealOf ⟨x.1, hxW⟩).asIdeal.IsMaximal := by
  have := hW.finite_quotient_primeIdealOf x hxW
  exact Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)

end ClosedPoint

namespace Scheme.Hom

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The geometric point over a point with finite residue field lies over `Spec ι` for a
`k`-embedding `ι : κ(x) ↪ k̄`. -/
lemma exists_geometricFiberPointOfFinitePoint_comp_geometricFiberProj (x : X.finitePoints) :
    ∃ ι : X.residueField x.1 ⟶ CommRingCat.of (AlgebraicClosure k),
      ι.hom.comp (f.residueFieldAlgebraMap x.1) = algebraMap k _ ∧
      f.geometricFiberPointOfFinitePoint x ≫ f.geometricFiberProj =
        Spec.map ι ≫ X.fromSpecResidueField x.1 := by
  letI := (f.residueFieldAlgebraMap x.1).toAlgebra
  have : Finite (X.residueField x.1) := X.mem_finitePoints.1 x.2
  have : Module.Finite k (X.residueField x.1) := Module.Finite.of_finite
  exact ⟨CommRingCat.ofHom
    (IsAlgClosed.lift : X.residueField x.1 →ₐ[k] AlgebraicClosure k).toRingHom,
    RingHom.ext fun c ↦ (IsAlgClosed.lift : X.residueField x.1 →ₐ[k] AlgebraicClosure k).commutes c,
    f.geometricFiberPoint_comp_geometricFiberProj _ _ _⟩

lemma geometricFiberPointOfFinitePoint_comp_geometricFiberToAlgebraicClosure
    (x : X.finitePoints) :
    f.geometricFiberPointOfFinitePoint x ≫ f.geometricFiberToAlgebraicClosure = 𝟙 _ :=
  letI := (f.residueFieldAlgebraMap x.1).toAlgebra
  f.geometricFiberPoint_comp_geometricFiberToAlgebraicClosure _ _ _

end Scheme.Hom
section Boundary

variable {k₀ : Type u} [Field k₀] [Finite k₀] {C : Scheme.{u}} [C.Over (Spec (.of k₀))]
  [IsIntegral C] {W : C.Opens} (hW : IsAffineOpen W) [Nonempty W] [IsDedekindDomain Γ(C, W)]
  {Ω : Type u} [Field Ω] [Algebra C.functionField Ω] [Algebra Γ(C, W) Ω]
  [IsScalarTower Γ(C, W) C.functionField Ω] [IsGalois C.functionField Ω] [IsSepClosed Ω]
  (Q : Ideal (integralClosure Γ(C, W) Ω)) [Q.IsMaximal]

omit [IsDedekindDomain Γ(C, W)] [IsGalois C.functionField Ω] [IsSepClosed Ω] in
lemma injective_algebraMap_sections_of_isAffineOpen :
    Function.Injective (algebraMap Γ(C, W) Ω) := by
  have : IsFractionRing Γ(C, W) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C W hW
  rw [IsScalarTower.algebraMap_eq Γ(C, W) C.functionField Ω]
  exact (algebraMap C.functionField Ω).injective.comp (IsFractionRing.injective _ _)

omit [IsDedekindDomain Γ(C, W)] [IsSepClosed Ω] in
lemma isAlgebraic_sections_of_isAffineOpen : Algebra.IsAlgebraic Γ(C, W) Ω := by
  have : IsFractionRing Γ(C, W) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C W hW
  have : Algebra.IsAlgebraic Γ(C, W) C.functionField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors Γ(C, W))
  exact Algebra.IsAlgebraic.trans _ C.functionField Ω

omit [IsDedekindDomain Γ(C, W)] in
/-- The inertia invariants `B_Q^{I_Q}` are strictly henselian. -/
theorem isStrictlyHenselianLocalRing_inertiaInvariants_of_isAffineOpen :
    IsStrictlyHenselianLocalRing (Ideal.inertiaInvariants C.functionField Q) :=
  have := isAlgebraic_sections_of_isAffineOpen hW (Ω := Ω)
  Ideal.isStrictlyHenselianLocalRing_inertiaInvariants _ Q
    (injective_algebraMap_sections_of_isAffineOpen hW)

variable (x : C.finitePoints) (hxW : x.1 ∈ W) [Q.LiesOver (hW.primeIdealOf ⟨x.1, hxW⟩).asIdeal]

include hxW in
/-- The inertia invariants `B_Q^{I_Q}` are ind-étale over `Γ(C, W)`. -/
theorem indEtale_inertiaInvariants_of_isAffineOpen :
    Algebra.IndEtale Γ(C, W) (Ideal.inertiaInvariants C.functionField Q) := by
  have : IsFractionRing Γ(C, W) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C W hW
  have := hW.isMaximal_primeIdealOf x hxW
  have := hW.finite_quotient_primeIdealOf x hxW
  have : Finite (hW.primeIdealOf ⟨x.1, hxW⟩).asIdeal.ResidueField :=
    Finite.of_surjective _ (Ideal.bijective_algebraMap_quotient_residueField _).2
  exact Ideal.indEtale_inertiaInvariants _ (hW.primeIdealOf ⟨x.1, hxW⟩).asIdeal Q

/-- The structure map `k₀ ⟶ Γ(C, W)` of the affine chart. -/
noncomputable abbrev sectionsStructHom : k₀ →+* Γ(C, W) :=
  (Spec.preimage (hW.fromSpec ≫ (C ↘ Spec (.of k₀)))).hom

include hxW in
/-- **An algebraic closure of `k₀` in `B_Q^{I_Q}`.** There are ring maps `ε : k̄ ⟶ B_Q^{I_Q}`
compatible with the structure maps from `k₀`, and `r : B_Q^{I_Q} ⟶ k̄` with kernel the maximal
ideal, such that `r ∘ ε = id`. The map `ε` is an embedding `k̄ ⟶ Ω` over `k₀`: its image consists
of elements integral over `k₀`, which are fixed by inertia since a nonzero element integral over
`k₀` is a unit of `B`. The residue field of `B_Q^{I_Q}` is algebraic over `k₀`, hence its
embedding of `k̄` is an isomorphism, whose inverse gives `r`. -/
theorem exists_algebraicClosure_inertiaInvariants :
    ∃ (ε : AlgebraicClosure k₀ →+* Ideal.inertiaInvariants C.functionField Q)
      (r : Ideal.inertiaInvariants C.functionField Q →+* AlgebraicClosure k₀),
      r.comp ε = RingHom.id _ ∧ (∀ a, r a = 0 ↔ ¬ IsUnit a) ∧
      (algebraMap Γ(C, W) _).comp (sectionsStructHom hW) =
        ε.comp (algebraMap k₀ (AlgebraicClosure k₀)) := by
  classical
  set K := C.functionField
  set A := Ideal.inertiaInvariants K Q
  have hRΩ := injective_algebraMap_sections_of_isAffineOpen hW (Ω := Ω)
  have := isAlgebraic_sections_of_isAffineOpen hW (Ω := Ω)
  have := isStrictlyHenselianLocalRing_inertiaInvariants_of_isAffineOpen hW Q
  have := hW.isMaximal_primeIdealOf x hxW
  have := hW.finite_quotient_primeIdealOf x hxW
  -- the `k₀`-structures
  set φ₀ := sectionsStructHom (k₀ := k₀) hW
  letI : Algebra k₀ Ω := ((algebraMap Γ(C, W) Ω).comp φ₀).toAlgebra
  letI : Algebra k₀ Γ(C, W) := φ₀.toAlgebra
  have : IsScalarTower k₀ Γ(C, W) Ω := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let ε₀ : AlgebraicClosure k₀ →ₐ[k₀] Ω := IsSepClosed.lift
  have hint₀ (z : AlgebraicClosure k₀) : IsIntegral k₀ (ε₀ z) :=
    (Algebra.IsIntegral.isIntegral (R := k₀) z).map ε₀
  have hint (z : AlgebraicClosure k₀) : IsIntegral Γ(C, W) (ε₀ z) := (hint₀ z).tower_top
  -- inertia fixes the image of `ε₀`
  have hfix (z : AlgebraicClosure k₀) : ∀ σ ∈ Q.inertia Gal(Ω/K),
      σ • (⟨ε₀ z, hint z⟩ : integralClosure Γ(C, W) Ω) = ⟨ε₀ z, hint z⟩ := by
    intro σ hσ
    let σ' : Ω →ₐ[k₀] Ω :=
      { σ.toRingHom with
        commutes' c := by
          change σ (algebraMap Γ(C, W) Ω (φ₀ c)) = algebraMap Γ(C, W) Ω (φ₀ c)
          rw [IsScalarTower.algebraMap_apply Γ(C, W) K Ω, AlgEquiv.commutes] }
    set w : integralClosure Γ(C, W) Ω := σ • ⟨ε₀ z, hint z⟩ - ⟨ε₀ z, hint z⟩
    have hwQ : w ∈ Q := hσ _
    have hwint : IsIntegral k₀ (w : Ω) := ((hint₀ z).map σ').sub (hint₀ z)
    by_contra hne
    have hw0 : (w : Ω) ≠ 0 := fun h ↦ hne (sub_eq_zero.1 (Subtype.ext h))
    have hinv : IsIntegral Γ(C, W) ((w : Ω)⁻¹) :=
      (isAlgebraic_iff_isIntegral.1 hwint.isAlgebraic.inv).tower_top
    have h1 : (⟨(w : Ω)⁻¹, hinv⟩ : integralClosure Γ(C, W) Ω) * w = 1 :=
      Subtype.ext (inv_mul_cancel₀ hw0)
    exact (Ideal.IsMaximal.ne_top inferInstance)
      ((Ideal.eq_top_iff_one _).2 (h1 ▸ Q.mul_mem_left _ hwQ))
  let ε₁ : AlgebraicClosure k₀ →+* integralClosure Γ(C, W) Ω :=
    ε₀.toRingHom.codRestrict (integralClosure Γ(C, W) Ω) hint
  let ε : AlgebraicClosure k₀ →+* A :=
    ((algebraMap _ (Localization.AtPrime Q)).comp ε₁).codRestrict A fun z ↦
      (Ideal.inertiaInvariantsOfFixed K Q _ (hfix z)).2
  have hε (z : AlgebraicClosure k₀) : Ideal.inertiaInvariantsToField K Q (ε z) = ε₀ z :=
    Ideal.atPrimeToField_algebraMap Q (ε₁ z)
  -- the residue field of `A` is `k̄`
  let ρ : AlgebraicClosure k₀ →+* ResidueField A := (residue A).comp ε
  have hρ : Function.Bijective ρ := IsAlgClosed.ringHom_bijective_of_isIntegral ρ fun y ↦ by
    obtain ⟨p, hp, hpy⟩ := Ideal.isIntegralElem_residueField_inertiaInvariants K Q
      (hW.primeIdealOf ⟨x.1, hxW⟩).asIdeal y
    refine ⟨p.map (Int.castRingHom _), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, ← hpy]
    congr 1
    exact RingHom.ext_int _ _
  let θ := (RingEquiv.ofBijective ρ hρ).symm
  refine ⟨ε, θ.toRingHom.comp (residue A), ?_, fun a ↦ ?_, ?_⟩
  · ext z
    exact (RingEquiv.ofBijective ρ hρ).symm_apply_apply z
  · change θ (residue A a) = 0 ↔ _
    rw [map_eq_zero_iff θ θ.injective, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff]
  · ext c
    apply Ideal.injective_inertiaInvariantsToField K Q
    change Ideal.inertiaInvariantsToField K Q (algebraMap Γ(C, W) A (φ₀ c)) =
      Ideal.inertiaInvariantsToField K Q (ε (algebraMap k₀ (AlgebraicClosure k₀) c))
    rw [AlgHom.commutes, hε, ε₀.commutes]
    rfl

end Boundary

end AlgebraicGeometry
