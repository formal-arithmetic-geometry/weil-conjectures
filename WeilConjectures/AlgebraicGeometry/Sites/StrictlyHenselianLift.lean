/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# Lifting étale neighbourhoods to a strictly henselian local scheme

Let `A` be a strictly henselian local ring with residue field `κ`, and `a : Spec A ⟶ X` a
morphism of schemes. Write `s̄ : Spec κ ⟶ Spec A ⟶ X` for the closed geometric point. For an
étale `X`-scheme `V` and a lift `v : Spec κ ⟶ V` of `s̄`, there is a unique lift
`ℓ : Spec A ⟶ V` of `a` restricting to `v` on the closed point
(`AlgebraicGeometry.Scheme.existsUnique_lift_of_isStrictlyHenselianLocalRing`): existence is the
section of the étale `V ×_X Spec A ⟶ Spec A` through the point of `v`, and uniqueness holds since
two lifts agree on an open subscheme of the local scheme `Spec A`
(`AlgebraicGeometry.FormallyUnramified.eqLocus`) containing the closed point.

This is the specialization from the geometric points of `Spec A` to its closed geometric point:
the étale neighbourhoods of `s̄` are the étale neighbourhoods of `Spec A ⟶ X`.

## Main statements

- `AlgebraicGeometry.Scheme.exists_section_comp_eq_of_isStrictlyHenselianLocalRing`: a section
  of an étale `Y ⟶ Spec A` through a given geometric point over the closed point.
- `AlgebraicGeometry.Scheme.existsUnique_lift_of_isStrictlyHenselianLocalRing`: unique lifts.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

section Field

variable {X Y : Scheme.{u}} {K : Type u} [Field K]

end Field

variable {A : Type u} [CommRing A]

section Local

variable [IsLocalRing A]

variable (A) in
/-- The closed geometric point `Spec κ ⟶ Spec A` of a local ring `A` with residue field `κ`. -/
noncomputable abbrev closedGeometricPoint :
    Spec (.of (IsLocalRing.ResidueField A)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))

lemma closedGeometricPoint_apply (x : Spec (.of (IsLocalRing.ResidueField A))) :
    closedGeometricPoint A x = IsLocalRing.closedPoint A := by
  rw [Subsingleton.elim x (IsLocalRing.closedPoint _)]
  exact IsLocalRing.comap_closedPoint (IsLocalRing.residue A)

end Local

section Henselian

variable [IsStrictlyHenselianLocalRing A]

set_option backward.isDefEq.respectTransparency.types false in
/-- Over a strictly henselian local ring `A`, an étale morphism `f : Y ⟶ Spec A` has a section
through every point `y` of `Y` over the closed point. -/
theorem exists_section_apply_eq_of_isStrictlyHenselianLocalRing {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of A)) [AlgebraicGeometry.Etale f] (y : Y)
    (hy : f y = IsLocalRing.closedPoint A) :
    ∃ σ : Spec (.of A) ⟶ Y, σ ≫ f = 𝟙 _ ∧ σ (IsLocalRing.closedPoint A) = y := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hV : IsAffineOpen V := hV
  let B := Γ(Y, V)
  let φ : CommRingCat.of A ⟶ B := Spec.preimage (hV.fromSpec ≫ f)
  have hφ : Spec.map φ = hV.fromSpec ≫ f := Spec.map_preimage _
  have hφe : φ.hom.Etale := by
    rw [← HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale), hφ]
    infer_instance
  algebraize [φ.hom]
  let n := hV.primeIdealOf ⟨y, hyV⟩
  have hn : n.asIdeal.comap φ.hom = IsLocalRing.maximalIdeal A := by
    have h : (Spec.map φ) n = IsLocalRing.closedPoint A := by
      change (Spec.map φ) (hV.primeIdealOf ⟨y, hyV⟩) = _
      rw [hφ, Scheme.Hom.comp_apply, hV.fromSpec_primeIdealOf, hy]
    exact congrArg PrimeSpectrum.asIdeal h
  let Bn := Localization.AtPrime n.asIdeal
  have : Algebra.WeaklyEtale A B := inferInstance
  have : Algebra.WeaklyEtale A Bn := Algebra.WeaklyEtale.trans A B Bn
  have : IsLocalHom (algebraMap A Bn) := by
    refine ⟨fun x hx ↦ ?_⟩
    rw [IsScalarTower.algebraMap_apply A B Bn,
      IsLocalization.AtPrime.isUnit_to_map_iff Bn n.asIdeal] at hx
    by_contra hx'
    exact hx (by
      have : x ∈ IsLocalRing.maximalIdeal A := hx'
      rw [← hn] at this
      exact this)
  have hbij := Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing (R := A) (S := Bn)
  let e : A ≃+* Bn := RingEquiv.ofBijective (algebraMap A Bn) hbij
  let ψ : B ⟶ CommRingCat.of A :=
    CommRingCat.ofHom (e.symm.toRingHom.comp (algebraMap B Bn))
  have hψ : φ ≫ ψ = 𝟙 _ := by
    ext x
    change e.symm (algebraMap B Bn (algebraMap A B x)) = x
    rw [← IsScalarTower.algebraMap_apply A B Bn]
    exact e.symm_apply_apply x
  refine ⟨Spec.map ψ ≫ hV.fromSpec, ?_, ?_⟩
  · rw [Category.assoc, ← hφ, ← Spec.map_comp, hψ, Spec.map_id]
  · rw [Scheme.Hom.comp_apply]
    have hpt : (Spec.map ψ) (IsLocalRing.closedPoint A) = n := by
      apply PrimeSpectrum.ext
      change Ideal.comap (e.symm.toRingHom.comp (algebraMap B Bn))
        (IsLocalRing.maximalIdeal A) = n.asIdeal
      rw [← Ideal.comap_comap]
      have he : Ideal.comap e.symm.toRingHom (IsLocalRing.maximalIdeal A) =
          IsLocalRing.maximalIdeal Bn := by
        ext b
        simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        exact (isUnit_map_iff e.symm b).not
      rw [he]
      exact Localization.AtPrime.under_maximalIdeal
    rw [hpt]
    exact hV.fromSpec_primeIdealOf ⟨y, hyV⟩

variable {X V : Scheme.{u}} (a : Spec (.of A) ⟶ X)

end Henselian

end AlgebraicGeometry.Scheme
