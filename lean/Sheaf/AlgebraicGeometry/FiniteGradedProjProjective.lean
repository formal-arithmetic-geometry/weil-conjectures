/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Sheaf.RingTheory.VeroneseGradedRing
public import Mathlib.Algebra.Field.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Affine

import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.VeroneseGeneration
import Sheaf.AlgebraicGeometry.VeroneseProjIso
import Sheaf.TraceFormula.ProjQcOpenTwistAmple
import WeilConjectures.AlgebraicGeometry.AmpleImmersionAffineBase
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Projectivity of a finite graded algebra with finite degree zero

Source: Stacks Project, Tags 0EGH, 0B5J, 01N0, 0B3I, 087S and 01WE
(blueprint: lem-sfb-finite-graded-proj-projective).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

private theorem finite_proj_hprojective {k R : Type u} [Field k] [CommRing R]
    [Algebra k R] (𝒜 : ℕ → Submodule k R) [GradedRing 𝒜]
    [Algebra.FiniteType k R] [FiniteDimensional k (𝒜 0)] :
    IsHProjective (Proj.toSpecOfAlgebra 𝒜) := by
  have : IsScalarTower k (𝒜 0) R := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : Algebra.FiniteType (𝒜 0) R :=
    Algebra.FiniteType.of_restrictScalars_finiteType k (𝒜 0) R
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k (𝒜 0)))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have : IsProper (Proj.toSpecOfAlgebra 𝒜) := by
    unfold Proj.toSpecOfAlgebra
    infer_instance
  have : CompactSpace (Proj 𝒜) :=
    QuasiCompact.compactSpace_of_compactSpace (Proj.toSpecOfAlgebra 𝒜)
  obtain ⟨e, he, h⟩ := exists_common_degree_twist_ample 𝒜 (𝟙 (Proj 𝒜))
  obtain ⟨hL, hample, _⟩ := h 1 Nat.zero_lt_one
  let L := (Proj.twist 𝒜 (Int.ofNat (e * 1))).restrict (𝟙 (Proj 𝒜))
  have : L.IsInvertible := hL
  obtain ⟨d, hd, n, i, hi, hif, _⟩ :=
    Scheme.Modules.IsAmple.exists_immersion_affine_base k (Proj 𝒜)
      (Proj.toSpecOfAlgebra 𝒜) L hample
  have : IsImmersion i := hi
  have : UniversallyClosed (i ≫ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)) ↘
      Spec (.of k)) := hif.symm ▸ inferInstance
  have hclosed : IsClosedImmersion i :=
    IsClosedImmersion.of_comp_of_isSeparated i
      (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)) ↘ Spec (.of k))
  exact ⟨⟨ULift.{u} (Fin (n + 1)), inferInstance, i, hclosed, hif⟩⟩

/-- Sufficiently divisible Veronese algebras are generated in degree one, their Proj is
canonically the original Proj, and that Proj is finite type and H-projective over `k`
(its structure morphism is `Proj.toSpecOfAlgebra 𝒜 : Proj 𝒜 ⟶ Spec R₀ ⟶ Spec k`).
The canonical isomorphism is specified on every standard affine chart: its ring map sends
`a/s^q` to the identical fraction in the original ring's localization.
Source: Stacks Project, Tags 0EGH, 0B5J, 01N0, 0B3I, 087S and 01WE
(blueprint: lem-sfb-finite-graded-proj-projective).

Proof: Finite generation over `k` implies finite generation over `R₀`. Apply the
weighted-monomial Veronese generation theorem and the canonical Veronese Proj
isomorphism. Independently, Mathlib proves that Proj is proper over `R₀`, and
`Spec R₀ → Spec k` is finite. Thus Proj is proper and quasi-compact over `k`.
A common positive twist on this quasi-compact Proj is invertible and ample.
The affine-base immersion theorem embeds it into finite projective space over `k`;
properness upgrades that immersion to a closed immersion. H-projectivity implies
the remaining finite-type and quasi-compact assertions, including the empty case. -/
theorem finite_graded_proj_projective {k R : Type u} [Field k] [CommRing R]
    [Algebra k R] (𝒜 : ℕ → Submodule k R) [GradedRing 𝒜]
    [Algebra.FiniteType k R] [FiniteDimensional k (𝒜 0)] :
    (∃ D : ℕ+, ∀ d : ℕ+, (D : ℕ) ∣ (d : ℕ) →
      (∀ (n : ℕ) (a : R), a ∈ 𝒜 (n * (d : ℕ)) →
        a ∈ Subring.closure ((𝒜 0 : Set R) ∪ (𝒜 (d : ℕ) : Set R))) ∧
      ∃ e : Proj 𝒜 ≅ Proj (GradedAlgebra.veroneseGrade 𝒜 d),
        ∀ (m : ℕ) (s : GradedAlgebra.veroneseSubring 𝒜 d)
          (hs : s ∈ GradedAlgebra.veroneseGrade 𝒜 d m) (hm : 0 < m),
          ∃ α : HomogeneousLocalization.Away (GradedAlgebra.veroneseGrade 𝒜 d) s →+*
              HomogeneousLocalization.Away 𝒜 (s : R),
            (∀ (q : ℕ) (a : GradedAlgebra.veroneseSubring 𝒜 d)
                (ha : a ∈ GradedAlgebra.veroneseGrade 𝒜 d (q • m)),
              (α (HomogeneousLocalization.Away.mk _ hs q a ha)).val =
                (Localization.mk (a : R) ⟨(s : R) ^ q, ⟨q, rfl⟩⟩ :
                  Localization.Away (s : R))) ∧
            Proj.awayι 𝒜 (s : R) hs (Nat.mul_pos hm d.pos) ≫ e.hom =
              Spec.map (CommRingCat.ofHom α) ≫
                Proj.awayι (GradedAlgebra.veroneseGrade 𝒜 d) s hs hm) ∧
    LocallyOfFiniteType (Proj.toSpecOfAlgebra 𝒜) ∧
    QuasiCompact (Proj.toSpecOfAlgebra 𝒜) ∧
    IsHProjective (Proj.toSpecOfAlgebra 𝒜) := by
  have : IsScalarTower k (𝒜 0) R := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : Algebra.FiniteType (𝒜 0) R :=
    Algebra.FiniteType.of_restrictScalars_finiteType k (𝒜 0) R
  obtain ⟨D, hD⟩ := GradedAlgebra.exists_veronese_generators 𝒜
  refine ⟨⟨D, fun d hd => ⟨hD d hd, ?_⟩⟩, ?_⟩
  · exact exists_veronese_proj_iso 𝒜 d
  · have : IsHProjective (Proj.toSpecOfAlgebra 𝒜) := finite_proj_hprojective 𝒜
    exact ⟨inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry
