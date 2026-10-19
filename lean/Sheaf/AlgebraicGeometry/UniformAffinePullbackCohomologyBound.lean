/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

import Sheaf.Topology.OpenModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import Sheaf.AlgebraicGeometry.ModuleCohomologySourceComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.QuasiCompactOpenInduction
import Sheaf.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import Sheaf.Topology.ModuleMayerVietoris
import Mathlib.Algebra.Category.Grp.Zero

/-! # Uniform open cohomology bounds under affine morphisms

Source: Stacks Project, Tag 01XJ, affine-cover induction.
(blueprint: lem-pc-j2-uniform-affine-pullback-cohomology-bound).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry

/-- A quasi-compact quasi-separated scheme has a bound for cohomology of all
quasi-coherent modules after every affine morphism to it.

Source: Stacks Project, Tag 01XJ, finite affine-cover induction.
(blueprint: lem-pc-j2-uniform-affine-pullback-cohomology-bound).

Proof: Induct on quasi-compact opens W of X. For an affine W, its inverse image under
an affine morphism h is affine, so positive cohomology vanishes and the bound is 1.
For W=A union B use bounds a,b,c for A,B,A intersect B, uniformly in h and F.
In degree p=q+1 at least max(max(a,b),c)+1, Mayer-Vietoris identifies every class on
the union with the image of a degree-q class on the intersection: the degree-p groups
on A and B are zero. The intersection group is zero as well, so the class vanishes.
Preimage preserves unions and intersections, making this argument uniform in h.
Apply quasi-compact-open induction and take W=X. The bound also handles empty opens,
empty schemes and the zero module, and does not assume a field or a Noetherian base. -/
theorem exists_uniform_affine_pullback_openCohomology_bound (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    ∃ n : ℕ, ∀ {Y : Scheme.{u}} (h : Y ⟶ X) [IsAffineHom h]
      (F : Y.Modules) [F.IsQuasicoherent], ∀ p : ℕ, n ≤ p →
        Subsingleton (F.H p) := by
  let P : X.Opens → Prop := fun W ↦ ∃ n : ℕ,
    ∀ {Y : Scheme.{u}} (h : Y ⟶ X) [IsAffineHom h]
      (F : Y.Modules) [F.IsQuasicoherent], ∀ p : ℕ, n ≤ p →
        IsZero ((RingedSpace.openModuleCohomology Y.toRingedSpace p (h ⁻¹ᵁ W)).obj F)
  have hP : ∀ W : X.Opens, IsCompact (W : Set X) → P W := by
    apply quasiCompactOpen_induction X P
    · intro W hW
      refine ⟨1, fun {Y} h _ F _ p hp ↦ ?_⟩
      have := subsingleton_openModuleCohomology_of_isAffineOpen Y F
        (h ⁻¹ᵁ W) (hW.preimage h) p (by omega)
      exact AddCommGrpCat.isZero_of_subsingleton _
    · intro A B _ _ hA hB hAB
      obtain ⟨a, ha⟩ := hA
      obtain ⟨b, hb⟩ := hB
      obtain ⟨c, hc⟩ := hAB
      refine ⟨max (max a b) c + 1, fun {Y} h _ F _ p hp ↦ ?_⟩
      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
      have hleft := AddCommGrpCat.subsingleton_of_isZero (ha h F (q + 1) (by omega))
      have hright := AddCommGrpCat.subsingleton_of_isZero (hb h F (q + 1) (by omega))
      have hsource := AddCommGrpCat.subsingleton_of_isZero (hc h F q (by omega))
      obtain ⟨δ, _, hexact, _⟩ := RingedSpace.module_mayerVietoris Y.toRingedSpace
      rw [Scheme.Hom.preimage_sup]
      apply AddCommGrpCat.isZero_iff_subsingleton.mpr
      refine ⟨fun x y ↦ ?_⟩
      have hx := (hexact (h ⁻¹ᵁ A) (h ⁻¹ᵁ B) F q).2.2
      have hzero : ∀ z :
          (RingedSpace.openModuleCohomology Y.toRingedSpace (q + 1)
            ((h ⁻¹ᵁ A) ⊔ (h ⁻¹ᵁ B))).obj F, z = 0 := by
        intro z
        obtain ⟨w, hw⟩ := (hx z).mp (by
          apply Prod.ext <;> exact Subsingleton.elim _ _)
        have : Subsingleton
            ((RingedSpace.openModuleCohomology Y.toRingedSpace q
              ((h ⁻¹ᵁ A) ⊓ (h ⁻¹ᵁ B))).obj F) := by
          simpa only [Scheme.Hom.preimage_inf] using hsource
        rw [← hw, Subsingleton.elim w 0, map_zero]
      exact (hzero x).trans (hzero y).symm
  obtain ⟨n, hn⟩ := hP ⊤ isCompact_univ
  refine ⟨n, fun {Y} h _ F _ p hp ↦ ?_⟩
  let : EnoughInjectives Y.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives Y.toRingedSpace).2
  let : (RingedSpace.openModuleSections Y.toRingedSpace ⊤).Additive :=
    RingedSpace.openModuleSections_additive _ _
  let I := injectiveResolution F
  let E := RingedSpace.globalSectionsFunctor Y.toRingedSpace
  let : E.Additive := RingedSpace.globalSectionsFunctor_additive _
  let B := forget₂ (ModuleCat Γ(Y, ⊤)) AddCommGrpCat
  let K := (E.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  have hz : IsZero ((RingedSpace.openModuleCohomology Y.toRingedSpace p ⊤).obj F) := by
    simpa using hn h F p hp
  let e := I.isoRightDerivedObj (RingedSpace.openModuleSections Y.toRingedSpace ⊤) p
  have hz' : IsZero ((B.mapHomologicalComplex (.up ℕ)).obj K |>.homology p) :=
    hz.of_iso e.symm
  have : Subsingleton ((RingedSpace.moduleCohomology Y.toRingedSpace p).obj F) := by
    have hz'' := hz'.of_iso ((K.sc p).mapHomologyIso B).symm
    have ht := AddCommGrpCat.subsingleton_of_isZero hz''
    let e' := I.isoRightDerivedObj E p
    exact ⟨fun x y ↦ e'.toLinearEquiv.injective (ht.elim _ _)⟩
  obtain ⟨a, _⟩ := Scheme.Modules.exists_moduleCohomology_source_comparison Y p
  exact ⟨fun x y ↦ (a F).symm.injective (Subsingleton.elim _ _)⟩

end AlgebraicGeometry
