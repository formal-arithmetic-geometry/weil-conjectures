/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials

import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Sheaf.AlgebraicGeometry.CoordinateDifferentialsAffineChart
import Sheaf.RingTheory.EtaleCoordinatesOfFibreBasis

/-!
# Étaleness from prescribed coordinate differentials

Source: Stacks Project, `morphisms.tex`, Tag 02GU (lemma-etale-at-point), condition (8),
Tag 01V7 (lemma-smooth-locally-standard-smooth), and `algebra.tex`, Tag 00T7
(lemma-standard-smooth), part (2)
(blueprint: lem-pur-etale-at-point-from-differentials).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry

/-- A prescribed coordinate map on a smooth finite-type scheme over a field is étale on an
open neighbourhood of a point if its coordinate differentials form a basis of the cotangent
fibre there. `IsLocalRing.ResidueField (U.presheaf.stalk x)` is definitionally the field
`U.residueField x`. The tensor product has the residue field on the left, using the canonical
commutativity identification with the order in the source.
Source: Stacks Project, Tags 02GU(8), 01V7 and 00T7(2)
(blueprint: lem-pur-etale-at-point-from-differentials).

Proof:
1. Choose a standard smooth affine chart using
   `Scheme.exists_coordinate_differentials_affine_chart`. Its canonical fibre comparison
   identifies the given coordinate differentials with their affine algebra differentials.
2. The complementary variables of the submersive presentation give a global differential
   basis. Pull the prescribed fibre basis back through the chart comparison and reindex
   both bases by the lifted coordinate index.
3. Apply `MvPolynomial.exists_etale_aeval_localization_of_fibre_basis`. The determinant of
   the prescribed differentials in the global basis is nonzero in the fibre. Inverting it
   makes these differentials a basis and the prescribed polynomial evaluation map étale.
4. The chart's coordinate-map identity and compatibility of polynomial evaluation with
   localization identify the resulting spectrum morphism with the prescribed map.
5. The localization followed by the chart immersion is an open immersion. Its image is
   the principal open of the chosen determinant, containing the point by nonzero evaluation.
   Transport étaleness through its canonical isomorphism onto this open subscheme. -/
theorem Scheme.exists_etale_open_of_coordinate_differentials_basis
    (k : Type u) [Field k] (U : Scheme.{u}) [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [Smooth (U ↘ Spec (.of k))] (x : U) (d : ℕ) (h : Fin d → Γ(U, ⊤))
    (hbasis : ∃ b : Module.Basis (Fin d) (IsLocalRing.ResidueField (U.presheaf.stalk x))
        (IsLocalRing.ResidueField (U.presheaf.stalk x) ⊗[U.presheaf.stalk x]
          ((RingedSpace.moduleStalkFunctor U.toRingedSpace x).obj
            (U ↘ Spec (.of k)).relativeDifferentials)),
      ∀ j : Fin d, b j = TensorProduct.tmul (U.presheaf.stalk x)
        (N := (RingedSpace.moduleStalkFunctor U.toRingedSpace x).obj
          (U ↘ Spec (.of k)).relativeDifferentials)
        (1 : IsLocalRing.ResidueField (U.presheaf.stalk x))
        ((U ↘ Spec (.of k)).relativeDifferentials.presheaf.germ ⊤ x trivial
          ((U ↘ Spec (.of k)).relativeDifferentialsDerivation.d (h j)))) :
    ∃ V : U.Opens, x ∈ V ∧
      Etale (V.ι ≫ AffineSpace.homOfVector (U ↘ Spec (.of k))
        (fun j : ULift.{u} (Fin d) ↦ h j.down)) := by
  classical
  obtain ⟨W, hW, hx, hchart⟩ :=
    Scheme.exists_coordinate_differentials_affine_chart k U x d h hbasis
  let res : Γ(U, ⊤) →+* Γ(U, W) :=
    (U.presheaf.map (homOfLE le_top).op).hom
  let : Algebra k Γ(U, W) :=
    ((ΓSpecIso (.of k)).inv ≫ (U ↘ Spec (.of k)).appTop ≫
      U.presheaf.map (homOfLE le_top).op).hom.toAlgebra
  let : Algebra Γ(U, W) (IsLocalRing.ResidueField (U.presheaf.stalk x)) :=
    (U.presheaf.germ W x hx ≫ U.residue x).hom.toAlgebra
  let : Module Γ(U, W)
      ((RingedSpace.moduleStalkFunctor U.toRingedSpace x).obj
        (U ↘ Spec (.of k)).relativeDifferentials) :=
    Module.compHom _ (U.presheaf.germ W x hx).hom
  let : Algebra (MvPolynomial (ULift.{u} (Fin d)) k) Γ(U, W) :=
    (MvPolynomial.aeval (R := k) (fun j : ULift.{u} (Fin d) ↦ res (h j.down))).toRingHom.toAlgebra
  obtain ⟨r, P, hP, _, ⟨g, Φ, _, _, hΦ⟩, _, _, hmap⟩ := hchart
  have hcompl : IsCompl (Set.range (Fin.natAdd r : Fin d → Fin (r + d)))
      (Set.range P.map) := by
    rw [hP]
    constructor
    · rw [Set.disjoint_left]
      rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
      have he := congrArg Fin.val hj
      simp only [Fin.val_castAdd, Fin.val_natAdd] at he
      omega
    · rw [codisjoint_iff_le_sup]
      intro i _
      by_cases hi : i.val < r
      · exact Or.inr ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
      · exact Or.inl ⟨⟨i.val - r, by omega⟩, Fin.ext (by simp; omega)⟩
  let b := P.basisKaehlerOfIsCompl (Fin.natAdd_injective d r) hcompl
  obtain ⟨c, hc⟩ := hbasis
  let c' := c.map Φ.symm
  have hc' (j : Fin d) :
      c' j = 1 ⊗ₜ[Γ(U, W)] KaehlerDifferential.D k Γ(U, W) (res (h j)) := by
    apply Φ.injective
    simpa only [c', Module.Basis.map_apply, LinearEquiv.apply_symm_apply, hc] using
      (hΦ j).symm
  have : Algebra.IsStandardSmooth k Γ(U, W) := P.isStandardSmooth
  obtain ⟨f, hf, het⟩ := MvPolynomial.exists_etale_aeval_localization_of_fibre_basis
    (fun j : ULift.{u} (Fin d) => res (h j.down))
    (b.reindex Equiv.ulift.symm) (c'.reindex Equiv.ulift.symm)
    (fun j => by simpa using hc' j.down)
  let S := Localization.Away f
  let l : Spec (.of S) ⟶ Spec Γ(U, W) :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(U, W) S))
  let a := AffineSpace.homOfVector (U ↘ Spec (.of k))
    (fun j : ULift.{u} (Fin d) => h j.down)
  have hl : Etale (l ≫ hW.fromSpec ≫ a) := by
    have heval :
        (algebraMap Γ(U, W) S).comp
          (MvPolynomial.aeval (R := k) (fun j : ULift.{u} (Fin d) => res (h j.down))).toRingHom =
        (MvPolynomial.aeval (R := k) (fun j : ULift.{u} (Fin d) =>
          algebraMap Γ(U, W) S (res (h j.down)))).toRingHom := by
      exact congrArg AlgHom.toRingHom
        (MvPolynomial.comp_aeval (fun j : ULift.{u} (Fin d) => res (h j.down))
          (IsScalarTower.toAlgHom k Γ(U, W) S))
    rw [← hmap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, heval]
    have : Etale (Spec.map (CommRingCat.ofHom
        (MvPolynomial.aeval (R := k) (fun j : ULift.{u} (Fin d) =>
          algebraMap Γ(U, W) S (res (h j.down)))).toRingHom)) :=
      (HasRingHomProperty.Spec_iff (P := @Etale)).mpr het
    infer_instance
  let i := l ≫ hW.fromSpec
  have hrange : i.opensRange = U.basicOpen f := by
    rw [Scheme.Hom.opensRange_comp, Scheme.Hom.opensRange_localizationAway,
      hW.fromSpec_image_basicOpen]
  have hx' : x ∈ i.opensRange := by
    rw [hrange]
    exact (U.evaluation_ne_zero_iff_mem_basicOpen x hx f).mp hf
  let e := IsOpenImmersion.isoOfRangeEq i i.opensRange.ι (by simp)
  refine ⟨i.opensRange, hx', ?_⟩
  have : Etale (i ≫ a) := by simpa only [i, Category.assoc] using hl
  have hi : Etale (e.inv ≫ i ≫ a) := inferInstance
  have hfac : e.inv ≫ i = i.opensRange.ι :=
    IsOpenImmersion.isoOfRangeEq_inv_fac i i.opensRange.ι _
  simpa only [← Category.assoc, hfac] using hi

end AlgebraicGeometry
