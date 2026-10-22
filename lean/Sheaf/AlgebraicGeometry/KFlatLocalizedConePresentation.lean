/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Sheaf.Algebra.Homology.KFlat
import WeilConjectures.Algebra.Homology.KFlatResolution

/-! # K-flat cone representatives of localized homotopy triangles

Source: Stacks Project, Tags 06YS and 06YJ, replacement by K-flat complexes
in the mapping-cone proof of derived pullback exactness.
(blueprint: lem-sc-kflat-localized-cone-presentation).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Pretriangulated
namespace AlgebraicGeometry

/-- A distinguished homotopy triangle becomes isomorphic, after localization, to
an explicit cone triangle of a morphism between K-flat complexes.

Source: Stacks Project, Tag 06YS, termwise surjective K-flat resolutions; Tag
06YJ, K-flat computation of derived pullback and its mapping-cone argument.
(blueprint: lem-sc-kflat-localized-cone-presentation).

Proof. Localize the given distinguished triangle. Resolve a representative of
its second object by a K-flat Q, obtaining an isomorphism eQ from the localization
of Q to that second object. Write its first arrow followed by eQ inverse as a
right fraction for the homotopy quasi-isomorphisms. Resolve the domain R of the
fraction by a K-flat P. Compose the resolution with the numerator and choose a
cochain representative p : P → Q of the resulting homotopy morphism. The
resolution and denominator become invertible after localization; their composite
gives eP from the localization of P to the first object. The right-fraction
identity gives the square between p and the original first arrow. Both triangles
are distinguished, so the triangulated axiom completing a square extends eP and
eQ to an isomorphism of triangles; the third component is invertible by the
five lemma. Take its inverse. No lifting property for K-flat objects is used.
The argument works for unbounded complexes, zero complexes and the empty scheme. -/
theorem exists_kFlat_localized_cone_presentation (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (T₀ : Triangle (HomotopyCategory
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)))
    (hT₀ : T₀ ∈ distTriang (HomotopyCategory
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))) :
    ∃ (P Q : CochainComplex
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) (p : P ⟶ Q),
      CochainComplex.IsAcyclicTensorKFlat (R := Y.sheaf) P ∧
      CochainComplex.IsAcyclicTensorKFlat (R := Y.sheaf) Q ∧
      Nonempty (DerivedCategory.Qh.mapTriangle.obj T₀ ≅
        DerivedCategory.Qh.mapTriangle.obj (CochainComplex.mappingCone.triangleh p))  := by
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let L : HomotopyCategory A (ComplexShape.up ℤ) ⥤ schemeDerivedCategory Y :=
    DerivedCategory.Qh
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  obtain ⟨B, hB⟩ := HomotopyCategory.quotient_obj_surjective T₀.obj₂
  obtain ⟨Q, t, hQ, _, ht, _⟩ := CochainComplex.exists_isKFlatResolution (R := Y.sheaf) B
  have ht' : W (q.map t) := (HomotopyCategory.quotient_map_mem_quasiIso_iff t).2 ht
  have : IsIso (L.map (q.map t)) := Localization.inverts L W _ ht'
  let eQ : L.obj (q.obj Q) ≅ (L.mapTriangle.obj T₀).obj₂ :=
    asIso (L.map (q.map t)) ≪≫ L.mapIso (eqToIso hB)
  obtain ⟨α, hα⟩ := Localization.exists_rightFraction L W
    ((L.mapTriangle.obj T₀).mor₁ ≫ eQ.inv)
  obtain ⟨R, hR⟩ := HomotopyCategory.quotient_obj_surjective α.X'
  obtain ⟨P, s, hP, _, hs, _⟩ := CochainComplex.exists_isKFlatResolution (R := Y.sheaf) R
  let r : q.obj P ⟶ α.X' := q.map s ≫ eqToHom hR
  have hr : W r := by
    have hs' := (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs
    exact W.comp_mem _ _ hs' (W.of_isIso (eqToHom hR))
  have : IsIso (L.map r) := Localization.inverts L W _ hr
  have : IsIso (L.map α.s) := Localization.inverts L W _ α.hs
  let eP : L.obj (q.obj P) ≅ (L.mapTriangle.obj T₀).obj₁ :=
    asIso (L.map r) ≪≫ asIso (L.map α.s)
  obtain ⟨p, hp⟩ := q.map_surjective (r ≫ α.f)
  refine ⟨P, Q, p, hP, hQ, ⟨?_⟩⟩
  apply Iso.symm
  refine isoTriangleOfIso₁₂ _ _
    (L.map_distinguished _ (HomotopyCategory.mappingCone_triangleh_distinguished p))
    (L.map_distinguished _ hT₀) eP eQ ?_
  change L.map (q.map p) ≫ eQ.hom = (L.map r ≫ L.map α.s) ≫ _
  rw [hp, L.map_comp]
  have h := α.map_s_comp_map L (Localization.inverts L W)
  rw [← hα] at h
  calc
    (L.map r ≫ L.map α.f) ≫ eQ.hom =
        L.map r ≫ (L.map α.s ≫
          ((L.mapTriangle.obj T₀).mor₁ ≫ eQ.inv)) ≫ eQ.hom := by
      rw [h]
      simp only [Category.assoc]
    _ = (L.map r ≫ L.map α.s) ≫ (L.mapTriangle.obj T₀).mor₁ := by
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry
