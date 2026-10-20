/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.Morphisms.NormalNoetherianRefinement
import Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Normal Noetherian approximation of a pointed smooth family

Source: Stacks Project, Tag 0EZJ, normal approximation and family descent.
(blueprint: lem-sbc-normal-pointed-family-approximation)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

set_option linter.unusedVariables false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Descend the base, family, section, and an invertible integer simultaneously.

Source: Stacks Project, Tag 0EZJ, the limit reduction up to the choice of generic points.
(blueprint: lem-sbc-normal-pointed-family-approximation)

Proof:
1. Use absolute Noetherian approximation (Tag 01ZA). For every stage take the integral
scheme-theoretic image of the integral base and normalize that image in its fraction field.
This is finite by finiteness of normalization for finite type integer domains. The normal
base factors through each normalization. Uniqueness of this factorization supplies the
transition maps and compatibility of the projections; the projections are dominant.
The transition maps are affine since their composites with the finite normalization maps
are affine. On affine charts these rings are subrings of the rings of the base; they contain
all the original image rings, whose union is the base ring. Therefore their limit is S.
2. Descend the finitely presented smooth family, its section, and the equation saying that
it is a section by Tag 01ZM, and smoothness by Tag 0C0C. Replace the model by the open
relative component through the section (Tag 055R). The geometrically connected fibres
of the original family map into this open, so its pullback is the original family.
The model is quasi-compact: it is an open of a Noetherian finite presentation family.
3. Descend the inverse of n on a finite affine cover, and its agreement on a finite affine
cover of the overlaps, using filtered colimits of sections. Restrict to a cofiltered tail
where all these equalities hold. Define the later families and sections by base change.
This supplies cartesian transition squares, the two compatible cones, and their section
compatibility. Base change preserves smoothness and geometric connectedness; the base
cones are limiting, and base change of the fixed family shows the family cone is limiting.
All later base schemes are normal integral Noetherian qcqs, and n remains invertible. -/
theorem exists_normal_pointed_family_approximation {S C : Scheme.{u}} [CompactSpace S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S) (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤))) :
    ∃ (I : Type u) (hcat : SmallCategory I),
      letI : SmallCategory I := hcat
      ∃ (hco : IsCofiltered I) (X Y : I ⥤ Scheme.{u})
        (α : (Functor.const I).obj S ⟶ X) (γ : (Functor.const I).obj C ⟶ Y)
        (hα : IsLimit (Cone.mk S α)) (hγ : IsLimit (Cone.mk C γ))
        (p : Y ⟶ X) (τ : X ⟶ Y) (hI : ∀ i, IsIntegral (X.obj i)),
        (∀ {i j : I} (f : i ⟶ j), IsAffineHom (X.map f)) ∧
        (∀ i, IsDominant (α.app i)) ∧
        (∀ i, IsPullback c (γ.app i) (α.app i) (p.app i)) ∧
        (∀ {i j : I} (f : i ⟶ j),
          IsPullback (Y.map f) (p.app i) (p.app j) (X.map f)) ∧
        (∀ i, σ ≫ γ.app i = α.app i ≫ τ.app i) ∧
        (∀ i, IsNoetherian (X.obj i) ∧ QuasiSeparatedSpace (X.obj i) ∧
          (∀ x : X.obj i, IsIntegrallyClosed ((X.obj i).presheaf.stalk x)) ∧
          QuasiCompact (p.app i) ∧ QuasiSeparated (p.app i) ∧ Smooth (p.app i) ∧
          GeometricallyConnected (p.app i) ∧ τ.app i ≫ p.app i = 𝟙 (X.obj i) ∧
          IsUnit (n : Γ(X.obj i, ⊤))) := by
  classical
  obtain ⟨N⟩ := S.nonempty_noetherianApproximation
  obtain ⟨I, hcat, hmodel⟩ := exists_normal_noetherian_refinement hS N
  let : SmallCategory I := hcat
  obtain ⟨hco, X, α, hα, hI, hXa, hdom, hstage⟩ := hmodel
  let : IsCofiltered I := hco
  obtain ⟨i, P, p₀, τ₀, a, hpb, hσa, hpqc, hpqs, hpsm, hpconn, hsec, hn₀⟩ :=
    exists_pointed_smooth_family_stage X α hα hXa (fun j ↦ (hstage j).1)
      (fun j ↦ (hstage j).2.1) c σ hσ n hn
  let X' := Over.forget i ⋙ X
  let α' := (Cone.mk S α).whisker (Over.forget i)
  let Y := baseChangeDiagram X p₀
  let p : Y ⟶ X' := baseChangeDiagramπ X p₀
  let γcone := (baseChangeCone X (Cone.mk S α) p₀).extend hpb.flip.isoPullback.hom
  let γ := γcone.π
  have hα' : IsLimit α' :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) (Cone.mk S α)).symm hα
  have hγ : IsLimit γcone :=
    (isLimitBaseChangeCone X (Cone.mk S α) p₀ hα).ofIsoLimit
      (Cone.ext hpb.flip.isoPullback.symm (fun j ↦ by simp [γcone, Cone.extend]))
  have hγfst (j : Over i) : γ.app j ≫ pullback.fst p₀ (X.map j.hom) = a := by
    simp [γ, γcone, Cone.extend, IsPullback.isoPullback_hom_fst]
  have hγsnd (j : Over i) : γ.app j ≫ p.app j = c ≫ α.app j.left := by
    simp [γ, γcone, p, Cone.extend]
  let sectionMap (j : Over i) : X'.obj j ⟶ Y.obj j :=
    pullback.lift (X.map j.hom ≫ τ₀) (𝟙 _) (by simp [Category.assoc, hsec])
  have hτfst (j : Over i) : sectionMap j ≫ pullback.fst p₀ (X.map j.hom) =
      X.map j.hom ≫ τ₀ := by simp [sectionMap]
  have hτsnd (j : Over i) : sectionMap j ≫ p.app j = 𝟙 _ := by
    simp [sectionMap, p]
  let τ : X' ⟶ Y :=
    { app := sectionMap
      naturality := by
        intro j k f
        apply pullback.hom_ext
        · change (X.map f.left ≫ sectionMap k) ≫ pullback.fst _ _ =
            (sectionMap j ≫ Y.map f) ≫ pullback.fst _ _
          rw [Category.assoc, hτfst, Category.assoc, baseChangeDiagram_map_fst,
            hτfst, ← Category.assoc, ← X.map_comp, Over.w f]
        · change (X.map f.left ≫ sectionMap k) ≫ pullback.snd _ _ =
            (sectionMap j ≫ Y.map f) ≫ pullback.snd _ _
          simp [Y, sectionMap, X']
        }
  have hαmap (j : Over i) : α.app j.left ≫ X.map j.hom = α.app i :=
    (α.naturality j.hom).symm.trans (Category.id_comp (α.app i))
  have hcart (j : Over i) : IsPullback c (γ.app j) (α'.π.app j) (p.app j) := by
    have hr := IsPullback.of_hasPullback p₀ (X.map j.hom)
    have outer : IsPullback (γ.app j ≫ pullback.fst p₀ (X.map j.hom)) c p₀
        (α'.π.app j ≫ X.map j.hom) := by
      change IsPullback (γ.app j ≫ pullback.fst p₀ (X.map j.hom)) c p₀
        (α.app j.left ≫ X.map j.hom)
      rw [hγfst, hαmap]
      exact hpb.flip
    exact (outer.of_right (hγsnd j) hr).flip
  have hcompat (j : Over i) : σ ≫ γ.app j = α'.π.app j ≫ τ.app j := by
    change σ ≫ γ.app j = α.app j.left ≫ sectionMap j
    apply pullback.hom_ext
    · rw [Category.assoc, hγfst, Category.assoc, hτfst, ← Category.assoc, hαmap]
      exact hσa
    · change (σ ≫ γ.app j) ≫ p.app j = (α.app j.left ≫ sectionMap j) ≫ p.app j
      rw [Category.assoc, hγsnd, ← Category.assoc, hσ, Category.id_comp,
        Category.assoc, hτsnd]
      exact (Category.comp_id (α.app j.left)).symm
  refine ⟨Over i, inferInstance, inferInstance, X', Y, α'.π, γ, hα', hγ, p, τ,
    (fun j ↦ hI j.left), (fun f ↦ hXa f.left), (fun j ↦ hdom j.left),
    hcart, (fun f ↦ isPullback_baseChangeDiagram_map X p₀ f), hcompat, ?_⟩
  intro j
  have hbase := (hstage j.left)
  have hpull := IsPullback.of_hasPullback p₀ (X.map j.hom)
  refine ⟨hbase.1, hbase.2.1, hbase.2.2, ?_, ?_, ?_, ?_, hτsnd j, ?_⟩
  · exact MorphismProperty.of_isPullback hpull hpqc
  · exact MorphismProperty.of_isPullback hpull hpqs
  · exact MorphismProperty.of_isPullback hpull hpsm
  · exact MorphismProperty.of_isPullback hpull hpconn
  · simpa only [map_natCast] using hn₀.map ((X.map j.hom).appTop).hom


end AlgebraicGeometry.Scheme
