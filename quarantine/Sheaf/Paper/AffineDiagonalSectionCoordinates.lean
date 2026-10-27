/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.Paper.AffineDiagonalIntegrationConstructions
import Sheaf.AlgebraicGeometry.ConormalConeZeroSectionPullback

/-! # Geometric section coordinates for the affine diagonal

Source: smooth-purity, Agreement on the model, ordered difference and normal coordinates.
(blueprint: def-pur-affine-diagonal-section-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- The zero section of the ordered affine tower.
Source: Agreement on the model (blueprint: def-pur-affine-diagonal-section-coordinates). -/
def affineDiagonalStandardZero (B : Scheme.{u}) (d : ℕ) :
    B ⟶ affineTraceTower B d :=
  AffineSpace.zeroSection (ULift.{u} (Fin d)) B ≫ (affineTraceAffineSpaceIso B d).inv

/-- Difference coordinates carry the diagonal to the standard tower zero section.
Source: Agreement on the model
(blueprint: def-pur-affine-diagonal-section-coordinates). -/
theorem affineDiagonalTranslatedCoordinates_zero (Y : Scheme.{u}) (d : ℕ) :
    pullback.diagonal (affineDiagonalProjection Y d) ≫
      affineDiagonalTranslatedCoordinates Y d =
        affineDiagonalStandardZero (affineDiagonalSpace Y d) d := by
  apply (cancel_mono (affineTraceAffineSpaceIso (affineDiagonalSpace Y d) d).hom).mp
  simpa only [affineDiagonalStandardZero, Category.assoc, Iso.inv_hom_id,
    Category.comp_id] using (affineDiagonalTranslatedCoordinates_spec Y d).2.2.1

private theorem restrict_top {T : TopCat.{u}} (F : TopCat.Presheaf CommRingCat.{v} T)
    (U : TopologicalSpace.Opens T) (hU : U = ⊤) (h : ⊤ ≤ U) (x : F.obj (op U)) :
    F.map (homOfLE h).op x = (eqToHom (congrArg (fun U ↦ F.obj (op U)) hU)) x := by
  subst U
  change (F.map (𝟙 (op ⊤))) x = x
  exact congrArg (fun f : F.obj (op ⊤) ⟶ F.obj (op ⊤) ↦ f x) (F.map_id _)

private theorem normal_function_zero (Y : Scheme.{u}) (d : ℕ) (i : Fin d) :
    (PurityNormalBundle.zeroSection (pullback.diagonal (affineDiagonalProjection Y d))).appTop
      (affineDiagonalNormalFunction Y d i) = 0 := by
  let s := pullback.diagonal (affineDiagonalProjection Y d)
  let A := (ConormalGradedAlgebra.presentation s).algebra
  let b := ConormalGradedAlgebra.homogeneousClass s A
    (ConormalGradedAlgebra.presentation s).inclusion 1 ⊤ (affineDiagonalDifferenceLift Y d i)
  have ha := (ConormalGradedAlgebra.presentation s).augmentation.exists.choose_spec
    1 ⊤ (affineDiagonalDifferenceLift Y d i)
  simp only [Scheme.Hom.preimage_top, Nat.one_ne_zero, ↓reduceIte] at ha
  have h := congrArg (fun f ↦ f b)
    (Etale.FiniteSmoothPurity.coneZeroSection_app s ⊤)
  simp only [Scheme.Hom.preimage_top, Scheme.Hom.appLE_top_top,
    CommRingCat.comp_apply] at h
  have hA (c : A.right.obj.obj (op (s ⁻¹ᵁ ⊤))) :
      A.right.obj.map (homOfLE (show ⊤ ≤ s ⁻¹ᵁ ⊤ by simp)).op c = c := by
    exact restrict_top A.right.obj _ (Scheme.Hom.preimage_top s) _ c
  have hN (c : Γ(PurityNormalBundle.normalCone s, PurityNormalBundle.projection s ⁻¹ᵁ ⊤)) :
      (PurityNormalBundle.normalCone s).presheaf.map
          (homOfLE (show ⊤ ≤ PurityNormalBundle.projection s ⁻¹ᵁ ⊤ by simp)).op c = c := by
    exact restrict_top (PurityNormalBundle.normalCone s).presheaf _
      (Scheme.Hom.preimage_top _) _ c
  change (PurityNormalBundle.zeroSection s).appTop
    ((PurityNormalBundle.normalCone s).presheaf.map (homOfLE _).op
      ((Etale.FiniteSmoothPurity.coneAlgebraIso s).hom.right.hom.app (op ⊤)
        (A.right.obj.map (homOfLE _).op b))) = 0
  rw [hN, hA]
  exact h.trans ha


/-- The homogeneous normal coordinates preserve zero, with no sign or frame choice.
Source: Agreement on the model; degree-zero augmentation
(blueprint: def-pur-affine-diagonal-section-coordinates).
Proof: the normalized Rees comparison preserves the zero section. Pulling each
homogeneous degree-one coordinate back by that section applies the augmentation,
which kills positive degree. The affine-space hom-ext criterion then proves the
zero-section identity; this also covers the empty coordinate list. -/
theorem affineDiagonalNormalCoordinates_zero (Y : Scheme.{u}) (d : ℕ)
    (q : (pullback.diagonal (affineDiagonalProjection Y d)).ker.normalCone ≅
      PurityNormalBundle.normalCone (pullback.diagonal (affineDiagonalProjection Y d)))
    (hq : Etale.FiniteSmoothPurity.ReesConeNormalized
      (pullback.diagonal (affineDiagonalProjection Y d)) q) :
    (pullback.diagonal (affineDiagonalProjection Y d)).normalConeZeroSection ≫
      affineDiagonalNormalCoordinates Y d q =
        affineDiagonalStandardZero (affineDiagonalSpace Y d) d := by
  let p := affineDiagonalProjection Y d
  let s := pullback.diagonal p
  let B := affineDiagonalSpace Y d
  apply (cancel_mono (affineTraceAffineSpaceIso B d).hom).mp
  simp only [affineDiagonalNormalCoordinates, affineDiagonalStandardZero, B,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change s.normalConeZeroSection ≫ AffineSpace.homOfVector
    (Scheme.Hom.normalConeProj (pullback.fst p p) s)
    (fun i : ULift.{u} (Fin d) ↦ q.hom.appTop (affineDiagonalNormalFunction Y d i.down)) = _
  apply AffineSpace.hom_ext
  · simp only [Category.assoc, AffineSpace.homOfVector_over, AffineSpace.zeroSection_over]
    exact Scheme.Hom.normalConeZeroSection_normalConeProj (pullback.diagonal_fst p)
  · rintro ⟨i⟩
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.homOfVector_appTop_coord, AffineSpace.zeroSection_appTop_coord,
      ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hq.2.1]
    exact normal_function_zero Y d i

/-- The standard section invariant, defined before any integration transpose.
Source: standard-pair calculation
(blueprint: def-pur-affine-diagonal-section-coordinates). -/
def affineDiagonalStandardSection (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] (d : ℕ) :=
  letI := Dnc.compactifiable P (affineTraceProjection B d) aB
  Etale.sectionInvariant P.Coefficient (affineTraceProjection B d)
    (affineDiagonalStandardZero B d)

/-- Inverse of the canonical exceptional mate for an isomorphism of section pairs.
No trace, purity map, or DNC arrow enters this comparison.
Source: section base change (blueprint: def-pur-affine-diagonal-section-coordinates). -/
def affineDiagonalSectionCoordinates (P : PurityFiniteSetting.{u})
    {U B : Scheme.{u}} (d : ℕ) (f : U ⟶ B) [HasCompactification f] [QuasiCompact f]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ U) (e : U ⟶ affineTraceTower B d) [IsIso e]
    (he : e ≫ affineTraceProjection B d = f)
    (hs : s ≫ e = affineDiagonalStandardZero B d) :
    Etale.sectionInvariant P.Coefficient f s ≅ P.affineDiagonalStandardSection B aB d :=
  letI := affineDiagonalProjection_smooth B d
  letI := Dnc.compactifiable P (affineTraceProjection B d) aB
  letI := Dnc.invertibleExponent P (affineTraceProjection B d ≫ aB)
  (Dnc.sectionBaseChange P.Coefficient d (affineTraceProjection B d)
    (IsPullback.of_horiz_isIso ⟨he.trans (Category.comp_id f).symm⟩)
    (affineDiagonalStandardZero B d) s (hs.trans (Category.id_comp _).symm)).symm ≪≫
    (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B).app _

/-- Difference coordinates on the diagonal section invariant.
Source: Agreement on the model (blueprint: def-pur-affine-diagonal-section-coordinates). -/
def affineDiagonalSourceCoordinates (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] (d : ℕ) :=
  let p := affineDiagonalProjection Y d
  letI := affineDiagonalProjection_smooth Y d
  letI := SmoothOfRelativeDimension.smooth d p
  letI := Dnc.compactifiable P p aY
  letI := Dnc.compactifiable P (pullback.fst p p) (p ≫ aY)
  letI := (affineDiagonalTranslatedCoordinates_spec Y d).1
  P.affineDiagonalSectionCoordinates d (pullback.fst p p) (p ≫ aY)
    (pullback.diagonal p) (affineDiagonalTranslatedCoordinates Y d)
    (affineDiagonalTranslatedCoordinates_spec Y d).2.1
    (affineDiagonalTranslatedCoordinates_zero Y d)

/-- Homogeneous normal coordinates on the normal zero-section invariant.
Source: Agreement on the model (blueprint: def-pur-affine-diagonal-section-coordinates). -/
def affineDiagonalNormalSectionCoordinates (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] (d : ℕ)
    (q : (pullback.diagonal (affineDiagonalProjection Y d)).ker.normalCone ≅
      PurityNormalBundle.normalCone (pullback.diagonal (affineDiagonalProjection Y d)))
    (hq : Etale.FiniteSmoothPurity.ReesConeNormalized
      (pullback.diagonal (affineDiagonalProjection Y d)) q) :=
  let p := affineDiagonalProjection Y d
  let s := pullback.diagonal p
  letI := affineDiagonalProjection_smooth Y d
  letI := SmoothOfRelativeDimension.smooth d p
  letI := Dnc.normalQuasiCompact d (pullback.fst p p) s (pullback.diagonal_fst p)
  letI := Dnc.normalCompactifiable P d (pullback.fst p p) (p ≫ aY) s (pullback.diagonal_fst p)
  letI := (affineDiagonalNormalCoordinates_spec Y d q hq).1
  P.affineDiagonalSectionCoordinates d (Scheme.Hom.normalConeProj (pullback.fst p p) s)
    (p ≫ aY) s.normalConeZeroSection (affineDiagonalNormalCoordinates Y d q)
    (affineDiagonalNormalCoordinates_spec Y d q hq).2
    (affineDiagonalNormalCoordinates_zero Y d q hq)

end WeilConjectures.PurityFiniteSetting
