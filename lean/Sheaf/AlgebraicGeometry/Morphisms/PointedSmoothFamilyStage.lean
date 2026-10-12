/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.Morphisms.Slicing

/-!
# Descent of a pointed smooth family to one Noetherian stage

Source: Stacks Project, Tag 0EZJ, pointed family descent paragraph.
(blueprint: lem-sbc-pointed-smooth-family-stage)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- Descend only a single family and section, together with an invertible integer.
The inverse system and its normality are supplied as input, not constructed here.

Source: Stacks Project, Tag 0EZJ, family descent paragraph; Tags 01ZM, 0C0C and 055R.
(blueprint: lem-sbc-pointed-smooth-family-stage)

Proof: Smoothness implies local finite presentation, so the qcqs family has finite
presentation. Apply finite-presentation descent to obtain a cartesian model at a stage.
Descend the section as a morphism between finitely presented objects by 01ZM(2), then
its section identity by 01ZM(3), passing to a common later stage. Descend smoothness by
0C0C. Replace the model by the open fibre component containing the descended section,
using the smooth section-component theorem (055R and 04KV). This open has geometrically
connected fibres. Every geometric fibre of C is connected and contains its section point,
so the comparison from C lands in this open: after geometric field extension the image
of a connected fibre lies in the component of the section. Hence the restricted model
still pulls back to C. The model is Noetherian, being of finite presentation over a
Noetherian stage, and its open component is therefore quasi-compact and quasi-separated.
Finally descend the inverse of n on a finite affine cover of the base stage. Sections on
these charts are filtered colimits of sections on their inverse images. The inverse
and its equations, and agreement on the finite affine covers of the pairwise overlaps,
therefore occur at a common later stage. Gluing gives an inverse to n there. Base change
preserves all the model's properties and the section identity. -/
theorem exists_pointed_smooth_family_stage {I : Type u} [SmallCategory I]
    [IsCofiltered I] {S C : Scheme.{u}}
    (X : I ⥤ Scheme.{u}) (α : (Functor.const I).obj S ⟶ X)
    (hα : IsLimit (Cone.mk S α))
    (hXa : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (X.map f))
    (hN : ∀ i, IsNoetherian (X.obj i))
    (hqs : ∀ i, QuasiSeparatedSpace (X.obj i))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S) (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤))) :
    ∃ (i : I) (P : Scheme.{u}) (p : P ⟶ X.obj i) (τ : X.obj i ⟶ P) (a : C ⟶ P),
      IsPullback c a (α.app i) p ∧ σ ≫ a = α.app i ≫ τ ∧
      QuasiCompact p ∧ QuasiSeparated p ∧ Smooth p ∧ GeometricallyConnected p ∧
      τ ≫ p = 𝟙 (X.obj i) ∧ IsUnit (n : Γ(X.obj i, ⊤)) := by sorry

end AlgebraicGeometry.Scheme
