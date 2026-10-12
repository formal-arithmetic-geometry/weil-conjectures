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
import Sheaf.RingTheory.FiniteTypeZDomainNormalizationFinite
import WeilConjectures.AlgebraicGeometry.Morphisms.Slicing
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
          IsUnit (n : Γ(X.obj i, ⊤))) := by sorry

end AlgebraicGeometry.Scheme
