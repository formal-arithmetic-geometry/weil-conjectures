/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.SecSmoothPurity.ReductionDirectImageComparison
public import Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange
public import Sheaf.Paper.EtaleDerivedScalarTensor
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension
import Sheaf.SecSmoothPurity.IntrinsicCoefficientSiteMate

/-! # Proper finite coefficient extension in intrinsic coordinates

Source: Stacks Project, more-etale.tex, Tag 0GL6, proper case, and Tag 09A6.
(blueprint: lem-sp-proper-intrinsic-finite-coefficient-extension).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

private theorem intrinsicCoefficientSiteDirectImageComparison_isIso
    (A : Type u) [CommRing A] [Finite A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (J : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) X)
    (hJ : ∃ n : ℤ, J.IsGE n) :
    IsIso ((intrinsicCoefficientSiteDirectImageComparison A f).app J) := by
  have := directImageComparisonAmbient_isIso (ULift.{u + 1, u} A) f J hJ
  dsimp only [intrinsicCoefficientSiteDirectImageComparison, NatTrans.comp_app,
    whiskerRight_app, whiskerLeft_app]
  infer_instance

/-- Proper finite coefficient extension on a retained ordinary etale origin.
Both lower-bound hypotheses concern the actual objects, and impose no flatness
or finite projective dimension on the coefficient map.
Source: Stacks Project, Tag 0GL6, proper case, and Tag 09A6.
(blueprint: lem-sp-proper-intrinsic-finite-coefficient-extension).

Proof: use intrinsicCoefficientSiteMate for the normalized coefficient/site square.
The two lower bounds make its A and B direct-image comparison components invertible
by the bounded-below qcqs site comparison, since a proper map is qcqs. The published
properFiniteCoefficientExtension makes the etale coefficient mate invertible over
Noetherian schemes. The scalar presentation boundaries are isomorphisms. Consequently
the right side of the square is invertible. Rewrite the left side by this square,
and cancel its two invertible boundaries to obtain invertibility of the intrinsic
coefficient mate. No scalar mate is inverted during this argument. -/
theorem properIntrinsicFiniteCoefficientExtension
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsProper f]
    (J : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) X)
    (_hJ : ∃ n : ℤ, J.IsGE n)
    (_hBJ : ∃ n : ℤ,
      ((Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj J).IsGE n) :
    IsIso ((directImageScalarComparison φ f).app
      ((etaleOriginOpenComparison A X).obj J)) := by
  have := intrinsicCoefficientSiteDirectImageComparison_isIso A f J _hJ
  have := intrinsicCoefficientSiteDirectImageComparison_isIso B f
    ((Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj J) _hBJ
  have := (Etale.properFiniteCoefficientExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) f).1 J
  have h := intrinsicCoefficientSiteMate φ f J
  have hh : IsIso ((scalarExtensionFunctor φ Y).map
        ((intrinsicCoefficientSiteDirectImageComparison A f).app J) ≫
      (directImageScalarComparison φ f).app ((etaleOriginOpenComparison A X).obj J) ≫
      (directImageConstantPush B f).map ((intrinsicCoefficientSiteScalarIso φ X).hom.app J)) := by
    rw [h]
    infer_instance
  simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using hh


end AlgebraicGeometry.ProEtale
