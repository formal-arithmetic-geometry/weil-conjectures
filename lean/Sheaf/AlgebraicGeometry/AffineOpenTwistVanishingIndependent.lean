/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections

/-! # Vanishing of twists over one affine open

Source: Stacks Project, Tag 02O1, affine-local part of Lemma 30.16.2.
(blueprint: lem-pc-q3-affine-open-twist-vanishing-independent)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- Serre vanishing over a specified affine open, without the global-cover step.

Source: Stacks Project, Tag 02O1, proof of Lemma 30.16.2, and Tag 0B5T.
(blueprint: lem-pc-q3-affine-open-twist-vanishing-independent)

Proof: put X_V = f inverse-image V. The restriction f_V is proper over the
Noetherian affine scheme V. Coherence and quasi-coherence of F restrict to X_V;
the given invertible restriction of L is ample there. Serre vanishing (Tag 0B5T (4))
gives a threshold in each positive degree.
A finite affine cover of the separated quasi-compact scheme X_V bounds the
cohomological degree of every quasi-coherent module by its Cech complex.
The maximum of the thresholds in these finitely many positive degrees
therefore works for F|X_V tensor (L|X_V)^n in every positive degree. The affine-base
comparison identifies these cohomology
groups with sections of R^q(f_V)_* of that twist. These higher images are
quasi-coherent, hence zero when their sections over the affine base vanish.
Restriction of higher direct images to V identifies them with the higher
images of f_V, and restriction commutes with tensor products and tensor powers.
Transporting these identifications gives the displayed restricted vanishing.
There is no finite-cover or uniform-threshold argument here. Empty V causes
no exception: its category of modules is zero and threshold zero works.
-/
theorem exists_isZero_higherDirectImage_twist_on_affine_open
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsProper f]
    (F : X.Modules) [F.IsQuasicoherent] (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (L : X.Modules) [L.IsInvertible]
    (V : S.Opens) (hV : IsAffineOpen V)
    (hL : ∃ h : (L.restrict (f ⁻¹ᵁ V).ι).IsInvertible,
      @IsAmple (f ⁻¹ᵁ V).toScheme (L.restrict (f ⁻¹ᵁ V).ι) h)
    [HasInjectiveResolutions X.Modules] :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ q : ℕ, 0 < q →
      IsZero (((higherDirectImage f q).obj (F ⊗ L.tensorPow n)).restrict V.ι) := by sorry

end AlgebraicGeometry.Scheme.Modules
