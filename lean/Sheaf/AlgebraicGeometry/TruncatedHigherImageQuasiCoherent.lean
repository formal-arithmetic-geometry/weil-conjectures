/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.Ample
import Sheaf.CategoryTheory.TruncationHypercohomology
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Sheaf.AlgebraicGeometry.Modules.QuasicoherentExtension
import Sheaf.AlgebraicGeometry.OrdinaryHigherImageQuasiCoherent
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty

/-! # Quasi-coherence of a truncated higher image

Source: Stacks Project, Tag 08D5, bounded-below paragraph, and Tag 015J.
-/

@[expose] public section

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry

/-- Kernel and cokernel closure propagate any object property to every derived page. -/
private theorem property_pages {C : Type*} [Category* C] [Abelian C]
    (P : ObjectProperty C)
    (hk : ∀ {M N : C} (φ : M ⟶ N), P M → P N → P (Limits.kernel φ))
    (hc : ∀ {M N : C} (φ : M ⟶ N), P M → P N → P (Limits.cokernel φ))
    (S : BigradedExactCouple C 0) (hS : ∀ p q : ℤ, P (S.E p q)) :
    ∀ (r : ℕ) (p q : ℤ), P (S.page r p q) := by
  suffices h : ∀ (r : ℕ) (p q : ℤ), P ((S.pageCouple r).E p q) by
    intro r p q
    exact h (r - 2) p q
  intro r
  induction r with
  | zero => exact hS
  | succ r ih =>
    intro p q
    exact hc
      (Limits.kernel.lift ((S.pageCouple r).d p q) ((S.pageCouple r).dInto p q)
        ((S.pageCouple r).dInto_comp_d p q))
      (ih _ _)
      (hk ((S.pageCouple r).d p q) (ih _ _) (ih _ _))

/-- An isomorphism-invariant extension-closed property passes from finite graded pieces
to the filtered object on any finite index interval, by descending induction. -/
private theorem property_of_shifted_filtration {C : Type*} [Category* C] [Abelian C]
    (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    (hext : ∀ (S : ShortComplex C), S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂)
    {M : C} (F : DecreasingFiltration M) (b : ℤ) (N : ℕ)
    (hfull : F.step b = ⊤) (hzero : F.step (b + N) = ⊥)
    (hgraded : ∀ p : ℤ, b ≤ p → p < b + N → P (F.gradedPiece p)) : P M := by
  sorry

/-- Each higher image of a canonical lower truncation is quasi-coherent.
Source: Stacks Project, Tag 08D5, proof of part (1), bounded-below paragraph;
Tag 015J supplies the bounded-below hypercohomology spectral sequence, and
Tag 01XJ, part (1), supplies quasi-coherence of ordinary higher direct images.
(blueprint: lem-pc-truncated-higher-image-quasi-coherent).

Proof.
1. Put K = tau_{>= a} E. Its cohomology agrees with that of E in degrees at
   least a and is zero in lower degrees. Thus all its cohomology sheaves are
   quasi-coherent, including the zero sheaf, and K is bounded below by a.
2. Use bounded-below truncation hypercohomology for module direct image. Its
   second page in bidegree (p,r), for p >= 0, is R^p f_* H^r(K). These sheaves
   are quasi-coherent by Tag 01XJ (1); the terms for p < 0 or r < a are zero.
   To obtain Tag 01XJ (1) locally, restrict to an affine target open, whose
   preimage is qcqs. Affine acyclicity and localization of cohomology on
   principal opens identify higher-image sections with localized modules on
   an affine source. Mayer--Vietoris induction on a finite affine cover,
   with quasi-compact overlaps, propagates this localization comparison.
   The higher-image presheaf description gives quasi-coherent second pages.
3. Each subsequent page is a kernel modulo an image. Closure of quasi-coherent
   modules under kernels, images and cokernels proves their quasi-coherence
   by induction on the page. In total degree q, the quadrant bounds give a
   finite convergent filtration of H^q(Rf_* K), and its graded pieces are
   stable page terms, hence quasi-coherent. Starting with its zero last step,
   extension closure proves quasi-coherence of each preceding filtration
   step and finally of the whole abutment. This also covers q < a, when the
   abutment is zero, and an empty scheme, where every module sheaf is zero.
-/
theorem truncated_higherImage_isQuasicoherent
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (E : schemeDerivedQCohCategory X) (a q : ℤ) :
    ((schemeHigherDirectImage f q).obj
      ((DerivedCategory.TStructure.t.truncGE a).obj E.obj)).IsQuasicoherent := by
  sorry

end AlgebraicGeometry
