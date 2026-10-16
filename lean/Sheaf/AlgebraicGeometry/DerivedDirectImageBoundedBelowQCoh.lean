/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.CategoryTheory.TruncationHypercohomology
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Sheaf.AlgebraicGeometry.Modules.QuasicoherentExtension
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections

/-! # Bounded-below direct image and quasi-coherence

Source: Stacks Project, perfect.tex, Tag 08D5, bounded-below paragraph
(blueprint: lem-pc-derived-direct-image-bounded-below-qcoh).
-/

@[expose] public section

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry

/-- The zero sheaf is quasi-coherent, using the free sheaf on no generators. -/
private theorem qcoh_containsZero (Y : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent (moduleRings Y.toRingedSpace)).ContainsZero := by
  have hzero : Limits.IsZero
      (SheafOfModules.free (R := moduleRings Y.toRingedSpace) PEmpty.{u + 1}) := by
    apply (Limits.IsZero.iff_id_eq_zero _).mpr
    apply (SheafOfModules.freeHomEquiv _).injective
    funext i
    exact PEmpty.elim i
  exact ⟨⟨_, hzero, SheafOfModules.isQuasicoherent_free
    (R := moduleRings Y.toRingedSpace) PEmpty.{u + 1}⟩⟩

/-- Kernel and Limits.cokernel closure propagate quasi-coherence to every derived page. -/
private theorem qcoh_pages {Y : Scheme.{u}}
    (S : BigradedExactCouple (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0)
    (hS : ∀ p q : ℤ, (S.E p q).IsQuasicoherent) :
    ∀ (r : ℕ) (p q : ℤ), (S.page r p q).IsQuasicoherent := by
  suffices h : ∀ (r : ℕ) (p q : ℤ), ((S.pageCouple r).E p q).IsQuasicoherent by
    intro r p q
    exact h (r - 2) p q
  intro r
  induction r with
  | zero => exact hS
  | succ r ih =>
    intro p q
    have : ((S.pageCouple r).E p q).IsQuasicoherent := ih p q
    have : ((S.pageCouple r).E (p + 2 + r) (q - 1 - r)).IsQuasicoherent :=
      ih _ _
    have : ((S.pageCouple r).E (p - r - 2) (q + r + 1)).IsQuasicoherent :=
      ih _ _
    have := Scheme.Modules.isQuasicoherent_kernel ((S.pageCouple r).d p q)
    exact (Scheme.Modules.quasiCoherent_cokernel_image
      (Limits.kernel.lift ((S.pageCouple r).d p q) ((S.pageCouple r).dInto p q)
        ((S.pageCouple r).dInto_comp_d p q))).2.2.2.2.2.2.1

/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
/ -- An isomorphism-invariant extension-closed property passes from finite graded pieces
to the filtered object, by descending induction from the zero step. - /
private theorem property_of_filtration {C : Type*} [Category* C] [Abelian C]
    (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    (hext : ∀ (S : ShortComplex C), S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂)
    {M : C} (F : DecreasingFiltration M) (N : ℕ)
    (hfull : F.step 0 = ⊤) (hzero : F.step N = ⊥)
    (hgraded : ∀ p : ℤ, P (F.gradedPiece p)) : P M := by
  sorry
-/

/-- Derived direct image of a bounded-below object with quasi-coherent cohomology
has quasi-coherent cohomology. No compactness of the target is required.
Source: Stacks Project, perfect.tex, Tag 08D5, bounded-below paragraph
(blueprint: lem-pc-derived-direct-image-bounded-below-qcoh).

Proof:
1. Represent E by a strictly bounded-below complex, using the standard t-structure.
   Apply exists_truncationHypercohomology to the module direct-image functor.
   Its right derived functor is definitionally schemeDerivedDirectImage.
   The E2 comparisons identify the terms with R^p f_* H^j(E).
2. The qcqs higher-direct-image theorem (Tag 01XJ, lem-pc-finite-support-hi)
   makes these terms quasi-coherent. Negative p and j < a terms vanish.
3. Each later page is a Limits.kernel modulo an image. The quasi-coherent Limits.kernel and
   Limits.cokernel/image lemmas imply, by induction on the page, quasi-coherence of
   every page term. In total degree q only 0 <= p <= q-a occurs, and each
   term stabilizes at a finite page by the half-plane bounds.
4. The convergence theorem supplies a finite filtration of H^q(Rf_*E), with
   those stable terms as graded pieces. Start from its zero last step and use
   isQuasicoherent_of_shortExact successively to deduce quasi-coherence of all
   filtration steps, ending at H^q(Rf_*E). This applies to every integer q.
-/
theorem schemeDerivedDirectImage_preserves_QCoh_of_isGE
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E)
    (a : ℤ) [E.IsGE a] :
    schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E) := by
  sorry

end AlgebraicGeometry
