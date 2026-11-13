/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.AlgebraicGeometry.PushforwardSupportClosed

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Proper pushforward preserves support proper over a separated finite-type base.
Source: Stacks Project, Theorem 088E, the paragraph on the support of H, using
Tags 02O5, 0CYQ (1), and 0CYN (https://stacks.math.columbia.edu/tag/088E). -/
theorem chow_algebraization_pushforward_support
    {S Z Y : Scheme.{u}} [IsNoetherian Z]
    (f : Z ⟶ S) [IsSeparated f] [LocallyOfFiniteType f]
    (q : Y ⟶ Z) [IsProper q] (F : CoherentModules Y)
    (hF : Scheme.Modules.HasSupportProperOver (q ≫ f) F.obj) :
    Scheme.Modules.HasSupportProperOver f ((Scheme.Modules.pushforward q).obj F.obj) := by
  obtain ⟨C, hC, hCp⟩ := hF
  obtain ⟨D, hD, hDsub⟩ := pushforward_support_closed_subset q F C hC
  obtain ⟨W, hWset, hWproper⟩ :=
    (Scheme.closed_subset_proper_over_base_properties (q ≫ f) C).2.2.2 q f rfl hCp
  have hDW : (D : Set Z) ⊆ W := by
    rw [hWset]
    exact hDsub
  have hDproper :=
    (Scheme.closed_subset_proper_over_base_properties f W).2.2.1 D hDW hWproper
  exact ⟨D, hD, hDproper⟩

end AlgebraicGeometry
