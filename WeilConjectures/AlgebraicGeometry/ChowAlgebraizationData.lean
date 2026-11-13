/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.AlgebraicGeometry.FormalSystemsPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.ChowAlgebraizationCore
import WeilConjectures.AlgebraicGeometry.ChowAlgebraizationSupport

/-! # Algebraization on a quasi-projective proper modification

Source: Stacks Project, Theorem 088E, projective compactification argument.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Algebraization on a supplied quasi-projective proper modification, with proper
support of the pushforward.

Source: Stacks Project, Theorem 088E, projective compactification and support paragraphs,
using Lemmas 0885 and 0887. -/
theorem exists_chow_algebraization_data
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    {Z : Scheme.{u}} [IsNoetherian Z] (f : Z ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Q : Z.IdealSheafData)
    (hQ : Q = (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)
    (G : CoherentFormalModule Z Q)
    (hR : Scheme.Modules.HasSupportProperOver f (G.obj.obj (op 0)))
    (Y : Scheme.{u}) (q : Y ⟶ Z) [IsProper q] (n : ℕ)
    (e : Y ⟶ ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (.of A)))
    [IsImmersion e]
    (he : e ≫ (ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (.of A)) ↘ Spec (.of A)) =
      q ≫ f)
    (L : Z.IdealSheafData)
    (hL : (L.support.compl : Set Z).Nonempty)
    (hIso : IsIso (pullback.snd q (Scheme.Opens.ι L.support.compl))) :
    ∃ F : CoherentModules Y,
      Nonempty (G.obj ⋙ Scheme.Modules.tensorPullback q ≅
        formalCompletionSystem (Q.comap q) F.obj) ∧
      Scheme.Modules.HasSupportProperOver f ((Scheme.Modules.pushforward q).obj F.obj) := by
  have := hL
  have := hIso
  obtain ⟨F, hF, hproper⟩ := exists_chow_algebraization_core A I f Q hQ G hR Y q n e he
  refine ⟨F, hF, ?_⟩
  exact chow_algebraization_pushforward_support f q F hproper

end AlgebraicGeometry
