/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.AlgebraicGeometry.Restrict
import WeilConjectures.AlgebraicGeometry.FlatModelFiniteFreeConstruction
import WeilConjectures.AlgebraicGeometry.FlatModelFiniteFreeComparison

/-! # Local nonnegative finite-free replacements of bounded flat complexes

## References

* Stacks Project, Tags 064U, 0653 and 00NX
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A bounded nonnegative flat complex with a bounded-above finite-free resolution has,
near a specified point, a finite-free replacement in the same degree interval. The
replacement computes the homology of every ordinary scheme pullback of the flat complex
(Stacks, Tags 064U, 0653 and 00NX). -/
theorem exists_local_finiteFree_shortening {T : Scheme.{u}} (U : T.Opens)
    (C Q : CochainComplex U.toScheme.Modules ℤ) (d : ℕ)
    (hCge : C.IsStrictlyGE 0) (hCle : C.IsStrictlyLE d)
    (hCflat : ∀ n : ℤ, (C.X n).IsFlatOver (𝟙 U.toScheme))
    (hQle : Q.IsStrictlyLE d)
    (hQfree : ∀ n : ℤ, ∃ r : ℕ,
      Nonempty (Q.X n ≅ SheafOfModules.free
        (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r))))
    (e : Q ⟶ C) (he : QuasiIso e) (t : T) (ht : t ∈ U) :
    ∃ (V : T.Opens) (hVU : V ≤ U) (P : CochainComplex V.toScheme.Modules ℤ),
      t ∈ V ∧ P.IsStrictlyGE 0 ∧ P.IsStrictlyLE d ∧
      (∀ n : ℤ, ∃ r : ℕ,
        Nonempty (P.X n ≅ SheafOfModules.free
          (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin r)))) ∧
      ∀ {T' : Scheme.{u}} (g : T' ⟶ V.toScheme) (q : ℕ),
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q ≅
          (((Modules.pullback (g ≫ T.homOfLE hVU)).mapHomologicalComplex _).obj C).homology q)
    := by
  obtain ⟨V, hVU, P, hstruct, hP⟩ :=
    exists_local_finiteFree_construction U C Q d hCge hCle hCflat hQle hQfree e he t ht
  obtain ⟨eP, heP⟩ := hP
  refine ⟨V, hVU, P, hstruct.1, hstruct.2.1, hstruct.2.2.1, hstruct.2.2.2, ?_⟩
  exact local_finiteFree_homology_comparison U C Q d hCge hCle hCflat hQle hQfree e he t
    V hVU P hstruct eP heP

end AlgebraicGeometry.Scheme.Modules
