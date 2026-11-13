/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.ClosedQuotientFormalPresentation
import WeilConjectures.AlgebraicGeometry.ChowPullbackAlgebraization
import WeilConjectures.AlgebraicGeometry.ClosedImmersionFormalComparisonTransport
import WeilConjectures.AlgebraicGeometry.FormalSystemsPushPull

/-! # The Chow comparison on a closed quotient

## References

* [Stacks Project, Cohomology of Schemes, Tag 088E]
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A formal module killed by K without proper scheme-theoretic support admits a comparison
to a properly supported formal module whose kernel is killed
by a strictly larger ideal. This is the geometric part of the Noetherian induction;
it does not assume or conclude proper scheme-theoretic support for that kernel.
(Stacks, Theorem 088E) -/
theorem grothendieckExistence_chow_comparison
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} [IsNoetherian X] (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    let Q := (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f
    ∀ [Abelian (CoherentFormalModule X Q)] (K : X.IdealSheafData)
      (M : CoherentFormalModule X Q),
      AnnihilatedBy Q K M →
      Scheme.Modules.HasSupportProperOver f (M.obj.obj (op 0)) →
      (¬ ∃ (Z : Scheme.{u}) (j : Z ⟶ X) (_ : IsClosedImmersion j),
        IsProper (j ≫ f) ∧ AnnihilatedBy Q j.ker M) →
      ∃ (N : CoherentFormalModule X Q) (α : M ⟶ N) (J : X.IdealSheafData),
        K < J ∧ AnnihilatedBy Q J (kernel α) ∧
        ∃ (Z : Scheme.{u}) (j : Z ⟶ X) (_ : IsClosedImmersion j),
          IsProper (j ≫ f) ∧ AnnihilatedBy Q j.ker N := by
  intro Q _ K M hK hR hP
  let j := K.subschemeι
  let : IsNoetherian K.subscheme := isNoetherian_of_locallyOfFiniteType j
  obtain ⟨G, ⟨e⟩, hG, hZ⟩ :=
    exists_closedQuotientFormalPresentation f Q K M hK hR hP
  have hQ : Q.comap j = (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap (j ≫ f) := by
    exact (Scheme.IdealSheafData.comap_comp
      (Scheme.IdealSheafData.ofIdealTop
        (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)) j f).symm
  obtain ⟨Y, q, hq, L, F, hU, hV, ⟨β⟩, hF⟩ :=
    exists_chowPullbackAlgebraization A I (j ≫ f) (Q.comap j) hQ G hG hZ
  let : IsProper q := hq
  obtain ⟨hcoh, α, t, k, c, ht, ⟨hk⟩, _, hkill, _⟩ :=
    exists_formalSystemsPushPull (Q.comap j) L q hV G F β
  obtain ⟨N, a, J, hJ, hker, hN⟩ :=
    exists_closedImmersionFormalComparisonTransport f j Q M G e
      ⟨(Scheme.Modules.pushforward q).obj F.obj, hcoh⟩ hF L hU α t ht k hk hkill
  refine ⟨N, a, J, ?_, hker, hN⟩
  simpa only [j, Scheme.IdealSheafData.ker_subschemeι] using hJ

end AlgebraicGeometry
