/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility

/-! # Shifts of uniformly constructible finite-Tor towers

Source: the cohomology shift and derived tensor shift identities; latest blueprint,
tower-geometric Gluing and Uniformity paragraphs.
(blueprint: lem-dla1-tower-constructible-shift).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerGluing

private theorem finite_of_iso (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L)
    (h : spFiniteConstructibleTor T A K) : spFiniteConstructibleTor T A L := by
  obtain ⟨⟨a, b, hab, hv⟩, hc, s, t, ht⟩ := h
  refine ⟨⟨a, b, hab, ?_⟩, ?_, s, t, torAmplitude_of_iso T A e s t ht⟩
  · intro i hi
    exact (hv i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e).symm
  · intro i
    have hcons := hc i
    rw [proEtaleModuleRestriction_constructible_iff] at hcons ⊢
    exact ProEtale.isConstructible_of_iso
      ((proEtaleModuleRestriction T A).mapIso
        ((DerivedCategory.homologyFunctor _ i).mapIso e)) hcons

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (q : SpTowerCalculus.Coordinates l E b)

/-- Shifting a constructible finite-Tor tower preserves uniform boundedness.
Source: latest blueprint, tower-geometric Gluing and Uniformity paragraphs;
cohomology of a shifted complex and the K-flat derived tensor construction.
(blueprint: lem-dla1-tower-constructible-shift).

Proof: exact evaluation commutes with shift. At each coefficient level,
H^i(M[j]) is H^(i+j)(M), preserving constructibility and moving the common
cohomology interval [a,d] to [a-j,d-j]. Tensor with a degree-zero test module
is triangulated: a K-flat resolution identifies it with the derived tensor
functor. Its shift isomorphism gives the same formula for tensor cohomology,
so the common Tor interval [s,t] moves to [s-j,t-j]. These endpoints are
independent of the coefficient level. Transport the resulting properties
back through the evaluation-shift comparison. -/
theorem tower_constructible_shift (T : Scheme.{u})
    (M : SpTowerCalculus.C l E b q T) (j : ℤ) :
    spConstructibleTorTowers l E T (q.abelian T) (M.obj⟦j⟧) := by
  let := (q.abelian T).hasDerived
  obtain ⟨hfinite, a, d, s, t, had, hst, hbounds⟩ := M.property
  have ev_shift (n : ℕ) :
      (spDerivedCoefficientEvaluation l E T (q.abelian T) n).obj (M.obj⟦j⟧) ≅
        ((spDerivedCoefficientEvaluation l E T (q.abelian T) n).obj M.obj)⟦j⟧ := by
    let ev := spDerivedCoefficientEvaluation l E T (q.abelian T) n
    let _ : ev.CommShift ℤ := by
      dsimp [ev, spDerivedCoefficientEvaluation]
      infer_instance
    exact (ev.commShiftIso j).app M.obj
  refine ⟨?_, a - j, d - j, s - j, t - j, by omega, by omega, ?_⟩
  · intro n
    exact finite_of_iso T _ (ev_shift n).symm
      (finite_shift T _ _ j (hfinite n))
  · intro n
    refine ⟨?_, torAmplitude_of_iso T _ (ev_shift n).symm _ _
      (tor_shift T _ _ s t j (hbounds n).2)⟩
    intro i hi
    have hz := (hbounds n).1 (i + j) (by omega)
    exact hz.of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso (ev_shift n) ≪≫
        ((DerivedCategory.homologyFunctor _ 0).shiftIso j i (i + j)
          (add_comm j i)).app _)

end AlgebraicGeometry.ProEtale.SpTowerGluing
