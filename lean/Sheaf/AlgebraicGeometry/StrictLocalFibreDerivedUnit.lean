/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D7
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap
public import Sheaf.AlgebraicGeometry.CohomologyPullbackExactConservative
public import Mathlib.FieldTheory.IsSepClosed
import Sheaf.AlgebraicGeometry.StrictLocalFibreUnitStalks
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # Testing the derived unit on strict-local geometric fibres

Source: Stacks Project, Tags 03Q9 and 03Q1; corrected Tag 0EZV proof, steps 6--7.
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- Geometric points detect the homology sheaf of the derived unit, and the pointwise
comparison identifies their tests with the comparisons for every lift.
Source: Stacks Project, Tags 03Q9 and 03PN; corrected Tag 0EZV proof, steps 6--7.
(blueprint: lem-weil-pbc-strict-local-fibre-derived-unit).
Proof: an invertible sheaf map remains invertible under every stalk functor. Each lift
corresponds to a point with the same bijectivity criterion, giving the forward implication.
Conversely, take the lift corresponding to each point and apply the pointwise criterion.
The universe-lift isomorphism transports this invertibility to the conservative family
of universe-lifted geometric points, which detects isomorphisms of abelian sheaves. -/
theorem strictLocalFibre_derivedUnit_iff
    {X S : Scheme.{u}} (f : X ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (K : Type u) [Field K] [IsSepClosed K]
    (u : Spec (.of K) ⟶ Scheme.strictHenselizationScheme (x ≫ f))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    let t := u ≫ Scheme.strictHenselizationStructuralMap (x ≫ f)
    let p := pullback.map
      (Scheme.strictHenselizationStructuralMap x ≫ f) t
      (Scheme.strictHenselizationStructuralMap (x ≫ f)) t
      (Scheme.strictHenselizationMap f x) (𝟙 _) (𝟙 _)
      (by simpa using (Scheme.strictHenselizationMap_over f x).symm) (by simp)
    let a := pullback.snd (Scheme.strictHenselizationStructuralMap (x ≫ f)) t
    IsIso (derivedPullbackUnitHomology p
      ((upperStar AddCommGrpCat.{u + 1} a).obj F) q) ↔
    ∀ v : Spec (.of K) ⟶ Scheme.strictHenselizationScheme (x ≫ f),
      v ≫ Scheme.strictHenselizationStructuralMap (x ≫ f) = t →
      Function.Bijective (cohomologyMap
        (pullback.snd (Scheme.strictHenselizationMap f x) v) F q) := by
  obtain ⟨hpoint, hlift⟩ := strictLocalFibre_unit_stalks f x K u F q
  constructor
  · intro h v hv
    obtain ⟨z, _, hz⟩ := hlift v hv
    apply hz.mp
    have := h
    infer_instance
  · intro h
    apply Scheme.isIso_of_isIso_sheafFiber_map
    intro z
    dsimp only [Scheme.uliftPointSmallEtale]
    apply (NatIso.isIso_map_iff
      (GrothendieckTopology.Point.uliftSheafFiberIso.{u + 1}
        (Scheme.pointSmallEtale
          ((pullback (Scheme.strictHenselizationStructuralMap (x ≫ f))
            (u ≫ Scheme.strictHenselizationStructuralMap (x ≫ f))).algClosurePoint z))
        AddCommGrpCat.{u + 1}) _).2
    obtain ⟨v, hv, _, hz⟩ := hpoint z
    exact hz.mpr (h v hv)

end AlgebraicGeometry.Etale
