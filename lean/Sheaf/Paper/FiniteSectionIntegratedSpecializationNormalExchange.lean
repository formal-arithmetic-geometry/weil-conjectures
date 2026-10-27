/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteSmoothPurityMaps
public import Sheaf.Paper.VectorPurityNormalization
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

/-- The geometric normal-cone exchange supplied by an arbitrary Cartesian section square.
Source: extended-Rees base-change compatibility and the homogeneous normal-cone comparison.
(blueprint: lem-sp-finite-section-integrated-specialization-base-change).
This is the normal-fibre component used by the specialization and integration squares. -/
theorem normalExchange_exists
    {V S V' S' : Scheme.{u}} [IsNoetherian S] [IsNoetherian S']
    (g : V ⟶ S) (g' : V' ⟶ S')
    (s : S ⟶ V) (s' : S' ⟶ V') [IsClosedImmersion s] [IsClosedImmersion s']
    (b : S' ⟶ S) (q : V' ⟶ V) (cart : IsPullback q g' g b)
    (hsec : s' ≫ q = b ≫ s)
    (d : ℕ) [FiniteRingSectionDeformation.Geometry d g s]
    [FiniteRingSectionDeformation.Geometry d g' s'] :
    ∃ (ν : s'.ker.normalCone ⟶ s.ker.normalCone),
      IsPullback ν (Scheme.Hom.normalConeProj g' s')
        (Scheme.Hom.normalConeProj g s) b ∧
      s'.normalConeZeroSection ≫ ν = b ≫ s.normalConeZeroSection := by
  sorry


end AlgebraicGeometry.Etale.FiniteSmoothPurity
