/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.Paper.ContinuousIntegralCoefficients
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def

/-! # A locally finite free resolution of a finitely presented integral local system -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A locally finitely presented integral coefficient module has a two-term locally free
resolution. Source: Bhatt--Scholze, Definition 6.8.10, Proposition 6.8.11(3),
Remark 7.3.2 and Lemma 7.3.9 (finite locally constant sheaves are classical).
(blueprint: lem-weil-pbc-integral-lfp-locally-free-resolution)

Proof: first compare local presentations with integral local systems. Evaluate their
matrices at geometric points. Descent makes the finite fiber module independent of the
lift to the presentation cover. Flat going-down and constancy of continuous functions
on comparable points show that its Smith invariants agree under specialization.
Noetherianity gives finitely many irreducible and connected components. On each connected
component its fiber module type is therefore fixed. Continuous pivot elimination on a
presentation cover identifies the module locally with that fixed finite module over O_E.
Its torsion subsheaf T has a uniform annihilator and finite fibers, and its quotient L is
locally finite free. The actions on T and on Hom(L,T) factor through finite quotients.
The extension cocycle of P is continuous with values in a finite module. A finite étale
cover consequently trivializes T and splits the extension P of L by T. On that cover,
resolve the finite constant torsion module by finite free constant modules over the DVR
and add the degree-zero free summand L. Push the degree-zero resolution module forward
along the finite étale cover and compose its surjection onto the pushed-forward P with
the finite étale counit onto P. Finite étale pushforward preserves local finite freeness,
and the counit is surjective, as checked on the split fibers, without dividing by
the covering degree. Its kernel is locally
finite free: locally the source is free and the target is a fixed finite DVR module, so
Smith normal form makes the kernel free. These give F₁, F₀, f and g and the asserted
short exact sequence. Zero torsion, zero ranks and empty schemes use zero summands and
the empty or identity cover. No resolution object is defined by choosing these witnesses.
-/
theorem integral_lfp_locallyFree_resolution
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (CondensedRing.integralCoeff ℓ E) X))
    (hP : IsLocallyFinitelyPresented
      (condensedRingObj (CondensedRing.integralCoeff ℓ E) X) P) :
    ∃ (F₁ F₀ : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (CondensedRing.integralCoeff ℓ E) X))
      (f : F₁ ⟶ F₀) (g : F₀ ⟶ P) (w : f ≫ g = 0),
      (ShortComplex.mk f g w).ShortExact ∧
      (∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
        Mod.IsFree ((upperStar Ab.{u + 1} (C.f s)).obj
          (condensedRingObj (CondensedRing.integralCoeff ℓ E) X))
          (((upperStar Ab.{u + 1} (C.f s)).mapMod _).obj F₁)) ∧
      (∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
        Mod.IsFree ((upperStar Ab.{u + 1} (C.f s)).obj
          (condensedRingObj (CondensedRing.integralCoeff ℓ E) X))
          (((upperStar Ab.{u + 1} (C.f s)).mapMod _).obj F₀)) := by
  sorry

end AlgebraicGeometry.ProEtale
