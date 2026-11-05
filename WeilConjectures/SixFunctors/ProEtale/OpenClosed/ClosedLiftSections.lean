/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.RingTheory.ProEtale.ClosedLiftRetraction
public import WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Sections over henselian lifts of weakly contractible objects

Let `X = Spec A`, `i : Z = Spec (A ⧸ I) ⟶ X` and `j : U ⟶ X` a quasi-compact open immersion onto
the complement. Let `C̄` be an ind-étale `A ⧸ I`-algebra all of whose faithfully flat ind-étale
covers split (e.g. a w-contractible one), and `W = Spec H_A(C̄)` its henselian lift
(`Algebra.ClosedLift`). Then:

* every faithfully flat ind-étale cover of `H_A(C̄)` splits
  (`Algebra.ClosedLift.exists_retraction`), so `W` is weakly contractible
  (`AlgebraicGeometry.Scheme.ProEt.isWeaklyContractible_of_forall_exists_retraction`);
* every nonempty clopen subset of `W` meets the closed fibre, so `j_! N` has no sections over
  `W` (`AlgebraicGeometry.ProEtale.subsingleton_openImmersionLowerShriek_closedLiftSpec`);
* consequently the unit `F(W) ⟶ (i^* F)(W ×_X Z)` is bijective
  (`AlgebraicGeometry.ProEtale.bijective_unit_app_closedLiftSpec`), part (1) of blueprint
  `det-sf-open-closed-pullback-limits`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable {A : CommRingCat.{u}} (I : Ideal A) (C : Type u) [CommRing C] [Algebra (A ⧸ I) C]
  [Algebra A C] [IsScalarTower A (A ⧸ I) C]

variable {I C}

variable {R : Type (u + 1)} [Ring R] {U : Scheme.{u}} (j : U ⟶ Spec A) [IsOpenImmersion j]

/-- Sections over a weakly contractible object are exact: an epimorphism of sheaves of modules is
surjective on sections over it. -/
lemma surjective_app_of_isWeaklyContractible {T : Scheme.{u}} {W : T.ProEt}
    (hW : (Scheme.ProEt.topology T).IsWeaklyContractible.{u + 1} W)
    {F G : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R)} (φ : F ⟶ G) [Epi φ] :
    Function.Surjective (φ.hom.app (op W)) :=
  hW ((sheafCompose _ (forget _)).map φ)
    ((Presheaf.isLocallySurjective_iff_whisker_forget _ _).1
      ((Sheaf.isLocallySurjective_iff_epi' (φ := φ)).2 inferInstance))

variable [QuasiCompact j]

end ProEtale

end AlgebraicGeometry
