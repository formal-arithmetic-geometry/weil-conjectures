/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent
import WeilConjectures.AlgebraicGeometry.FiniteEtaleLiftingApproximation

/-!
# Essential surjectivity of finite étale lifting over a henselian pair

## References

* Stacks Project, Tag 0GS2
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Every finite étale cover of the closed fibre of a proper scheme over a henselian pair
lifts to a finite étale cover of the scheme, with an isomorphism over the closed fibre.
(Stacks, Tag 0GS2.) -/
theorem Scheme.essSurj_pullback_finiteEtale_of_henselianRing
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f]
    (V : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤
      (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) :
    ∃ U : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y,
      Nonempty
        (Over.mk (pullback.snd U.hom
          (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) ≅
          Over.mk V.hom) := by
  apply Scheme.exists_finiteEtale_lift_of_henselianPair_of_gRing_lifting
    (fun B _ hB J _ Z g _ W ↦
      Scheme.exists_finiteEtale_lift_of_henselianPair_of_isGRing hB J g W) I f V

end AlgebraicGeometry
