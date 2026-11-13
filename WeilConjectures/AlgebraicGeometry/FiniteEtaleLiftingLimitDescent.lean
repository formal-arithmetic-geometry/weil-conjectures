/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore

/-!
# Reduction of finite étale lifting to henselian G-rings

## References

* Stacks Project, Tag 0GS2
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Lifting finite étale covers of proper schemes over arbitrary henselian pairs follows
from lifting them over henselian G-ring pairs. Hypothesis `H` is the statement of
`exists_finiteEtale_lift_of_henselianPair_of_isGRing`.
(Stacks, Tag 0GS2.) -/
theorem exists_finiteEtale_lift_of_henselianPair_of_gRing_lifting
    (H : ∀ (B : Type u) [CommRing B], IsGRing B →
      ∀ (J : Ideal B) [HenselianRing B J] (Z : Scheme.{u})
        (g : Z ⟶ Spec (.of B)) [IsProper g]
        (W : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤
          (pullback g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))),
        ∃ U' : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Z,
          Nonempty
            (Over.mk (pullback.snd U'.hom
              (pullback.fst g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))) ≅
              Over.mk W.hom))
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f]
    (V : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤
      (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) :
    ∃ U : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y,
      Nonempty
        (Over.mk (pullback.snd U.hom
          (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) ≅
          Over.mk V.hom) := by
  obtain ⟨U, hU, _⟩ :=
    exists_finiteEtale_lift_of_henselianPair_of_gRing_lifting_core H I f V
  exact ⟨U, hU⟩

end AlgebraicGeometry.Scheme
