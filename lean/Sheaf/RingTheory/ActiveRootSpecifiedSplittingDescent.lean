/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.RingTheory.ActiveRootNormalizationData
public import Mathlib.RingTheory.RingHom.FinitePresentation

/-! # Descent of a specified active-root splitting

Source: Stacks, Tags 01ZM and 05N9, morphism and equality clauses.
(blueprint: lem-sfb-active-root-specified-splitting-descent).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace Algebra.ActiveRootNormalization

/-- A specified splitting over the punctured active-root colimit descends exactly.
Source: Stacks, Tag 05N9(2),(3), affine form of Tag 01ZM.
(blueprint: lem-sfb-active-root-specified-splitting-descent).

Proof: positive orders coprime to p form a nonempty directed divisibility preorder:
1 is an object and the product of two orders is a common upper bound. Base change of
D to order 1 is finitely presented. The diagonal product of d copies of that stage is
finitely presented by the coordinate idempotents, their orthogonality, and sum equal
to 1; for d = 0 the presentation is the single relation 1 = 0. Finite products commute
with scalar extension: send (a_j) tensor b to (a_j*b), and send (b_j) to the sum of
e_j tensor b_j. Descend theta and its inverse by the morphism clause of 05N9 and
transport both to a common upper stage. Their two composites become identities at
the colimit. Apply the equality clause of 05N9 to each composite and its identity,
and pass to a common upper stage again. The resulting maps are inverse and still
extend to the specified theta. Their agreement on D is the displayed equation;
agreement on the coefficient stage is automatic for algebra maps. No transition map
is assumed injective. No characteristic, geometric point, normality, finiteness of
D as a module, or nonempty product hypothesis is needed. -/
theorem activeRootTower_specified_splitting_descends
    {B A : Type u} [CommRing B] [CommRing A] [Algebra B A]
    {r s : ℕ} (t : Fin r → B) (active : Fin s → Fin r) (p : ℕ)
    (D : Under (CommRingCat.of (Localization.Away (∏ i, t i))))
    (hD : D.hom.hom.FinitePresentation) (d : ℕ)
    (theta : extend D (activeColimit (A := A) t active p) ≅
      diagonal (activeColimit (A := A) t active p).right d) :
    ∃ m : RootTowerIndex {n : ℕ+ | Nat.Coprime (n : ℕ) p},
      ∃ theta_m : extend D ((activeDiagram (A := A) t active p).obj m) ≅
          diagonal ((activeDiagram (A := A) t active p).obj m).right d,
        ∀ (x : D.right) (j : Fin d),
          (colimit.ι (activeDiagram (A := A) t active p) m).right
              (theta_m.hom.right (extendInclusion D _ x) j) =
            theta.hom.right (extendInclusion D _ x) j := by sorry

end Algebra.ActiveRootNormalization
