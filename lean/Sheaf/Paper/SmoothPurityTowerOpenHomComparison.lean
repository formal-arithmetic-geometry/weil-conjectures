/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import Sheaf.Paper.SmoothPurityTowerBinaryCounitPredicates
import Sheaf.Paper.SequenceSiteOpenExtension
import Sheaf.CategoryTheory.RingedToposBinaryDescent
import Sheaf.Paper.CoefficientTowerShriekCalculus
import Sheaf.Paper.SmoothPurityTowerRestrictedRepresentingPair

/-! # Binary coefficient-tower counit gluing steps -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v₀ v₁ w₀ w₁
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerBinaryCounit

open SpTowerShriek SpTowerBinaryCtfFibre

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : Base l E) (o : Operations l E b) (q : SpTowerCalculus.Coordinates l E b)

/-- Local transpose equations and the exact five-term comparison, before the five lemma.
Source: blueprint latest, smooth tower geometric gluing, Gluing paragraph, outer
columns and exact Hom rows (blueprint: lem-sp-tower-open-hom-comparison).

Proof: the adjunction transpose of f:j_D!N → G is the restriction of f after the
unit. Naturality of the counit and he show that theta(f) is the local representing
map after postcomposition with aD. For W precompose the U equation with the
nested counit, using restrictionComp; the restricted pair is obtained by the
open-adjunction argument. These give the three OpenThetaEquation identities.
The sequence-site open-localization theorem identifies constant open subterminals
with U,V,W. Binary ringed-topos descent gives the triangle with the displayed
signed nested maps and actual counits. Restriction, exact open extension, finite
sums and shifts preserve goodness: retain common bounds for restriction and
extension, take unions for finite sums, and translate bounds under shifts.
Apply contravariant Hom exactness to this triangle and its signed rotation, and
to their images under triangulated compact support, to obtain the two exact rows.
The first arrow is negative shifted coverS in both rows. Local representability
and the three transpose equations give the outer bijections for A and for its
shift, since open extension commutes with shift. The product decomposition of Hom
out of a finite biproduct gives those for B and its shift. This establishes only
the four outer bijections; the central comparison still requires the five lemma. -/
theorem open_hom_comparison
    (p : ℕ) (hp : 0 < p) (hlp : l ≠ p)
    (k : Type u) [Field k] [CharP k p]
    (Z Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (h : Z ⟶ Y) (c₀ : Compactification h.left)
    (U V : Z.left.Opens) (hcover : U ⊔ V = ⊤)
    (_hF : ∀ M : D l E Z.left, good l E b q Z.left M →
      good l E b q Y.left ((F l E b o c₀).obj M))
    (_hFD : ∀ (D₀ : Z.left.Opens) (N : D l E D₀.toScheme),
      good l E b q D₀.toScheme N →
      good l E b q Y.left ((support l E b o c₀ D₀).obj N))
    (K : D l E Y.left) (_hK : good l E b q Y.left K)
    (P : D l E U.toScheme) (_hP : good l E b q U.toScheme P)
    (Q : D l E V.toScheme) (_hQ : good l E b q V.toScheme Q)
    (eU : (support l E b o c₀ U).obj P ⟶ K)
    (eV : (support l E b o c₀ V).obj Q ⟶ K)
    (hU : Represents l E b q (support l E b o c₀ U) P K eU)
    (hV : Represents l E b q (support l E b o c₀ V) Q K eV)
    (G : D l E Z.left) (hG : good l E b q Z.left G)
    (aU : (restriction l E b o U).obj G ≅ P)
    (aV : (restriction l E b o V).obj G ≅ Q)
    (e : (F l E b o c₀).obj G ⟶ K)
    (he : LiftEquations l E b o c₀ U V eU eV aU aV e) :
          OpenThetaEquation l E b o q c₀ U eU aU e ∧
          OpenThetaEquation l E b o q c₀ V eV aV e ∧
          OpenThetaEquation l E b o q c₀ (U ⊓ V)
            (restrictedCounit l E b o c₀ (inf_le_left : U ⊓ V ≤ U) P K eU)
            ((restrictionComp l E b o (inf_le_left : U ⊓ V ≤ U)).app G ≪≫
              (restrictionBetween l E b o (inf_le_left : U ⊓ V ≤ U)).mapIso aU) e ∧
          ∀ M : D l E Z.left, good l E b q Z.left M →
            ∃ δ : M ⟶ (shiftFunctor _ (1 : ℤ)).obj (coverA l E b o U V M),
              Triangle.mk (coverS l E b o U V M) (coverT l E b o U V M) δ ∈
                distTriang _ ∧
              good l E b q Z.left (coverA l E b o U V M) ∧
              good l E b q Z.left (coverB l E b o U V M) ∧
              good l E b q Z.left
                ((shiftFunctor _ (1 : ℤ)).obj (coverA l E b o U V M)) ∧
              good l E b q Z.left
                ((shiftFunctor _ (1 : ℤ)).obj (coverB l E b o U V M)) ∧
              HomFiveExact (coverS l E b o U V M) (coverT l E b o U V M) δ G ∧
              ImageHomFiveExact (F l E b o c₀)
                (coverS l E b o U V M) (coverT l E b o U V M) δ K ∧
              OuterBijective (A := coverA l E b o U V M) (B := coverB l E b o U V M)
                (F l E b o c₀) e := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerBinaryCounit
