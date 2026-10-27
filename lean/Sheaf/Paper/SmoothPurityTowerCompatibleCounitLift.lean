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

/-- Compatible local counits factor across the signed open-cover triangle.
Source: blueprint latest, smooth tower geometric gluing, Gluing paragraph, signed
counit lift (blueprint: lem-sp-tower-compatible-counit-lift).

Proof: identify sequence-site opens with the open slices using
sequenceSiteOpenExtension. Binary ringed-topos descent supplies the distinguished
signed triangle with maps coverS and coverT; the shrink calculus identifies its
nested-open maps with nested. In F(coverS) followed by beta the two summands are
the restricted local counits, transported along aU and aV. Use hcompat and hc to
identify them, so that the negative second summand cancels the first. Compact
support is triangulated; contravariant Hom exactness on its image triangle supplies
e with F(coverT) ≫ e = beta. Composing with the images of the two inclusions gives
the two LiftEquations. Conversely those equations and additivity, applied to the
biproduct formula for coverT, give the same factorization for every lift. The
zero-overlap identity depends only on compatibility and holds before a lift is chosen. -/
theorem compatible_counit_lift
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
    (c : (restrictionBetween l E b o (inf_le_left : U ⊓ V ≤ U)).obj P ≅
      (restrictionBetween l E b o (inf_le_right : U ⊓ V ≤ V)).obj Q)
    (hc : (support l E b o c₀ (U ⊓ V)).map c.hom ≫
        restrictedCounit l E b o c₀ (inf_le_right : U ⊓ V ≤ V) Q K eV =
      restrictedCounit l E b o c₀ (inf_le_left : U ⊓ V ≤ U) P K eU)
    (G : D l E Z.left) (hG : good l E b q Z.left G)
    (aU : (restriction l E b o U).obj G ≅ P)
    (aV : (restriction l E b o V).obj G ≅ Q)
    (hcompat : (restrictionComp l E b o (inf_le_left : U ⊓ V ≤ U)).hom.app G ≫
        (restrictionBetween l E b o (inf_le_left : U ⊓ V ≤ U)).map aU.hom ≫ c.hom =
      (restrictionComp l E b o (inf_le_right : U ⊓ V ≤ V)).hom.app G ≫
        (restrictionBetween l E b o (inf_le_right : U ⊓ V ≤ V)).map aV.hom) :
    (∃ e : (F l E b o c₀).obj G ⟶ K,
      LiftEquations l E b o c₀ U V eU eV aU aV e) ∧
    (F l E b o c₀).map (coverS l E b o U V G) ≫
      beta l E b o c₀ U V eU eV aU aV = 0 ∧
    ∀ e : (F l E b o c₀).obj G ⟶ K,
      LiftEquations l E b o c₀ U V eU eV aU aV e →
      (F l E b o c₀).map (coverT l E b o U V G) ≫ e =
        beta l E b o c₀ U V eU eV aU aV := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerBinaryCounit
