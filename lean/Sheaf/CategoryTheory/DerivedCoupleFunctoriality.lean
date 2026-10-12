/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.CategoryTheory.ExactCoupleConvergence
import Sheaf.CategoryTheory.DerivedCoupleExact
import Sheaf.CategoryTheory.ExactCouple

/-!
# Functoriality of derived exact couples

Source: Stacks Project, Homological Algebra, Definitions 12.21.1 and 12.21.3,
Lemmas 12.21.2 and 12.21.4 (Tags 011Q, 011R, 011S, 011T)
(blueprint: lem-sp-derived-couple-functoriality).
-/

@[expose] public section

universe u v

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A degree-preserving morphism of type-`s` bigraded exact couples.
Source: Stacks Project, Homological Algebra, Definition 12.21.1, Tag 011Q
(blueprint: lem-sp-derived-couple-functoriality). -/
structure CoupleMorphism {s : ℕ} (X Y : BigradedExactCouple C s) where
  tD : ∀ p q : ℤ, X.D p q ⟶ Y.D p q
  tE : ∀ p q : ℤ, X.E p q ⟶ Y.E p q
  alpha_comm : ∀ p q : ℤ,
    tD p q ≫ Y.alpha p q = X.alpha p q ≫ tD (p - 1) (q + 1)
  f_comm : ∀ p q : ℤ,
    tE p q ≫ Y.f p q = X.f p q ≫ tD (p + 2) (q - 1)
  g_comm : ∀ p q : ℤ,
    tD p q ≫ Y.g p q = X.g p q ≫ tE (p + s) (q - s)

/-- A morphism of exact couples induces compatible morphisms on every derived page,
and on the limiting page. The latter carries limiting cycles and boundaries into those
of the target and hence descends to the quotient at infinity, when the limits exist.

Proof, Step 1 (def-sp-exact-couple, lem-sp-derived-couple-exact): the three squares
imply differential commutation. Restrict tE to differential kernels and descend through
boundaries to obtain the derived E map. Restrict tD to the incoming alpha image to obtain
the derived D map. The restriction and quotient equations uniquely characterize these
maps. The three structure-map squares descend, since alpha, f and g in the derived
couple are defined by these same restrictions, factorizations and quotient projections.
Step 2 (lem-sp-derived-couple-exact): each derived couple is again exact. Induct on n
to obtain morphisms M n of the type-n couples, beginning with T. The successor D map
commutes with derivedDInclusion and the successor E map with derivedEProjection through
the induced kernel map. The f and g squares imply commutation with each d_r.
Step 3 (def-sp-convergence): induction in the cycle/boundary recursion shows that tE
preserves every finite Z_r and B_r and induces the page maps on Z_r/B_r. The universal
properties of the greatest lower bound and least upper bound give preservation of Z∞
and B∞. Restrict tE to Z∞ and use the cokernel universal property to descend to E∞.
Source: Stacks Project, Homological Algebra, Definitions 12.21.1 and 12.21.3,
Lemmas 12.21.2 and 12.21.4 (Tags 011Q, 011R, 011S, 011T)
(blueprint: lem-sp-derived-couple-functoriality). -/
theorem derivedCoupleFunctoriality (X Y : BigradedExactCouple C 0)
    (T : CoupleMorphism X Y) :
    (∃ M : ∀ n : ℕ, CoupleMorphism (X.pageCouple n) (Y.pageCouple n),
      (∀ p q : ℤ, (M 0).tD p q = T.tD p q) ∧
      (∀ p q : ℤ, (M 0).tE p q = T.tE p q) ∧
      (∀ (n : ℕ) (p q : ℤ),
        (M (n + 1)).tD p q ≫ (Y.pageCouple n).derivedDInclusion p q =
          (X.pageCouple n).derivedDInclusion p q ≫ (M n).tD p q) ∧
      (∀ (n : ℕ) (p q : ℤ),
        ∃ k : kernel ((X.pageCouple n).d p q) ⟶
          kernel ((Y.pageCouple n).d p q),
          k ≫ kernel.ι ((Y.pageCouple n).d p q) =
            kernel.ι ((X.pageCouple n).d p q) ≫ (M n).tE p q ∧
          (X.pageCouple n).derivedEProjection p q ≫ (M (n + 1)).tE p q =
            k ≫ (Y.pageCouple n).derivedEProjection p q) ∧
      (∀ (n : ℕ) (p q : ℤ),
        (M n).tE p q ≫ (Y.pageCouple n).d p q =
          (X.pageCouple n).d p q ≫ (M n).tE (p + 2 + n) (q - 1 - n))) ∧
    (∀ (LX : LimitSubobjects X) (LY : LimitSubobjects Y),
      (∀ p q : ℤ,
        (LY.Z p q).Factors ((LX.Z p q).arrow ≫ T.tE p q) ∧
        (LY.B p q).Factors ((LX.B p q).arrow ≫ T.tE p q)) ∧
      (∀ p q : ℤ, ∃ (e : X.pageInfinity LX p q ⟶ Y.pageInfinity LY p q)
          (z : (LX.Z p q : C) ⟶ (LY.Z p q : C)),
        (LX.Z p q).arrow ≫ T.tE p q = z ≫ (LY.Z p q).arrow ∧
        z ≫ cokernel.π (Subobject.ofLE (LY.B p q) (LY.Z p q)
              (limitBoundary_le_cycle Y LY p q)) =
          cokernel.π (Subobject.ofLE (LX.B p q) (LX.Z p q)
              (limitBoundary_le_cycle X LX p q)) ≫ e)
    ) := by
  sorry

end CategoryTheory.BigradedExactCouple
