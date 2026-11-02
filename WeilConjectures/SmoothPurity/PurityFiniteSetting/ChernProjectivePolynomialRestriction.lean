/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.ChernProjectivePolynomialValue

/-! # Restriction of the lower projective Chern relation

(blueprint: lem-pur-chern-projective-polynomial-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules

namespace WeilConjectures.PurityFiniteSetting

/-- The lower Chern polynomial vanishes after restriction along a morphism of
projective realizations preserving their tautological line and base projection.
There is no exact sequence, Cartier condition, candidate family, or flag.

Source: Stacks Project, Tag 0FI5, proposition-chern-class, the restriction-zero
sentence in the invertible-subbundle paragraph.
(blueprint: lem-pur-chern-projective-polynomial-restriction).

Proof: the canonical unit and positive-power pullback comparisons compose along
scheme morphisms. For the shifted line this is the root-normalized inverse-image
comparison; tensor naturality and induction give the same identity for every
ordered positive power. Consequently hi identifies successive pullback of each
base coefficient with its pullback along Q's projection. Picard invariance under
θ and arbitrary-base Kummer functoriality identify the pulled hyperplane root with
Q's hyperplane root. The pullback/tensor square and induction then identify every
hyperplane product in the value on D with its counterpart on Q. The degree casts
agree by equality induction. Additivity of exact inverse image preserves the
signed finite sum and subtraction. Thus the pulled value equals the lower value
on Q. Since n>0, the defining Chern-family predicate gives the projective relation
for G on this Q; the proved relation/value equivalence makes that value zero. -/
theorem ordinaryFiniteProjectivePolynomialValue_restrict_eq_zero
    (P : PurityFiniteSetting.{u}) {S : Scheme.{u}}
    (a : S ⟶ Spec (.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (n : ℕ) (hn : 0 < n) (G : S.Modules) [G.IsFiniteLocallyFreeOfRank n]
    {F : S.Modules} (D : ProjectiveBundleRealization S F) (hD : D.L.IsInvertible)
    (Q : ProjectiveBundleRealization S G) (hQ : Q.L.IsInvertible)
    (i : Q.A.data.relProj ⟶ D.A.data.relProj)
    (hi : i ≫ D.A.data.relProjHom = Q.A.data.relProjHom)
    (θ : (Scheme.Modules.tensorPullback i).obj D.L ≅ Q.L)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    P.ordinaryFiniteCohomologyPullback t i
      (P.diagonalExponent_isUnit (D.A.data.relProjHom ≫ a)) n
      (P.ordinaryFiniteProjectivePolynomialValue t a D hD n
        (P.ordinaryFiniteChernClasses a G n)) = 0 := by
  sorry

end WeilConjectures.PurityFiniteSetting
