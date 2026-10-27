/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CondensedTateIntegralTowerData
import Sheaf.Paper.TateTensorNormalizedSquarePair

/-! The scalar comparison square for projection-normalized Tate levels.

Source: smooth-purity transport, normalized Tate tower, Step 4.
(blueprint: lem-pur-tate-tensor-normalized-square)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

/-- For an already constructed, projection-normalized tower, its normalization
at one comparable pair agrees with every normalized finite root-line comparison.
No tower or finite comparison is constructed in this statement.

Source: current blueprint, sec-smooth-purity/sk-thm-purity-transport, Step 2;
lem-pur-normalized-tate-tensor-reductions, proof Step 4.
(blueprint: lem-pur-tate-tensor-normalized-square)

Proof: choose the ordinary balancing isomorphisms supplied by ProjectionNormalized.
They carry every integral pure root tensor to its finite projection, with the full
quotient scalar action. The transition of the strict tower is ordinary quotient
balancing. Its value after two reductions is x tensor q(c)a. On the finite side,
the roots_power and generators fields of r give the same power map and the same
scalar value on every tensor factor. At zero, tensorPower is the scalar unit
comparison, so the calculation is coefficient multiplication. The
derived_normalization field identifies the derived map with the scalar counit
followed by the single of the ordinary sheaf comparison; hence the same equality
holds after the prescribed scalar and site adjunction mates. Exact single/evaluation
and ProjectionNormalized identify these computations with the given e. The
AdicTower.transition field identifies the other map with M.normalization. The
finite root tensors are locally free, hence K-flat in their single degree, so
scalar extension of the source is also computed by a single ordinary quotient.
Equality can be checked on these single sheaves: exact restriction retains their
underlying sheaf maps, and single in a fixed degree is fully faithful. Local
scalar/root generators determine sheaf maps by tensor generation and sheafification,
so the two maps agree. Equal indices and the empty scheme use the same equations. -/
theorem tateTensor_normalizedSquare
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (d : ℕ)
    (M : AdicTower T (datum.{u} ell))
    (e : ∀ n : ℕ, M.level n ≅ (derivedRealization T ell n).obj (finiteTwist T ell n d))
    (h : M.tower = strictDerivedTower T ell d)
    (hp : ProjectionNormalized T ell hT d M e h)
    (b a : ℕ) (hab : a ≤ b)
    (r : CoefficientLineComparison
      (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1))
      (ell ^ (b + 1)) (ell ^ (a + 1))
      (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T) :
    (pbcDerivedExtend (pbcAdicQuotient T (datum.{u} ell) b a hab)).map (e b).hom ≫
        (scalarComparison T ell b a hab).hom.app (finiteTwist T ell b d) ≫
        (derivedRealization T ell a).map (proTwistMap d r) =
      (M.normalization b a hab).hom ≫ (e a).hom := by
  let cb := (hp b).choose
  let ca := (hp a).choose
  have hcb : normalizedAt T ell hT d M e h b cb := (hp b).choose_spec
  have hca : normalizedAt T ell hT d M e h a ca := (hp a).choose_spec
  exact tateTensor_normalizedSquare_of_pair T ell hT d M e h b a hab cb ca hcb hca r

end AlgebraicGeometry.Scheme.PurityIntegralTower
