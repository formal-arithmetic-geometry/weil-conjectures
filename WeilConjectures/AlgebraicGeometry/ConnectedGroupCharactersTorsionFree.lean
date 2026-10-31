/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StandardGroupSchemes
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.Regular
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Polynomial.Laurent

/-!
# Characters of a smooth connected affine group have no torsion

Source: Milne, Algebraic Groups (2017), Proposition 18.19, proof, printed p.392,
and Theorem 18.25, proof, printed p.393
(blueprint: lem-sfb-connected-group-characters-torsion-free).

Characters are morphisms of group schemes to the multiplicative group, expressed
using the existing `IsMonHom` predicate. Multiplication, powers and the trivial
character are the pointwise operations on morphisms into a group object.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- Characters of a smooth connected affine group of finite type over an
algebraically closed field are torsion free. Source: Milne, Algebraic Groups
(2017), Proposition 18.19, proof, printed p.392, and Theorem 18.25, proof,
printed p.393 (blueprint: lem-sfb-connected-group-characters-torsion-free).

Proof plan:
1. Write G = Spec A. Smoothness gives regularity and local Noetherianity
   (`lem-weil-pbc-smooth-scheme-over-field-regular`). The identity point makes G
   nonempty; connectedness and regularity give integrality
   (`lem-sc-regular-connected-integral`), hence A is a domain
   (`def-pc-integral-scheme`).
2. By affine contravariance (`def-weil-affine-spectrum`), the character gives
   an F-algebra map F[t,t⁻¹] → A. Let u be the image of t. The Hopf multiplication
   of `def-sc-gm-ga` identifies the power hypothesis with u^n = 1.
3. Factor T^n - 1 into linear factors over F
   (`lem-weil-alg-closed-linear-factorization`). Evaluating at u gives a zero
   product in A, so u is a scalar root. This also works with repeated roots.
4. The counit A → F from `def-sc-group-scheme` sends u to 1 because the
   character preserves the identity. Thus that scalar is 1. The algebra map
   agrees with the trivial character on scalars, t and t⁻¹, hence on all Laurent
   polynomials (`def-weil-laurent-polynomial-ring`). Affine contravariance gives
   equality of morphisms, as asserted. -/
theorem character_eq_one_of_pow_eq_one
    (F : Type u) [Field F] [IsAlgClosed F]
    (G : Over (Spec (.of F))) [GrpObj G] [IsAffine G.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [Smooth G.hom] [ConnectedSpace G.left]
    (n : ℕ) (hn : 1 ≤ n)
    (χ : G ⟶ StandardGroupSchemes.multiplicative F) [IsMonHom χ]
    (hχ : χ ^ n = 1) : χ = 1 := by
  sorry

end AlgebraicGeometry
