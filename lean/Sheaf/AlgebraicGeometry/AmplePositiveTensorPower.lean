/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.SectionNonvanishingZeroLocus
import WeilConjectures.AlgebraicGeometry.Modules.AffineComplement

/-! # Positive tensor powers preserve absolute ampleness

Source: Stacks Project, Properties Definition 01PS and Lemma 01PT;
Varieties Lemma 09NX, powering the component bundles.
(blueprint: lem-sc-ample-positive-tensor-power).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

private theorem nonvanishingLocus_app_one {X : Scheme.{u}} (M : X.Modules)
    [M.IsInvertible] (a : 𝟙_ X.Modules ⟶ M) :
    nonvanishingLocus M (a.app ⊤ (unitSectionsEquiv ⊤ 1)) =
      ((Hom.zeroLocus a).support.compl : Set X) := by
  have h : homOfGlobalSection M (a.app ⊤ (unitSectionsEquiv ⊤ 1)) = a := by
    refine (SheafOfModules.unitHomEquiv M).injective (Subtype.ext (funext fun U ↦ ?_))
    change Hom.app (homOfGlobalSection M (a.app ⊤ (unitSectionsEquiv ⊤ 1)))
      U.unop (1 : Γ(X, U.unop)) = Hom.app a U.unop (1 : Γ(X, U.unop))
    rw [homOfGlobalSection_app_one, ← Hom.app_presheaf_map]
    exact congrArg (Hom.app a U.unop)
      (map_one (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op).hom :)
  rw [nonvanishingLocus_eq_compl_support_zeroLocus, h]

/-- A positive tensor power of an ample invertible module is ample.

Source: Stacks Project, Properties Definition 01PS and Lemma 01PT;
Varieties Lemma 09NX, first two paragraphs.
(blueprint: lem-sc-ample-positive-tensor-power).

Proof: keep compactness from ampleness of M. At any point choose a positive exponent n,
a section s of M^n, and its affine nonvanishing open U containing the point. The kth
power of s is a global section of (M^n)^k. Transport it through the tensor-power
isomorphisms (M^n)^k ≅ M^(n*k) ≅ M^(k*n) ≅ (M^k)^n. In a local frame of M the
coefficient of the new section is the kth power of that of s. Since k is positive,
that coefficient is a unit in each local ring exactly when the original coefficient
is a unit. Consequently the nonvanishing locus stays U, and n, U and the transported
section witness ampleness of M^k at the chosen point. On the empty scheme the
pointwise condition is vacuous. Positivity is necessary: M^0 is the structure module,
which need not be ample on a nonaffine scheme.
-/
theorem isAmple_positive_tensorPow {X : Scheme.{u}} (M : X.Modules) [M.IsInvertible]
    (hM : IsAmple X M) (k : ℕ) (hk : 0 < k) : IsAmple X (M.tensorPow k)  := by
  refine ⟨hM.1, fun x ↦ ?_⟩
  obtain ⟨n, hn, s, U, hx, hU, hs⟩ := hM.2 x
  let e : (M.tensorPow n).tensorPow k ≅ (M.tensorPow k).tensorPow n :=
    (M.tensorPowMulIso n k).symm ≪≫
      eqToIso (congrArg M.tensorPow (Nat.mul_comm n k)) ≪≫ M.tensorPowMulIso k n
  let a := tensorPowSection (homOfGlobalSection (M.tensorPow n) s) k
  let t := (a ≫ e.hom).app ⊤ (unitSectionsEquiv ⊤ 1)
  have ht : nonvanishingLocus ((M.tensorPow k).tensorPow n) t =
      nonvanishingLocus (M.tensorPow n) s := by
    have := IsInvertible.sheafOfModules_isInvertible ((M.tensorPow k).tensorPow n)
    have := IsInvertible.sheafOfModules_isInvertible ((M.tensorPow n).tensorPow k)
    rw [nonvanishingLocus_app_one, nonvanishingLocus_eq_compl_support_zeroLocus]
    have he := Hom.zeroLocus_eq_of_arrowIso a (a ≫ e.hom)
      (Arrow.isoMk (Iso.refl _) e (by simp))
    rw [← he, compl_support_zeroLocus_tensorPowSection (M.tensorPow n) _ hk]
  refine ⟨n, hn, t, U, hx, hU, fun y ↦ ?_⟩
  exact (hs y).trans (Set.ext_iff.mp ht y).symm

end AlgebraicGeometry.Scheme.Modules
