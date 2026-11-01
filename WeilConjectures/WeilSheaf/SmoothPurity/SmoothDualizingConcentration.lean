/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.TateTwist
import WeilConjectures.WeilSheaf.SmoothPurity.SmoothDualizingVanishing

/-! # Concentration of native smooth dualizing purity

The native derived category of Weil sheaves retains derived morphisms.  This statement
isolates Concentration, rather than identifying that category with fixed pairs of derived objects.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- The exceptional constant object on a smooth scheme is concentrated in degree `-2d`.

Source: current blueprint, `cor-pur-adic-and-rational-smooth-dualizing-complexes`,
smooth specialization, and `cor-coef-verdier-weil-equivariance`, exceptional adjunction.
(blueprint: lem-sf-weil-smooth-dualizing-concentration)

Proof: base change the structure morphism to the algebraic closure; separated finite type
and relative dimension `d` are preserved.  The native exceptional-forgetting comparison,
normalized by the counit of `adj`, identifies the ordinary realization of `J` on the
constant Weil complex with the geometric exceptional inverse image of the constant object.
The coefficient-stage smooth purity theorem identifies this realization with the constant
Tate line shifted by `2d`.  The Tate line is a sheaf in degree zero, so all its cohomology
outside degree `-2d` vanishes.  Forgetting a Weil sheaf is exact and conservative: it computes
cohomology by forgetting the Frobenius isomorphism and detects the zero sheaf.  Therefore
the native cohomology sheaves outside degree `-2d` vanish as well.  The canonical derived
category t-structure then gives both bounds below.  This argument only uses vanishing;
it does not identify the surviving Weil sheaf or its Frobenius action.
-/
theorem smooth_dualizing_concentration
    (J : WeilComplex k₀ l (Spec (CommRingCat.of k₀)) ⥤ WeilComplex k₀ l X)
    (adj : derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀)) ⊣ J)
    (d : ℕ) [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))] :
    ((J.obj (WeilSheaf.toComplex.obj
        (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀))))).obj.IsGE (-2 * (d : ℤ))) ∧
    ((J.obj (WeilSheaf.toComplex.obj
        (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀))))).obj.IsLE (-2 * (d : ℤ))) := by
  let K := J.obj (WeilSheaf.toComplex.obj
    (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀))))
  let b : ℤ := -2 * (d : ℤ)
  have hz : ∀ i : ℤ, i ≠ b → IsZero ((homologySheaf i).obj K) := by
    intro i hi
    exact smooth_dualizing_homology_vanishing J adj d i (by simpa [b] using hi)
  have hge : K.obj.IsGE b :=
    (_root_.DerivedCategory.isGE_iff K.obj b).2 (fun i hi ↦
      (isZero_homologySheaf_obj_iff i K).1 (hz i (ne_of_lt hi)))
  have hle : K.obj.IsLE b :=
    (_root_.DerivedCategory.isLE_iff K.obj b).2 (fun i hi ↦
      (isZero_homologySheaf_obj_iff i K).1 (hz i (ne_of_gt hi)))
  exact ⟨by simpa [K, b] using hge, by simpa [K, b] using hle⟩

end AlgebraicGeometry.WeilComplex
