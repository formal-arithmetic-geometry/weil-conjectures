/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Thickening

/-!
# Locally finitely presented morphisms with unique infinitesimal lifts are étale

Source: Stacks Project, More on Morphisms, Tag 02HM (blueprint:
lem-per-lfp-unique-infinitesimal-lifts-etale).
-/

universe u

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

/--
A locally finitely presented morphism of schemes with a unique lift against every
first-order thickening of affine schemes is étale. This is the converse implication
in Stacks Project, More on Morphisms, Lemma 37.13.2 (Tag 02HM), using the affine
first-order lifting formulation of formal étaleness (Tag 02HG).

Proof steps, postponed to stage 3:
1. For each point, choose affine opens in the source and target; the induced affine
   algebra map is finitely presented by
   `lem-weil-pbc-lfp-affine-opens-finite-presentation`.
2. The lifting property restricts to the chosen affine opens, using
   `def-sbc-first-order-thickening` and `def-weil-open-immersion`.
3. For a square-zero ideal `I` in an affine algebra `D`, apply the restricted
   property to `Spec (D / I) ⟶ Spec D`; `def-weil-affine-spectrum` and
   `def-weil-closed-immersion` identify the resulting lift with a unique algebra
   lift.
4. Use `lem-per-ring-square-zero-lifts-cotangent-zero` and
   `lem-weil-pbc-etale-ring-map-iff-etale-affine` to show the affine chart is étale.
5. The affine-local criterion in `def-weil-etale-morphism` then gives that `c` is
   étale, including the vacuous case of an empty source.
(blueprint: lem-per-lfp-unique-infinitesimal-lifts-etale)
-/
theorem lfp_unique_infinitesimal_lifts_etale
    {W Z : Scheme.{u}} (c : W ⟶ Z) [LocallyOfFinitePresentation c]
    (h : ∀ (T₀ T : Scheme.{u}) (j : T₀ ⟶ T)
      [IsAffine T₀] [IsAffine T]
      (hj : IsFirstOrderThickening j)
      (a₀ : T₀ ⟶ W) (b : T ⟶ Z),
      a₀ ≫ c = j ≫ b →
      ∃! a : T ⟶ W, j ≫ a = a₀ ∧ a ≫ c = b) :
    Etale c := by
  sorry

end AlgebraicGeometry

end
