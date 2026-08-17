/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.Mathlib.Algebra.Category.Ring.Constructions

/-!
# Base change of the subscheme cut out by an ideal sheaf

The affine cover of the closed subscheme `V(I)` cut out by a quasi-coherent ideal `I` is
obtained by base change: over an affine open `U` of `X`, the square formed by the chart
`Spec (Γ(X, U) ⧸ I(U)) ⟶ V(I)` of `I.subschemeCover`, the closed immersion `I.subschemeι`
and `U.2.fromSpec` is a pullback
(`AlgebraicGeometry.Scheme.IdealSheafData.isPullback_subschemeCover_map`).

Pasting this square with `Spec` of the pushout square `CommRingCat.isPushout_quotient`
computes the base change of `I.subschemeι` along an arbitrary affine probe
`Spec.map φ ≫ U.2.fromSpec`: it is the closed immersion cut out by the extended ideal
`I(U)·S` (`AlgebraicGeometry.Scheme.IdealSheafData.isPullback_subschemeι_specMap_fromSpec`).

## Main results

- `AlgebraicGeometry.Scheme.IdealSheafData.isPullback_subschemeCover_map`
- `AlgebraicGeometry.Scheme.IdealSheafData.isPullback_subschemeι_specMap_fromSpec`
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)

/-- The affine chart of the subscheme over an affine open is the fibre product: the
square with the chart `Spec (Γ(X, U) ⧸ I(U)) ⟶ V(I)` and `fromSpec` is a pullback. -/
lemma isPullback_subschemeCover_map :
    IsPullback (I.subschemeCover.f U)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))))
      I.subschemeι U.2.fromSpec := by
  refine (IsOpenImmersion.isPullback _ _ _ _ ?_ ?_).flip
  · exact (I.subschemeCover_map_subschemeι U).trans (I.glueDataObjι_ι U)
  · rw [U.2.opensRange_fromSpec, opensRange_subschemeCover_map]

/-- **The subscheme of an ideal sheaf base changes to the subscheme of the extended
ideal.** Along a morphism `Spec S ⟶ X` of the form `Spec.map φ ≫ U.2.fromSpec` with `U` an
affine open, the base change of `I.subschemeι` is `Spec` of the quotient of `S` by the
extension of `I(U)` along `φ`. -/
lemma isPullback_subschemeι_specMap_fromSpec {S : CommRingCat.{u}} (φ : Γ(X, U.1) ⟶ S) :
    IsPullback (Spec.map (CommRingCat.ofHom (Ideal.quotientMap ((I.ideal U).map φ.hom) φ.hom
        Ideal.le_comap_map)) ≫ I.subschemeCover.f U)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((I.ideal U).map φ.hom))))
      I.subschemeι (Spec.map φ ≫ U.2.fromSpec) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_quotient φ (I.ideal U))).paste_horiz
      (I.isPullback_subschemeCover_map U)

end AlgebraicGeometry.Scheme.IdealSheafData
