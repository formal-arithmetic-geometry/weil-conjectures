/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
public import WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar

/-!

# The lower and upper shriek of Weil objects

Let `f : X ⟶ Y` be a morphism of schemes and `e_X : X ≅ X`, `e_Y : Y ≅ Y` automorphisms, and write
`Φ_X = Le_X^*` and `Φ_Y = Le_Y^*` for the Frobenius pullbacks on `Dᵇc(-)⟦Λ⟧`
(`WeilConjectures.WeilObject.BoundedConstructible.Defs`). As in
`WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar`, a functor `G` with a commutation
isomorphism `b_G` transports Weil objects by `CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso`.
This file supplies `b_G` for the extension by zero along an open immersion, and for the lower
shriek `Rf_!^c = i_! ⋙ Rg_*` and the upper shriek `Rf^!(c) = Rg^! ⋙ i^*` attached to an
explicit compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`.

The compactification is required to be *Frobenius compatible*: it comes with an automorphism
`e_Z : Z ≅ Z` such that `e_X ≫ i = i ≫ e_Z` (`hi`) and `e_Z ≫ g = g ≫ e_Y` (`hg`). This is the
case for a compactification descended from `𝔽_q`, with `e_Z` the Frobenius of `Z`. Independence
of the compactification is not treated, and nothing is said about the compactification
`compactificationOverField k f` chosen by Nagata's theorem.

* **Extension by zero.** For an open immersion `j : U ⟶ X` with `e_U ≫ j = j ≫ e_X`, the square
  is cartesian (its horizontal maps are isomorphisms), and the comparison
  `j_! ⋙ Φ_X ≅ Φ_U ⋙ j_!` is base change for extension by zero
  (`boundedConstructibleOpenImmersionLowerShriekBaseChangeIso`)
  (`ProEtale.CondensedRing.weilOpenImmersionLowerShriekComparison`).
* **Lower shriek.** The comparison `b_! : Rf_!^c ⋙ Φ_Y ≅ Φ_X ⋙ Rf_!^c` is the pasting
  ```
  i_! ⋙ Rg_* ⋙ Φ_Y ≅ i_! ⋙ Φ_Z ⋙ Rg_* ≅ Φ_X ⋙ i_! ⋙ Rg_*
  ```
  of the base change isomorphism along the Frobenius square of `g`
  (`ProEtale.CondensedRing.weilLowerStarComparison`) and the extension-by-zero comparison of `i`
  (`ProEtale.CondensedRing.weilLowerShriekComparison`).
* **Upper shriek.** For `g` proper with `Rg_* ⊣ Rg^!`, the mate of the inverse of the base change
  isomorphism `Rg_* ⋙ Φ_Y ≅ Φ_Z ⋙ Rg_*` is a natural transformation
  `Rg^! ⋙ Φ_Z ⟶ Φ_Y ⋙ Rg^!` (`ProEtale.CondensedRing.weilProperUpperShriekComparison`). The
  comparison `b^! : Rf^!(c) ⋙ Φ_X ≅ Φ_Y ⋙ Rf^!(c)` is its pasting with the pullback comparison
  `i^* ⋙ Φ_X ≅ Φ_Z ⋙ i^*` (`ProEtale.CondensedRing.weilUpperShriekComparison`).

## Sorried input

- `ProEtale.CondensedRing.isIso_weilProperUpperShriekComparison`: the mate
  `Rg^! ⋙ Φ_Z ⟶ Φ_Y ⋙ Rg^!` is an isomorphism. The mate of an isomorphism is not an isomorphism
  in general; it is here because `Φ_Z` and `Φ_Y` are equivalences, with inverses the pullbacks
  along `e_Z⁻¹` and `e_Y⁻¹`: the mate is then conjugate to the inverse isomorphism under these
  equivalences. As for `isIso_boundedConstructibleBaseChange_of_isIso`, making this precise needs
  the identity isomorphism `L(𝟙 X)^* ≅ 𝟭` of the derived pullback on module objects.

## Main definitions

- `ProEtale.CondensedRing.weilOpenImmersionLowerShriek`: the extension by zero `j_!` of Weil
  objects along an open immersion.
- `ProEtale.CondensedRing.weilLowerShriek`: the lower shriek `Rf_!^c` of Weil objects for a
  Frobenius compatible compactification `c`.
- `ProEtale.CondensedRing.weilUpperShriek`: the upper shriek `Rf^!(c)` of Weil objects for a
  Frobenius compatible compactification `c`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-! ### The extension by zero along an open immersion -/

section OpenImmersion

variable {U X : Scheme.{u}} [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
  [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
  [IsSeparated (U ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
  [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
  (eU : U ≅ U) (eX : X ≅ X) [eU.hom.IsOver (Spec (.of k))] [eX.hom.IsOver (Spec (.of k))]
  (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))] (hj : eU.hom ≫ j = j ≫ eX.hom)

/-- The Frobenius comparison `j_! ⋙ Le_X^* ≅ Le_U^* ⋙ j_!` of the extension by zero along an
open immersion `j` with `e_U ≫ j = j ≫ e_X`: base change for extension by zero, the square being
cartesian since its horizontal maps `e_U` and `e_X` are isomorphisms. -/
noncomputable def weilOpenImmersionLowerShriekComparison :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ k j ⋙
        boundedConstructibleUpperStar Λ ℓ k eX.hom ≅
      boundedConstructibleUpperStar Λ ℓ k eU.hom ⋙
        boundedConstructibleOpenImmersionLowerShriek Λ ℓ k j :=
  boundedConstructibleOpenImmersionLowerShriekBaseChangeIso Λ ℓ k
    (IsPullback.of_horiz_isIso ⟨hj⟩)

/-- The extension by zero `j_!` of Weil objects along an open immersion: a Weil object
`(K, φ_K)` for `e_U` is sent to `j_! K` with the structure isomorphism
`Φ_X j_! K ≅ j_! Φ_U K ≅ j_! K`. -/
noncomputable def weilOpenImmersionLowerShriek :
    WeilBoundedConstructible Λ ℓ k eU ⥤ WeilBoundedConstructible Λ ℓ k eX :=
  IsoAlgebra.mapOfNatIso (weilOpenImmersionLowerShriekComparison Λ ℓ k eU eX j hj)

@[simp]
lemma weilOpenImmersionLowerShriek_obj_carrier (K : WeilBoundedConstructible Λ ℓ k eU) :
    ((weilOpenImmersionLowerShriek Λ ℓ k eU eX j hj).obj K).carrier =
      (boundedConstructibleOpenImmersionLowerShriek Λ ℓ k j).obj K.carrier :=
  rfl

/-- The extension by zero of Weil objects lifts the extension by zero on `Dᵇc(-)⟦Λ⟧` along the
forgetful functors. -/
lemma weilOpenImmersionLowerShriek_comp_forget :
    weilOpenImmersionLowerShriek Λ ℓ k eU eX j hj ⋙ WeilBoundedConstructible.forget Λ ℓ k eX =
      WeilBoundedConstructible.forget Λ ℓ k eU ⋙
        boundedConstructibleOpenImmersionLowerShriek Λ ℓ k j :=
  rfl

end OpenImmersion

/-! ### The upper shriek along a proper morphism -/

section Proper

variable {Z Y : Scheme.{u}} [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
  [IsSeparated (Z ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
  [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
  (eZ : Z ≅ Z) (eY : Y ≅ Y) [eZ.hom.IsOver (Spec (.of k))] [eY.hom.IsOver (Spec (.of k))]
  (g : Z ⟶ Y) [g.IsOver (Spec (.of k))] (hg : eZ.hom ≫ g = g ≫ eY.hom)
  [(boundedConstructibleLowerStar Λ ℓ k g).IsLeftAdjoint]

/-- The Frobenius comparison `Rg^! ⋙ Le_Z^* ⟶ Le_Y^* ⋙ Rg^!` of the right adjoint `Rg^!` of
`Rg_*`: the mate, for the adjunction `Rg_* ⊣ Rg^!` on both sides, of the inverse
`Le_Z^* ⋙ Rg_* ⟶ Rg_* ⋙ Le_Y^*` of the base change isomorphism `weilLowerStarComparison`. -/
noncomputable def weilProperUpperShriekComparison :
    (boundedConstructibleLowerStar Λ ℓ k g).rightAdjoint ⋙
        boundedConstructibleUpperStar Λ ℓ k eZ.hom ⟶
      boundedConstructibleUpperStar Λ ℓ k eY.hom ⋙
        (boundedConstructibleLowerStar Λ ℓ k g).rightAdjoint :=
  (mateEquiv (Adjunction.ofIsLeftAdjoint (boundedConstructibleLowerStar Λ ℓ k g))
    (Adjunction.ofIsLeftAdjoint (boundedConstructibleLowerStar Λ ℓ k g))
    (TwoSquare.mk _ _ _ _ (asIso (weilLowerStarComparison Λ ℓ k eZ eY g hg)).inv)).natTrans

/-- The Frobenius comparison of `Rg^!` is an isomorphism, the Frobenius pullbacks being
equivalences. See the module docstring for the argument. -/
instance isIso_weilProperUpperShriekComparison :
    IsIso (weilProperUpperShriekComparison Λ ℓ k eZ eY g hg) :=
  sorry

end Proper

/-! ### The lower and upper shriek along a compactification -/

section Compactification

variable {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
  [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
  (eX : X ≅ X) (eY : Y ≅ Y) [eX.hom.IsOver (Spec (.of k))] [eY.hom.IsOver (Spec (.of k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of k))] (c : Compactification f)
  (eZ : c.Z ≅ c.Z) [eZ.hom.IsOver (Spec (.of k))]
  (hi : eX.hom ≫ c.i = c.i ≫ eZ.hom) (hg : eZ.hom ≫ c.g = c.g ≫ eY.hom)

section LowerShriek

/-- The Frobenius comparison `b_! : Rf_!^c ⋙ Le_Y^* ≅ Le_X^* ⋙ Rf_!^c` of the lower shriek
`Rf_!^c = i_! ⋙ Rg_*` attached to a compactification `c = (X ⟶[i] Z ⟶[g] Y)` with a compatible
automorphism `e_Z` of `Z`: the pasting
`i_! ⋙ Rg_* ⋙ Φ_Y ≅ i_! ⋙ Φ_Z ⋙ Rg_* ≅ Φ_X ⋙ i_! ⋙ Rg_*` of the base change isomorphism of `g`
and the extension-by-zero comparison of `i`. -/
noncomputable def weilLowerShriekComparison :
    boundedConstructibleLowerShriekOfCompactification Λ ℓ k c ⋙
        boundedConstructibleUpperStar Λ ℓ k eY.hom ≅
      boundedConstructibleUpperStar Λ ℓ k eX.hom ⋙
        boundedConstructibleLowerShriekOfCompactification Λ ℓ k c :=
  Functor.associator (boundedConstructibleOpenImmersionLowerShriek Λ ℓ k c.i)
      (boundedConstructibleLowerStar Λ ℓ k c.g) (boundedConstructibleUpperStar Λ ℓ k eY.hom) ≪≫
    Functor.isoWhiskerLeft _ (asIso (weilLowerStarComparison Λ ℓ k eZ eY c.g hg)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (weilOpenImmersionLowerShriekComparison Λ ℓ k eX eZ c.i hi) _ ≪≫
    Functor.associator (boundedConstructibleUpperStar Λ ℓ k eX.hom)
      (boundedConstructibleOpenImmersionLowerShriek Λ ℓ k c.i)
      (boundedConstructibleLowerStar Λ ℓ k c.g)

/-- The lower shriek `Rf_!^c` of Weil objects along a Frobenius compatible compactification `c`:
a Weil object `(K, φ_K)` for `e_X` is sent to `Rf_!^c K` with the structure isomorphism
`Φ_Y Rf_!^c K ≅ Rf_!^c Φ_X K ≅ Rf_!^c K` given by `weilLowerShriekComparison` and
`Rf_!^c φ_K`. -/
noncomputable def weilLowerShriek :
    WeilBoundedConstructible Λ ℓ k eX ⥤ WeilBoundedConstructible Λ ℓ k eY :=
  IsoAlgebra.mapOfNatIso (weilLowerShriekComparison Λ ℓ k eX eY c eZ hi hg)

@[simp]
lemma weilLowerShriek_obj_carrier (K : WeilBoundedConstructible Λ ℓ k eX) :
    ((weilLowerShriek Λ ℓ k eX eY c eZ hi hg).obj K).carrier =
      (boundedConstructibleLowerShriekOfCompactification Λ ℓ k c).obj K.carrier :=
  rfl

lemma weilLowerShriek_obj_str (K : WeilBoundedConstructible Λ ℓ k eX) :
    ((weilLowerShriek Λ ℓ k eX eY c eZ hi hg).obj K).str =
      (weilLowerShriekComparison Λ ℓ k eX eY c eZ hi hg).app K.carrier ≪≫
        (boundedConstructibleLowerShriekOfCompactification Λ ℓ k c).mapIso K.str :=
  IsoAlgebra.mapOfNatIso_obj_str _ K

/-- The lower shriek of Weil objects lifts the lower shriek on `Dᵇc(-)⟦Λ⟧` along the forgetful
functors. -/
lemma weilLowerShriek_comp_forget :
    weilLowerShriek Λ ℓ k eX eY c eZ hi hg ⋙ WeilBoundedConstructible.forget Λ ℓ k eY =
      WeilBoundedConstructible.forget Λ ℓ k eX ⋙
        boundedConstructibleLowerShriekOfCompactification Λ ℓ k c :=
  rfl

end LowerShriek

section UpperShriek

variable [(boundedConstructibleLowerStar Λ ℓ k c.g).IsLeftAdjoint]

/-- The Frobenius comparison `b^! : Rf^!(c) ⋙ Le_X^* ≅ Le_Y^* ⋙ Rf^!(c)` of the upper shriek
`Rf^!(c) = Rg^! ⋙ i^*` attached to a compactification `c = (X ⟶[i] Z ⟶[g] Y)` with a compatible
automorphism `e_Z` of `Z`: the pasting
`Rg^! ⋙ i^* ⋙ Φ_X ≅ Rg^! ⋙ Φ_Z ⋙ i^* ≅ Φ_Y ⋙ Rg^! ⋙ i^*` of the pullback comparison of `i` and
the Frobenius comparison of `Rg^!`. -/
noncomputable def weilUpperShriekComparison :
    boundedConstructibleUpperShriekOfCompactification Λ ℓ k c ⋙
        boundedConstructibleUpperStar Λ ℓ k eX.hom ≅
      boundedConstructibleUpperStar Λ ℓ k eY.hom ⋙
        boundedConstructibleUpperShriekOfCompactification Λ ℓ k c :=
  Functor.associator (boundedConstructibleLowerStar Λ ℓ k c.g).rightAdjoint
      (boundedConstructibleUpperStar Λ ℓ k c.i) (boundedConstructibleUpperStar Λ ℓ k eX.hom) ≪≫
    Functor.isoWhiskerLeft _ (weilUpperStarComparison Λ ℓ k eX eZ c.i hi) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (weilProperUpperShriekComparison Λ ℓ k eZ eY c.g hg)) _ ≪≫
    Functor.associator (boundedConstructibleUpperStar Λ ℓ k eY.hom)
      (boundedConstructibleLowerStar Λ ℓ k c.g).rightAdjoint
      (boundedConstructibleUpperStar Λ ℓ k c.i)

/-- The upper shriek `Rf^!(c)` of Weil objects along a Frobenius compatible compactification
`c`: a Weil object `(K, φ_K)` for `e_Y` is sent to `Rf^!(c) K` with the structure isomorphism
`Φ_X Rf^!(c) K ≅ Rf^!(c) Φ_Y K ≅ Rf^!(c) K` given by `weilUpperShriekComparison` and
`Rf^!(c) φ_K`. -/
noncomputable def weilUpperShriek :
    WeilBoundedConstructible Λ ℓ k eY ⥤ WeilBoundedConstructible Λ ℓ k eX :=
  IsoAlgebra.mapOfNatIso (weilUpperShriekComparison Λ ℓ k eX eY c eZ hi hg)

@[simp]
lemma weilUpperShriek_obj_carrier (K : WeilBoundedConstructible Λ ℓ k eY) :
    ((weilUpperShriek Λ ℓ k eX eY c eZ hi hg).obj K).carrier =
      (boundedConstructibleUpperShriekOfCompactification Λ ℓ k c).obj K.carrier :=
  rfl

lemma weilUpperShriek_obj_str (K : WeilBoundedConstructible Λ ℓ k eY) :
    ((weilUpperShriek Λ ℓ k eX eY c eZ hi hg).obj K).str =
      (weilUpperShriekComparison Λ ℓ k eX eY c eZ hi hg).app K.carrier ≪≫
        (boundedConstructibleUpperShriekOfCompactification Λ ℓ k c).mapIso K.str :=
  IsoAlgebra.mapOfNatIso_obj_str _ K

/-- The upper shriek of Weil objects lifts the upper shriek on `Dᵇc(-)⟦Λ⟧` along the forgetful
functors. -/
lemma weilUpperShriek_comp_forget :
    weilUpperShriek Λ ℓ k eX eY c eZ hi hg ⋙ WeilBoundedConstructible.forget Λ ℓ k eX =
      WeilBoundedConstructible.forget Λ ℓ k eY ⋙
        boundedConstructibleUpperShriekOfCompactification Λ ℓ k c :=
  rfl

end UpperShriek

end Compactification

end AlgebraicGeometry.ProEtale.CondensedRing
