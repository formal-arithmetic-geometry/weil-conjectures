/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
public import WeilConjectures.WeilObject.BoundedConstructible.Defs

/-!

# The lower and upper shriek of Weil objects

Let `f : X ⟶ Y` be a morphism of schemes and `e_X : X ≅ X`, `e_Y : Y ≅ Y` automorphisms
compatible with `f`, that is `e_X ≫ f = f ≫ e_Y` (`hf`), and write `Φ_X = Le_X^*` and
`Φ_Y = Le_Y^*` for the Frobenius pullbacks on `Dᵇc(-)⟦ℚ̲̄_ℓ⟧`
(`WeilConjectures.WeilObject.BoundedConstructible.Defs`). As in
`WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar`, a functor `G` with a commutation
isomorphism `b_G` transports Weil objects by `CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso`.
This file supplies `b_G` for the lower shriek `Rf_!^c = i_! ⋙ Rg_*` and the upper shriek
`Rf^!(c) = Rg^! ⋙ i^*` attached to an explicit compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`.

The Frobenius square `e_X ≫ f = f ≫ e_Y` is cartesian, its horizontal maps being isomorphisms
(`ProEtale.CondensedRing.weilFrobeniusSquare`). Write `c' = c.baseChange sq` for the base change
of `c` along it, a compactification of `f` again.

* **Lower shriek.** The comparison `b_! : Rf_!^c ⋙ Φ_Y ≅ Φ_X ⋙ Rf_!^c`
  (`ProEtale.CondensedRing.weilLowerShriekComparison`) is the compact-support base-change
  morphism of the Frobenius square with the compactification `c` on both sides
  (`boundedConstructibleLowerShriekBaseChangeSelf`, which goes through the identification of the
  base-changed compactification `c'` with `c`). It is an isomorphism by the compactly supported
  base change theorem (`isIso_boundedConstructibleLowerShriekBaseChangeSelf_padicAlgCl`).
* **Upper shriek.** The comparison `b^! : Rf^!(c) ⋙ Φ_X ⟶ Φ_Y ⋙ Rf^!(c)` is the mate of the
  inverse of `b_!` for the adjunction `Rf_!^c ⊣ Rf^!(c)` on both sides
  (`ProEtale.CondensedRing.weilUpperShriekComparison`).

## Sorried input

- `ProEtale.CondensedRing.isIso_weilUpperShriekComparison`: the mate `b^!` is an isomorphism.
  The mate of an isomorphism is not an isomorphism in general; it is here because `Φ_X` and
  `Φ_Y` are equivalences, with inverses the pullbacks along `e_X⁻¹` and `e_Y⁻¹`, so that `b^!`
  is conjugate to `b_!` under these equivalences. Making this precise needs the identity
  isomorphism `L(𝟙 X)^* ≅ 𝟭` of the derived pullback on module objects.

The compactly supported base change theorem, and the identification
`Rf_!^{c'} ≅ Rf_!^c`, are inputs from
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek`.

## Main definitions

- `ProEtale.CondensedRing.weilLowerShriek`: the lower shriek `Rf_!^c` of Weil objects.
- `ProEtale.CondensedRing.weilUpperShriek`: the upper shriek `Rf^!(c)` of Weil objects.

-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
  [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
  (eX : X ≅ X) (eY : Y ≅ Y) [eX.hom.IsOver (Spec (.of k))] [eY.hom.IsOver (Spec (.of k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of k))] (hf : eX.hom ≫ f = f ≫ eY.hom)
  (c : Compactification f)

omit [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [eX.hom.IsOver (Spec (.of k))]
  [eY.hom.IsOver (Spec (.of k))] [f.IsOver (Spec (.of k))] in
include hf in
/-- The Frobenius square `e_X ≫ f = f ≫ e_Y` is cartesian, its horizontal maps being
isomorphisms. -/
theorem weilFrobeniusSquare : IsPullback eX.hom f f eY.hom :=
  IsPullback.of_horiz_isIso ⟨hf⟩

/-! ### The lower shriek -/

section LowerShriek

/-- The Frobenius comparison `b_! : Rf_!^c ⋙ Le_Y^* ≅ Le_X^* ⋙ Rf_!^c` of the lower shriek
attached to a compactification `c` of `f`: the compact-support base-change morphism
`boundedConstructibleLowerShriekBaseChangeSelf` of the Frobenius square, with the same
compactification `c` on both sides, which is an isomorphism by the compactly supported base
change theorem. -/
noncomputable def weilLowerShriekComparison :
    boundedConstructibleLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) ℓ k c ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k eY.hom ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k eX.hom ⋙
        boundedConstructibleLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) ℓ k c :=
  have := isIso_boundedConstructibleLowerShriekBaseChangeSelf_padicAlgCl ℓ k c
    (weilFrobeniusSquare eX eY hf)
  asIso (boundedConstructibleLowerShriekBaseChangeSelf (Profinite.padicAlgClRingObj ℓ) ℓ k c
    (weilFrobeniusSquare eX eY hf))

lemma weilLowerShriekComparison_hom :
    (weilLowerShriekComparison ℓ k eX eY hf c).hom =
      boundedConstructibleLowerShriekBaseChangeSelf (Profinite.padicAlgClRingObj ℓ) ℓ k c
        (weilFrobeniusSquare eX eY hf) :=
  rfl

/-- The lower shriek `Rf_!^c` of Weil objects along a compactification `c` of `f`: a Weil object
`(K, φ_K)` for `e_X` is sent to `Rf_!^c K` with the structure isomorphism
`Φ_Y Rf_!^c K ≅ Rf_!^c Φ_X K ≅ Rf_!^c K` given by `weilLowerShriekComparison` and
`Rf_!^c φ_K`. -/
noncomputable def weilLowerShriek :
    WeilBoundedConstructible ℓ k eX ⥤ WeilBoundedConstructible ℓ k eY :=
  IsoAlgebra.mapOfNatIso (weilLowerShriekComparison ℓ k eX eY hf c)

@[simp]
lemma weilLowerShriek_obj_carrier (K : WeilBoundedConstructible ℓ k eX) :
    ((weilLowerShriek ℓ k eX eY hf c).obj K).carrier =
      (boundedConstructibleLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) ℓ k
        c).obj K.carrier :=
  rfl

lemma weilLowerShriek_obj_str (K : WeilBoundedConstructible ℓ k eX) :
    ((weilLowerShriek ℓ k eX eY hf c).obj K).str =
      (weilLowerShriekComparison ℓ k eX eY hf c).app K.carrier ≪≫
        (boundedConstructibleLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) ℓ k
          c).mapIso K.str :=
  IsoAlgebra.mapOfNatIso_obj_str _ K

/-- The lower shriek of Weil objects lifts the lower shriek on `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` along the forgetful
functors. -/
lemma weilLowerShriek_comp_forget :
    weilLowerShriek ℓ k eX eY hf c ⋙ WeilBoundedConstructible.forget ℓ k eY =
      WeilBoundedConstructible.forget ℓ k eX ⋙
        boundedConstructibleLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) ℓ k c :=
  rfl

end LowerShriek

/-! ### The upper shriek -/

section UpperShriek

/-- The Frobenius comparison `b^! : Rf^!(c) ⋙ Le_X^* ⟶ Le_Y^* ⋙ Rf^!(c)` of the upper shriek
attached to a compactification `c` of `f`: the mate, for the adjunction `Rf_!^c ⊣ Rf^!(c)` on
both sides, of the inverse `Φ_X ⋙ Rf_!^c ⟶ Rf_!^c ⋙ Φ_Y` of the lower shriek comparison
`weilLowerShriekComparison`. -/
noncomputable def weilUpperShriekComparison :
    boundedConstructibleUpperShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) ℓ k c ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k eX.hom ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k eY.hom ⋙
        boundedConstructibleUpperShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) ℓ k c :=
  (mateEquiv
    (boundedConstructibleUpperShriekOfCompactificationAdjunction (Profinite.padicAlgClRingObj ℓ)
      ℓ k c)
    (boundedConstructibleUpperShriekOfCompactificationAdjunction (Profinite.padicAlgClRingObj ℓ)
      ℓ k c)
    (TwoSquare.mk _ _ _ _ (weilLowerShriekComparison ℓ k eX eY hf c).inv)).natTrans

/-- The Frobenius comparison of the upper shriek is an isomorphism, the Frobenius pullbacks being
equivalences. See the module docstring for the argument. -/
instance isIso_weilUpperShriekComparison :
    IsIso (weilUpperShriekComparison ℓ k eX eY hf c) :=
  sorry

/-- The upper shriek `Rf^!(c)` of Weil objects along a compactification `c` of `f`: a Weil object
`(K, φ_K)` for `e_Y` is sent to `Rf^!(c) K` with the structure isomorphism
`Φ_X Rf^!(c) K ≅ Rf^!(c) Φ_Y K ≅ Rf^!(c) K` given by `weilUpperShriekComparison` and
`Rf^!(c) φ_K`. -/
noncomputable def weilUpperShriek :
    WeilBoundedConstructible ℓ k eY ⥤ WeilBoundedConstructible ℓ k eX :=
  IsoAlgebra.mapOfNatIso (asIso (weilUpperShriekComparison ℓ k eX eY hf c))

@[simp]
lemma weilUpperShriek_obj_carrier (K : WeilBoundedConstructible ℓ k eY) :
    ((weilUpperShriek ℓ k eX eY hf c).obj K).carrier =
      (boundedConstructibleUpperShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) ℓ k
        c).obj K.carrier :=
  rfl

lemma weilUpperShriek_obj_str (K : WeilBoundedConstructible ℓ k eY) :
    ((weilUpperShriek ℓ k eX eY hf c).obj K).str =
      (asIso (weilUpperShriekComparison ℓ k eX eY hf c)).app K.carrier ≪≫
        (boundedConstructibleUpperShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) ℓ k
          c).mapIso K.str :=
  IsoAlgebra.mapOfNatIso_obj_str _ K

/-- The upper shriek of Weil objects lifts the upper shriek on `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` along the
forgetful functors. -/
lemma weilUpperShriek_comp_forget :
    weilUpperShriek ℓ k eX eY hf c ⋙ WeilBoundedConstructible.forget ℓ k eX =
      WeilBoundedConstructible.forget ℓ k eY ⋙
        boundedConstructibleUpperShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) ℓ k c :=
  rfl

end UpperShriek

end AlgebraicGeometry.ProEtale.CondensedRing
