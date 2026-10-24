/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.BaseChangeCoherence
public import WeilConjectures.TraceFormula.HomologyWeilLowerStar
public import WeilConjectures.TraceFormula.WeilSheafLowerStar
public import WeilConjectures.TraceFormula.WeilTrace
public import WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar

/-!

# Homology sheaves of the lower shriek of Weil objects along a finite morphism

Let `f : X ⟶ Y` be a finite morphism with automorphisms `e_X`, `e_Y` such that
`e_X ≫ f = f ≫ e_Y`. For a Weil object `K` for `e_X`, the homology sheaves of the lower shriek
`Rf_!^Weil K` are the pushforwards of the homology sheaves of `K`, as Weil sheaves for `e_Y`:
```
Hʲ(Rf_!^Weil K) ≅ f_* Hʲ(K)
```
(`ProEtale.CondensedRing.nonempty_homologyFunctor_weilLowerShriek_iso`). It is the composite of

- `Rf_!^Weil K ≅ Rf_*^Weil K` for proper `f`
  (`ProEtale.CondensedRing.weilLowerShriekIsoWeilLowerStar`), through
  `Rf_! ≅ Rf_*` and the identification of the compact-support base change with the direct-image
  base change for proper vertical maps
  (`boundedConstructibleLowerShriekBaseChange_padicAlgCl_of_isProper`, blueprint
  `def-exchange-projection`);
- `Hʲ(Rf_*^Weil K) ≅ f_* Hʲ(K)` for finite `f`
  (`ProEtale.CondensedRing.nonempty_homologyFunctor_weilLowerStar_iso`): the pushforward along a
  finite morphism is exact, so `Rf_*` is computed levelwise and commutes with homology, and the
  derived base-change morphism of the Frobenius square induces the underived one on homology.

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (eX : X ≅ X) (eY : Y ≅ Y) {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom)

/-- **`Rf_! ≅ Rf_*` for Weil objects** along a proper morphism `f`: the isomorphism
`Rf_! ≅ Rf_*` (`boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl`) is compatible with the
Frobenius structures, the compact-support base change of the Frobenius square being the
direct-image base change for proper vertical maps
(`boundedConstructibleLowerShriekBaseChange_padicAlgCl_of_isProper`). -/
noncomputable def weilLowerShriekIsoWeilLowerStar [IsProper f.left]
    (K : WeilBoundedConstructible ℓ eX.hom) :
    (weilLowerShriek ℓ eX eY hf).obj K ≅ (weilLowerStar ℓ eX eY f hf).obj K :=
  IsoAlgebra.isoMk ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).app
    K.carrier) (by
    rw [← IsoAlgebra.str_hom, ← IsoAlgebra.str_hom, weilLowerShriek_obj_str, weilLowerStar_obj_str]
    have nat := (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom.naturality
      K.str.hom
    have hp := boundedConstructibleLowerShriekBaseChange_padicAlgCl_of_isProper ℓ
      (weilFrobeniusSquare eX eY hf) K.carrier
    simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, asIso_hom, Category.assoc,
      weilLowerShriekComparison_hom]
    rw [nat, reassoc_of% hp]
    rfl)

/-- **Homology of the pushforward of Weil objects along a finite morphism**: for finite `f`, the
Weil sheaf `Hʲ(Rf_*^Weil K)` for `e_Y` is the pushforward `f_* Hʲ(K)` of the Weil sheaf `Hʲ(K)`.
The pushforward along a finite morphism is exact, so `Rf_*` is computed levelwise and commutes
with homology, and on homology the derived base-change morphism of the Frobenius square is the
base-change morphism of module objects. -/
theorem nonempty_homologyFunctor_weilLowerStar_iso [IsFinite f.left]
    (K : WeilBoundedConstructible ℓ eX.hom) (j : ℤ) :
    Nonempty ((WeilBoundedConstructible.homologyFunctor ℓ eY j).obj
        ((weilLowerStar ℓ eX eY f hf).obj K) ≅
      (weilSheafLowerStar ℓ eX eY hf).obj
        ((WeilBoundedConstructible.homologyFunctor ℓ eX j).obj K)) := by
  have := locallyOfFinitePresentation_left f
  have := preservesFiniteColimits_lowerStar_of_isFinite (Profinite.padicAlgClRingObj ℓ) f.left
  have sq : CommSq eX.hom f f eY.hom := ⟨hf⟩
  have : IsIso (boundedConstructibleBaseChange (Profinite.padicAlgClRingObj ℓ) ℓ sq) :=
    isIso_weilLowerStarComparison ℓ eX eY f hf
  have : IsIso eX.hom.left := inferInstanceAs (IsIso ((Over.forget _).map eX.hom))
  have : IsIso eY.hom.left := inferInstanceAs (IsIso ((Over.forget _).map eY.hom))
  have : IsIso (Adjunction.exchangeRight
      (upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f.left)
      (upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f.left)
      (upperStarSquareComparison (Profinite.padicAlgClRingObj ℓ)
        (commSq_left_of_comp_eq eX eY hf))) :=
    isIso_lowerStarBaseChange_of_isIso _ (commSq_left_of_comp_eq eX eY hf)
  obtain ⟨iso⟩ := IsoAlgebra.nonempty_mapOfNatIso_liftComparison_obj_iso
    (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f.left)
    (leftDerivedUpperStarSquareComparison ℓ sq)
    (upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f.left)
    (upperStarSquareComparison (Profinite.padicAlgClRingObj ℓ) (commSq_left_of_comp_eq eX eY hf))
    ((eY.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧.leftDerivedFunctorHomologyFunctorIso j)
    ((eX.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧.leftDerivedFunctorHomologyFunctorIso j)
    ((f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧.rightDerivedFunctorHomologyFunctorIso j)
    (Adjunction.homologyFunctor_map_exchangeRight_derivedAdjunction
      (upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f.left)
      (upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f.left)
      (upperStarSquareComparison (Profinite.padicAlgClRingObj ℓ) (commSq_left_of_comp_eq eX eY hf))
      (leftDerivedUpperStarSquareComparison ℓ sq)
      (fun K ↦ Functor.leftDerivedFunctorSquareIso_hom_app _ _ _ K) j)
    (boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ f)
    (boundedConstructibleLowerStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ f)
    (boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ eY.hom)
    (boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ eX.hom)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ f K.obj K.property)
    (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj _ ℓ f K.obj K.property)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ eY.hom K.obj K.property)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ eX.hom K.obj K.property)
    rfl rfl rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
    (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ f) rfl
    (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ sq)
    (fun K ↦ heq_of_eq (boundedConstructiblePullbackSquareComparison_hom_app_hom ℓ sq K))
    (weilLowerStarComparison ℓ eX eY f hf)
    (boundedConstructibleBaseChange_eq_exchangeRight _ ℓ sq)
    (weilSheafLowerStarComparison ℓ eX eY hf) (lowerStarBaseChange_eq _ _)
  -- the isomorphism of functors, checked at the level of functors
  have iso' : weilLowerStar ℓ eX eY f hf ⋙ WeilBoundedConstructible.homologyFunctor ℓ eY j ≅
      WeilBoundedConstructible.homologyFunctor ℓ eX j ⋙ weilSheafLowerStar ℓ eX eY hf := iso
  have i := iso'.app K
  rw [Functor.comp_obj, Functor.comp_obj] at i
  exact ⟨i⟩

/-- **Homology of the lower shriek of Weil objects along a finite morphism**:
`Hʲ(Rf_!^Weil K) ≅ f_* Hʲ(K)` as Weil sheaves for `e_Y`. -/
theorem nonempty_homologyFunctor_weilLowerShriek_iso [IsFinite f.left]
    (K : WeilBoundedConstructible ℓ eX.hom) (j : ℤ) :
    Nonempty ((WeilBoundedConstructible.homologyFunctor ℓ eY j).obj
        ((weilLowerShriek ℓ eX eY hf).obj K) ≅
      (weilSheafLowerStar ℓ eX eY hf).obj
        ((WeilBoundedConstructible.homologyFunctor ℓ eX j).obj K)) := by
  obtain ⟨i'⟩ := nonempty_homologyFunctor_weilLowerStar_iso ℓ eX eY hf K j
  exact ⟨(WeilBoundedConstructible.homologyFunctor ℓ eY j).mapIso
    (weilLowerShriekIsoWeilLowerStar ℓ eX eY hf K) ≪≫ i'⟩

end AlgebraicGeometry.ProEtale.CondensedRing
