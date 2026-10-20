/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Modification

/-!
# Extension by zero under a proper modification

Source: blueprint, sec-smooth-purity/sk-prop-sf-cbc,
lem-finrepair-modification-extension-zero; Stacks Project, Tags 03S6, 03S5, 03Q1, 0DDF.
(blueprint: lem-finrepair-modification-extension-zero)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Extension by zero from the isomorphism locus of a proper map has no positive higher
 direct images, and its canonical adjunction map is an isomorphism.
Source: blueprint sec-smooth-purity/sk-prop-sf-cbc, lemma of the same name;
Stacks Project, Tags 03S6, 03S5, 03Q1, 0DDF and 04JN.
(blueprint: lem-finrepair-modification-extension-zero)

Proof:
The source-library theorem
`nonempty_rightDerivedLowerStar_openImmersionLowerShriek_iso` identifies
`Rπ_*((j'_! h⁻¹ G)[0])` with `(j_! G)[0]`. Its degree-zero homology identifies
`π_* j'_! h⁻¹ G` with `j_! G`, and its positive homology vanishes.

To check the specific canonical map, write `J = j_!`, `L = π⁻¹` and `R = π_*`.
The extension-by-zero base-change isomorphism identifies `J ⋙ L` with
`h⁻¹ ⋙ j'_!`, which is fully faithful because `h` is an isomorphism and extension
by zero is fully faithful. The unit of the composite adjunction is therefore an
isomorphism. Since the unit of `J ⊣ j⁻¹` is also an isomorphism, `j⁻¹` of the
unit of `L ⊣ R`, evaluated at `J G`, is an isomorphism. The stated map is this
unit followed by `R` of the inverse base-change map, so its restriction to `U`
is an isomorphism. Both its source and target are in the essential image of
`J`, by the degree-zero identification above. The counit of `J ⊣ j⁻¹` is an
isomorphism on these objects; its naturality now proves that the stated map
itself is an isomorphism. -/
theorem modification_extension_zero
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {Y U X : Scheme.{u}} (π : Y ⟶ X) [IsProper π]
    (j : U ⟶ X) [IsOpenImmersion j] [IsIso (pullback.snd π j)]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π).homEquiv _ _
      ((@inv _ _ _ _ (etaleLowerShriekBaseChangeMap Λ π j)
        (isIso_etaleLowerShriekBaseChangeMap Λ π j)).app G)) ∧
    ∀ q : ℤ, 0 < q →
      IsZero (higherDirectImage Λ π q
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (pullback.fst π j)).obj
          ((upperStar (ModuleCat.{u + 1} Λ) (pullback.snd π j)).obj G))) := by
  let A := ModuleCat.{u + 1} Λ
  let J := openImmersionLowerShriek A j
  let L := upperStar A π
  let R := lowerStar A π
  let h := pullback.snd π j
  let j' := pullback.fst π j
  let F := (openImmersionLowerShriek A j').obj ((upperStar A h).obj G)
  let E := J.obj G
  obtain ⟨e⟩ := nonempty_rightDerivedLowerStar_openImmersionLowerShriek_iso π j j' h
    (IsPullback.of_hasPullback π j) G
  let e₀ : R.obj F ≅ E :=
    ((R.homologyRightDerivedFunctorObjSingleFunctorIso F 0) ≪≫
      R.rightDerivedZeroIsoSelf.app F).symm ≪≫
      (_root_.DerivedCategory.homologyFunctor _ 0).mapIso e ≪≫
      (_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app E
  constructor
  · let adj := upperStarLowerStarAdjunction A π
    let adjJ := openImmersionLowerShriekUpperStarAdjunction A j
    let b := etaleLowerShriekBaseChangeMap Λ π j
    have hb : IsIso b := isIso_etaleLowerShriekBaseChangeMap Λ π j
    have : (upperStar A h).IsEquivalence := isEquivalence_upperStar A h
    have : (upperStar A h ⋙ etaleLowerShriek A j' inferInstance).Full :=
      inferInstanceAs (upperStar A h ⋙ openImmersionLowerShriek A j').Full
    have : (upperStar A h ⋙ etaleLowerShriek A j' inferInstance).Faithful :=
      inferInstanceAs (upperStar A h ⋙ openImmersionLowerShriek A j').Faithful
    have : (J ⋙ L).Full := Functor.Full.of_iso (asIso b)
    have : (J ⋙ L).Faithful := Functor.Faithful.of_iso (asIso b)
    have hu : IsIso ((adjJ.comp adj).unit.app G) := inferInstance
    change IsIso (adjJ.unit.app G ≫ (upperStar A j).map (adj.unit.app E)) at hu
    have hu' : IsIso ((upperStar A j).map (adj.unit.app E)) := by
      exact (isIso_comp_left_iff (adjJ.unit.app G) _).mp hu
    let a := adj.homEquiv E F ((inv b).app G)
    have ha : IsIso ((upperStar A j).map a) := by
      change IsIso ((upperStar A j).map (adj.unit.app E ≫ R.map ((inv b).app G)))
      rw [Functor.map_comp]
      infer_instance
    have hc : IsIso (adjJ.counit.app (R.obj F)) :=
      adjJ.isIso_counit_app_of_iso e₀
    have hnat := adjJ.counit.naturality a
    dsimp only [Functor.id_map, Functor.comp_map] at hnat
    have hi : IsIso (adjJ.counit.app E ≫ a) := by
      rw [← hnat]
      infer_instance
    exact (isIso_comp_left_iff (adjJ.counit.app E) a).mp hi
  · intro q hq
    let e' :
        (R.rightDerivedFunctorPlus.obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F)).obj ≅
        (_root_.DerivedCategory.singleFunctor _ 0).obj E :=
      R.rightDerivedFunctorPlusCompatibility.app _ ≪≫
        R.rightDerivedFunctor.mapIso
          ((_root_.DerivedCategory.Plus.singleFunctorιIso _ 0).app F) ≪≫ e
    exact IsZero.of_iso
      (((_root_.DerivedCategory.singleFunctor _ 0).obj E).isZero_of_isLE 0 q hq)
      ((_root_.DerivedCategory.homologyFunctor _ q).mapIso e')

end AlgebraicGeometry.Etale
