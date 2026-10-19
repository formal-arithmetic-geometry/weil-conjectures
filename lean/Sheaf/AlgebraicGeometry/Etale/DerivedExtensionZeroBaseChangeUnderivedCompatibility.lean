/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap
public import Sheaf.AlgebraicGeometry.OpenImmersionSquare
public import Sheaf.AlgebraicGeometry.Etale.OpenExtensionZeroEtaleAdjunctionAgreement
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare

/-!
# Underived canonical open base-change compatibility

Source: Stacks Project, Etale Cohomology, Tags 03S6 and 0F70
(blueprint: lem-cbc-derived-extension-zero-base-change-underived-compatibility).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option autoImplicit false

/-- The canonical module mate for a chosen commutative square. It is defined by the
same inverse-conjugate formula as `etaleLowerShriekBaseChangeMap`, using the given square
rather than replacing its top-left scheme by the standard fiber product.
Source: Stacks Project, Etale Cohomology, Tag 03S6, comparison of the right adjoints;
`def-weil-pbc-etale-shriek-base-change-map`, the explicit inverse-conjugate formula
(blueprint: lem-cbc-derived-extension-zero-base-change-underived-compatibility). -/
noncomputable def chosenSquareEtaleLowerShriekBaseChangeMate
    (Λ : Type (u + 1)) [CommRing Λ] {U' U X' X : Scheme.{u}}
    {gU : U' ⟶ U} {j' : U' ⟶ X'} {j : U ⟶ X} {g : X' ⟶ X}
    [Etale j] [Etale j'] (sq : CommSq gU j' j g) :
    upperStar (ModuleCat.{u + 1} Λ) gU ⋙
        etaleLowerShriek (ModuleCat.{u + 1} Λ) j' inferInstance ⟶
      etaleLowerShriek (ModuleCat.{u + 1} Λ) j inferInstance ⋙
        upperStar (ModuleCat.{u + 1} Λ) g :=
  (conjugateEquiv
    ((etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j inferInstance).comp
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g))
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) gU).comp
      (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j' inferInstance))).symm
    (baseChangeMap (ModuleCat.{u + 1} Λ) sq.flip)

/-- On the standard fiber-product square, the chosen-square mate is the recorded module
base-change map, rather than a separately chosen comparison.
Source: Stacks Project, Etale Cohomology, Tag 03S6, and the defining formula of
`def-weil-pbc-etale-shriek-base-change-map`
(blueprint: lem-cbc-derived-extension-zero-base-change-underived-compatibility).

Proof plan: unfold the two definitions. The flip of the specified square has exactly the
projections and commutativity proof used in `etaleLowerShriekBaseChangeMap`; proof
irrelevance identifies the square proofs. The composite adjunctions and their conjugate
bijections are identical, so the natural transformations are equal. -/
theorem chosenSquareEtaleLowerShriekBaseChangeMate_pullback
    (Λ : Type (u + 1)) [CommRing Λ] {Y V X : Scheme.{u}}
    (f : Y ⟶ X) (j : V ⟶ X) [Etale j] :
    chosenSquareEtaleLowerShriekBaseChangeMate Λ
        (IsPullback.of_hasPullback f j).toCommSq.flip =
      etaleLowerShriekBaseChangeMap Λ f j := by
  rfl

/-- The module base-change map on a chosen cartesian open square, transported from the
open-extension map by the canonical open/etale comparison κ.
Source: Stacks Project, Etale Cohomology, Tag 03S6 and Modules on Sites, Tag 03DI
(blueprint: lem-cbc-derived-extension-zero-base-change-underived-compatibility). -/
noncomputable def chosenSquareEtaleLowerShriekBaseChangeMap
    (Λ : Type (u + 1)) [CommRing Λ] {U' U X' X : Scheme.{u}}
    {gU : U' ⟶ U} {j' : U' ⟶ X'} {j : U ⟶ X} {g : X' ⟶ X}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : CommSq gU j' j g) :
    upperStar (ModuleCat.{u + 1} Λ) gU ⋙
        etaleLowerShriek (ModuleCat.{u + 1} Λ) j' inferInstance ⟶
      etaleLowerShriek (ModuleCat.{u + 1} Λ) j inferInstance ⋙
        upperStar (ModuleCat.{u + 1} Λ) g :=
  letI := (openImmersionToEtaleLowerShriek_adjunction_agreement Λ j').1
  letI := (openImmersionToEtaleLowerShriek_adjunction_agreement Λ j).1
  Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} Λ) gU)
      (asIso (openImmersionToEtaleLowerShriek Λ j')).inv ≫
    openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ) sq ≫
    Functor.whiskerRight (asIso (openImmersionToEtaleLowerShriek Λ j)).hom
      (upperStar (ModuleCat.{u + 1} Λ) g)

/-- The κ-transported open comparison is the canonical module mate on this square.
This supplies the comparison with the dependency's module base-change construction.
Source: Stacks Project, Etale Cohomology, Tag 03S6; Modules on Sites, Tag 03DI
(blueprint: lem-cbc-derived-extension-zero-base-change-underived-compatibility).

Proof plan: use `openImmersionToEtaleLowerShriek_adjunction_agreement` at both open
immersions. It identifies the units and counits of the open and étale adjunctions.
Expand `conjugateEquiv.symm` for the two composite adjunctions. Substitute those unit
and counit identities and use naturality of κ and of the module exchange. Cancel the
inverse κ at the source and obtain precisely the displayed κ-transport of the open
mate. This proves equality of natural transformations, without choosing a new mate.
For a cartesian square this is Step 2 of the node's proof; on the standard fiber product,
`chosenSquareEtaleLowerShriekBaseChangeMate_pullback` identifies it with the recorded β. -/
theorem chosenSquareEtaleLowerShriekBaseChangeMap_eq_mate
    (Λ : Type (u + 1)) [CommRing Λ] {U' U X' X : Scheme.{u}}
    {gU : U' ⟶ U} {j' : U' ⟶ X'} {j : U ⟶ X} {g : X' ⟶ X}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : CommSq gU j' j g) :
    chosenSquareEtaleLowerShriekBaseChangeMap Λ sq =
      chosenSquareEtaleLowerShriekBaseChangeMate Λ sq := by
  have hj : openImmersionToEtaleLowerShriek Λ j =
      𝟙 (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j) := by
    simp only [openImmersionToEtaleLowerShriek, Functor.whiskerRight_id']
    rfl
  have hj' : openImmersionToEtaleLowerShriek Λ j' =
      𝟙 (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j') := by
    simp only [openImmersionToEtaleLowerShriek, Functor.whiskerRight_id']
    rfl
  simp only [chosenSquareEtaleLowerShriekBaseChangeMap, hj, hj', asIso_inv, asIso_hom]
  apply NatTrans.ext
  funext F
  simp only [Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    NatTrans.id_app, IsIso.inv_id]
  change 𝟙 _ ≫ (openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app F ≫
      (upperStar (ModuleCat.{u + 1} Λ) g).map (𝟙 _) =
    (openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app F
  simp

/-- The chosen-square transport of the module base-change map is invertible for a
cartesian open square.  Its proof is the composition of the κ isomorphisms with
open-immersion base change.
Source: Stacks Project, Etale Cohomology, Tag 03S6
(blueprint: lem-cbc-derived-extension-zero-base-change-underived-compatibility). -/
theorem isIso_chosenSquareEtaleLowerShriekBaseChangeMap
    (Λ : Type (u + 1)) [CommRing Λ] {U' U X' X : Scheme.{u}}
    {gU : U' ⟶ U} {j' : U' ⟶ X'} {j : U ⟶ X} {g : X' ⟶ X}
    [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback gU j' j g) :
    IsIso (chosenSquareEtaleLowerShriekBaseChangeMap Λ sq.toCommSq) := by
  have := (openImmersionToEtaleLowerShriek_adjunction_agreement Λ j').1
  have := (openImmersionToEtaleLowerShriek_adjunction_agreement Λ j).1
  have := isIso_openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ) sq
  unfold chosenSquareEtaleLowerShriekBaseChangeMap
  infer_instance


/-- For a cartesian open-immersion square, the canonical extension-by-zero comparison
and the module base-change map are inverse, with the stated adjunction-transpose and
restriction formulas.  The module map is represented by the open-extension map after
transport along `openImmersionToEtaleLowerShriek`, whose adjunction agreement is recorded
in `openImmersionToEtaleLowerShriek_adjunction_agreement`.

Proof plan from Stacks Project, Etale Cohomology, Tags 03S6 and 0F70.  (1) Put
`A = j_! F` and `N = g^{-1} A`; the inverse-image comparison for the square is module
linear by `etaleInverseImageCompositionModuleLinear`, and the module exchange is the
linear exchange of the square.  Its adjunction transpose is the counit formula obtained
from the two inverse-image adjunctions.  (2) Expand the module base-change map through its
composite adjunction.  Transporting through the comparison between open and étale
extensions gives the transpose of the pulled-back extension unit.  (3) Naturality of the
square comparison along the unit of `g^{-1} ⊣ g_*`, followed by its triangle identity,
reduces this transpose to `s_g ≫ g_U^{-1}(η_j)`.  (4) The canonical open base-change map
has the same transpose, so adjunction injectivity identifies it with the module map; the
comparison isomorphism then gives the inverse equality.  (5) Apply the unit-isomorphism for
an open immersion and cancel the two unit isomorphisms.  This gives the displayed identity
on the restriction, including the identity-square, empty-open, zero-sheaf, and zero-ring
cases.  Dependencies used are `lem-cbc-extension-zero-base-change`,
`def-weil-pbc-etale-shriek-base-change-map`,
`lem-cbc-open-extension-zero-etale-adjunction-agreement`,
`lem-weil-pbc-extension-by-zero-adjunction`,
`lem-weil-pbc-extension-by-zero-unit-iso`, and the module inverse-image comparison and
exchange declarations.
Source: Stacks Project, Etale Cohomology, Tags 03S6 and 0F70
(blueprint: lem-cbc-derived-extension-zero-base-change-underived-compatibility). -/
theorem derivedExtensionZeroBaseChangeUnderivedCompatibility
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    ∀ {U' U X' X : Scheme.{u}}
      {gU : U' ⟶ U} {j' : U' ⟶ X'} {j : U ⟶ X} {g : X' ⟶ X}
      (sqdata : OpenImmersionSquare gU j' j g),
      letI : IsOpenImmersion j := sqdata.isOpenImmersion
      letI : IsOpenImmersion j' := sqdata.isOpenImmersion'
      let sq : IsPullback gU j' j g :=
        IsPullback.of_iso_pullback
          sqdata.toChosenCartesianSquare.toCommSq
          sqdata.toChosenCartesianSquare.isoPullback
          sqdata.toChosenCartesianSquare.hom_fst
          sqdata.toChosenCartesianSquare.hom_snd
      letI : IsIso (chosenSquareEtaleLowerShriekBaseChangeMap Λ sq.toCommSq) :=
        isIso_chosenSquareEtaleLowerShriekBaseChangeMap Λ sq
      ∀ (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        (@asIso _ _ _ _ _
            (isIso_openImmersionLowerShriekBaseChangeMap
              (ModuleCat.{u + 1} Λ) sq)).inv.app F =
          ((@asIso _ _ _ _ _
            (isIso_chosenSquareEtaleLowerShriekBaseChangeMap Λ sq)).app F).inv ∧
        (openImmersionLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} Λ) j').unit.app
            ((upperStar (ModuleCat.{u + 1} Λ) gU).obj F) ≫
          (upperStar (ModuleCat.{u + 1} Λ) j').map
            ((openImmersionLowerShriekBaseChangeMap
              (ModuleCat.{u + 1} Λ) sq.toCommSq).app F) =
          (upperStar (ModuleCat.{u + 1} Λ) gU).map
            ((openImmersionLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} Λ) j).unit.app F) ≫
          (squareUpperStarIso (ModuleCat.{u + 1} Λ)
            sq.toCommSq.flip).hom.app
            ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).obj F) ∧
        (upperStar (ModuleCat.{u + 1} Λ) gU).map
            ((openImmersionLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} Λ) j).unit.app F) ≫
          (squareUpperStarIso (ModuleCat.{u + 1} Λ)
            sq.toCommSq.flip).hom.app
            ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).obj F) ≫
          (upperStar (ModuleCat.{u + 1} Λ) j').map
            ((@asIso _ _ _ _ _
              (isIso_openImmersionLowerShriekBaseChangeMap
                (ModuleCat.{u + 1} Λ) sq)).inv.app F) ≫
          (asIso (openImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} Λ) j').unit).inv.app
            ((upperStar (ModuleCat.{u + 1} Λ) gU).obj F) =
          𝟙 ((upperStar (ModuleCat.{u + 1} Λ) gU).obj F) := by
  intro U' U X' X gU j' j g sqdata
  let : IsOpenImmersion j := sqdata.isOpenImmersion
  let : IsOpenImmersion j' := sqdata.isOpenImmersion'
  let sq : IsPullback gU j' j g := IsPullback.of_iso_pullback
    sqdata.toCommSq sqdata.isoPullback sqdata.hom_fst sqdata.hom_snd
  have := isIso_openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ) sq
  have := isIso_chosenSquareEtaleLowerShriekBaseChangeMap Λ sq
  dsimp only
  intro F
  have hmap : chosenSquareEtaleLowerShriekBaseChangeMap Λ
      sqdata.toChosenCartesianSquare.toCommSq =
      openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ)
        sqdata.toChosenCartesianSquare.toCommSq := by
    exact (chosenSquareEtaleLowerShriekBaseChangeMap_eq_mate Λ _).trans rfl
  refine ⟨?_, unit_map_openImmersionLowerShriekBaseChangeMap_app _ _ _, ?_⟩
  · simp only [Iso.app_inv, asIso_inv, NatIso.isIso_inv_app]
    exact IsIso.inv_eq_inv.mpr (congrArg (fun α ↦ α.app F) hmap).symm
  · have ht := unit_map_openImmersionLowerShriekBaseChangeMap_app
      (ModuleCat.{u + 1} Λ) sqdata.toCommSq F
    rw [← Category.assoc, ← Category.assoc, ← ht]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc]
    have hc := Iso.hom_inv_id_app
      (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap
        (ModuleCat.{u + 1} Λ) sq)) F
    dsimp only [asIso_hom, Functor.comp_obj] at hc
    rw [hc]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    exact Iso.hom_inv_id_app
      (asIso (openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} Λ) j').unit)
      ((upperStar (ModuleCat.{u + 1} Λ) gU).obj F)

end AlgebraicGeometry.Etale
