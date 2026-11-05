/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteOpenBaseChangeNormalized
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Functor.OfSequence
import all WeilConjectures.AlgebraicGeometry.StrictTower.FiniteConstantCoefficientTransport
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryRestrictionPullbackSquare

/-!
# Finite open exchange and coefficient restriction

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/
lem-cbc-completed-extension-zero-comparison.proof.md, finite exchange before derived limits;
Stacks Project, Tag 03DI, direct-sum adjunction construction
(blueprint: lem-cbc-finite-open-exchange-scalars).

We use the recorded constant-ring module coordinates and the recorded inverse open-unit
transpose. All complex functors below are termwise, before derived localization.
-/

@[expose] public noncomputable section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.StrictTower.FiniteOpenScalars

attribute [local irreducible] Functor.leftAdjoint

variable {B C : Type (u + 1)} [CommRing B] [CommRing C]

/-- The map of constant coefficient sheaves induced by a ring homomorphism.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
abbrev coefficientMap (a : B →+* C) (X : Scheme.{u}) :
    coefficients B X ⟶ coefficients C X :=
  (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map (CommRingCat.ofHom a)

/-- The underlying ring sheaf of the recorded commutative constant coefficients.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
abbrev ringCoefficients (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :=
  (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients A X)

/-- The same coefficient homomorphism after forgetting commutativity.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
abbrev ringCoefficientMap (a : B →+* C) (X : Scheme.{u}) :
    ringCoefficients B X ⟶ ringCoefficients C X :=
  (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (coefficientMap a X)

/-- The recorded restriction of scalars, leaving the abelian sheaf unchanged.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
abbrev res (a : B →+* C) (X : Scheme.{u}) : Modules C X ⥤ Modules B X :=
  Scheme.proEtaleRingRestrictScalars (coefficientMap a X)

set_option backward.isDefEq.respectTransparency false in
private theorem scalarUnit_naturality (a : B →+* C) (X : Scheme.{u})
    (V : X.ProEtᵒᵖ) (b : B) :
    ((ringCoefficientMap a X).hom.app V) ((scalarUnit B X).app V b) =
      (scalarUnit C X).app V (a b) := by
  have h := congr_app ((toSheafification (Scheme.ProEt.topology X)
    CommRingCat.{u + 1}).naturality
      ((Functor.const X.ProEtᵒᵖ).map (CommRingCat.ofHom a))) V
  exact (ConcreteCategory.congr_hom h b).symm

set_option backward.isDefEq.respectTransparency false in
-- Change of constant-ring coordinates, with identity underlying section maps.
private def resFixed (a : B →+* C) (X : Scheme.{u}) :
    res a X ⋙ fixedRestriction B X ≅
      fixedRestriction C X ⋙ Sheaf.restrictScalars (Scheme.ProEt.topology X) a :=
  ringUnitLinearizeIso B (Scheme.ProEt.topology X) _ (scalarUnit B X)
    C a (res a X) (fixedRestriction C X) (Iso.refl _) (by
      intro M V b m
      change ((ringCoefficientMap a X).hom.app V) ((scalarUnit B X).app V b) •
          (show M.val.obj V from m) =
        (scalarUnit C X).app V (a b) • (show M.val.obj V from m)
      rw [scalarUnit_naturality])

/-- The constant-preserving coefficient maps commute with a coefficient homomorphism.
Source: Stacks Tags 03D2 and 03CY
(blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: transpose under the ring-sheaf adjunction. Both maps send each constant b to
the constant section a(b). The constant-presheaf sheafification property gives equality. -/
theorem coefficientSquare (a : B →+* C) {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (constantRingIso B f).hom ≫ coefficientMap a Y =
      (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (coefficientMap a X) ≫
        (constantRingIso C f).hom := by
  exact (Scheme.proEtaleConstantInverseImageMap_naturality f (CommRingCat.ofHom a)).symm

/-- Canonical pullback/scalar identification, the mate of identity on direct-image sections.
Source: Stacks Tags 03D2 and 03CY
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
def pullRes (a : B →+* C) {Y X : Scheme.{u}} (f : Y ⟶ X) :
    res a X ⋙ modulePullback B f ≅ modulePullback C f ⋙ res a Y :=
  @asIso _ _ _ _ (Scheme.proEtaleRingRestrictionPullbackInv f
    (coefficients B X) (coefficients C X) (coefficients B Y) (coefficients C Y)
    (coefficientMap a X) (coefficientMap a Y) (constantRingIso B f) (constantRingIso C f)
    (coefficientSquare a f))
    (Scheme.proEtaleRingRestrictionPullbackInv_isIso f
      (coefficients B X) (coefficients C X) (coefficients B Y) (coefficients C Y)
      (coefficientMap a X) (coefficientMap a Y) (constantRingIso B f) (constantRingIso C f)
      (coefficientSquare a f))

/-- Canonical direct-image/scalar identification, identity on every section.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
def pushRes (a : B →+* C) {Y X : Scheme.{u}} (f : Y ⟶ X) :
    moduleDirectImage C f ⋙ res a X ≅ res a Y ⋙ moduleDirectImage B f :=
  Scheme.proEtaleRingRestrictionDirectImage f
    (coefficients B X) (coefficients C X) (coefficients B Y) (coefficients C Y)
    (coefficientMap a X) (coefficientMap a Y) (constantRingIso B f) (constantRingIso C f)
    (coefficientSquare a f)

set_option backward.isDefEq.respectTransparency false in
private theorem pullRes_mate (a : B →+* C) {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (mateEquiv (Scheme.proEtaleRingModuleAdjunction f
        (coefficients C X) (coefficients C Y) (constantRingIso C f))
      (Scheme.proEtaleRingModuleAdjunction f
        (coefficients B X) (coefficients B Y) (constantRingIso B f))
      (TwoSquare.mk _ _ _ _ (pullRes a f).hom)).natTrans = (pushRes a f).hom := by
  change (mateEquiv (Scheme.proEtaleRingModuleAdjunction f
      (coefficients C X) (coefficients C Y) (constantRingIso C f))
    (Scheme.proEtaleRingModuleAdjunction f
      (coefficients B X) (coefficients B Y) (constantRingIso B f)))
      (TwoSquare.mk _ _ _ _ (pullRes a f).hom) =
    TwoSquare.mk _ _ _ _ (pushRes a f).hom
  rw [← Equiv.eq_symm_apply]
  apply TwoSquare.ext
  intro M
  simp only [mateEquiv_symm_apply, pullRes, asIso_hom,
    Scheme.proEtaleRingRestrictionPullbackInv,
    Scheme.proEtaleRingRestrictionPullbackApp, pushRes, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.comp_map, Category.id_comp]
  simp only [TwoSquare.mk, CategoryTheory.Functor.map_id]
  dsimp only [TwoSquare.natTrans, Functor.comp_obj]
  simp only [Category.id_comp]
  exact congrArg (fun k ↦ _ ≫ _ ≫ k) (Category.comp_id _).symm

section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] fixedRestriction_equivalence

private def fixedPull {A : Type (u + 1)} [CommRing A]
    {Y X : Scheme.{u}} (f : Y ⟶ X) :
    TwoSquare (fixedRestriction A X) (modulePullback A f)
      (upperStar (ModuleCat.{u + 1} A) f) (fixedRestriction A Y) :=
  (mateEquiv (Scheme.proEtaleRingModuleAdjunction f
    (coefficients A X) (coefficients A Y) (constantRingIso A f))
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)).symm
    (TwoSquare.mk _ _ _ _ (fixedDirect A f).hom)

private instance fixedPull_isIso {A : Type (u + 1)} [CommRing A]
    {Y X : Scheme.{u}} (f : Y ⟶ X) : IsIso (fixedPull (A := A) f).natTrans :=
  inverseMate_isIso_of_equivalences _ _ _

-- The pullback square can be checked on the identity-on-sections direct-image mates.
private theorem resPull_fixed (a : B →+* C) {Y X : Scheme.{u}} (f : Y ⟶ X) :
    TwoSquare.hComp (TwoSquare.mk _ _ _ _ (pullRes a f).hom)
        (fixedPull (A := B) f) =
      ((TwoSquare.hComp (fixedPull (A := C) f)
        (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso a f).hom)).whiskerTop
          (resFixed a X).hom).whiskerBottom (resFixed a Y).inv := by
  let adjC : modulePullback C f ⊣ moduleDirectImage C f :=
    Scheme.proEtaleRingModuleAdjunction f
    (coefficients C X) (coefficients C Y) (constantRingIso C f)
  let adjB : modulePullback B f ⊣ moduleDirectImage B f :=
    Scheme.proEtaleRingModuleAdjunction f
    (coefficients B X) (coefficients B Y) (constantRingIso B f)
  let ordC := upperStarLowerStarAdjunction (ModuleCat.{u + 1} C) f
  let ordB := upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f
  apply (mateEquiv adjC ordB).injective
  rw [mateEquiv_vcomp adjC adjB ordB, mateEquiv_whiskerTop_whiskerBottom adjC ordB,
    mateEquiv_vcomp adjC ordC ordB]
  have hp := pullRes_mate a f
  change (mateEquiv adjC adjB (TwoSquare.mk _ _ _ _ (pullRes a f).hom)).natTrans =
    (pushRes a f).hom at hp
  have hp' : mateEquiv adjC adjB (TwoSquare.mk _ _ _ _ (pullRes a f).hom) =
      TwoSquare.mk _ _ _ _ (pushRes a f).hom := by
    exact (TwoSquare.equivNatTrans _ _ _ _).injective hp
  rw [hp', show mateEquiv adjB ordB (fixedPull (A := B) f) =
      TwoSquare.mk _ _ _ _ (fixedDirect B f).hom from Equiv.apply_symm_apply _ _,
    show mateEquiv adjC ordC (fixedPull (A := C) f) =
      TwoSquare.mk _ _ _ _ (fixedDirect C f).hom from Equiv.apply_symm_apply _ _]
  have hs := scalar_direct_mate a f
  change (mateEquiv ordC ordB
    (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso a f).hom)).natTrans = 𝟙 _ at hs
  rw [show mateEquiv ordC ordB
      (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso a f).hom) =
      TwoSquare.mk _ _ _ _ (𝟙 _) from (TwoSquare.equivNatTrans _ _ _ _).injective hs]
  apply (TwoSquare.equivNatTrans _ _ _ _).injective
  apply (cancel_mono (Functor.whiskerRight (resFixed a Y).hom
    (lowerStar (ModuleCat.{u + 1} B) f))).mp
  simp only [TwoSquare.equivNatTrans, Equiv.coe_fn_mk, TwoSquare.natTrans,
    TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.mk,
    Category.assoc, ← Functor.whiskerRight_comp, Iso.inv_hom_id,
    Functor.whiskerRight_id', Category.comp_id]
  ext M V m
  change ((pushRes a f).hom.app M).val.app V m = m
  exact (Classical.choose_spec (Scheme.proEtaleRingRestrictionDirectImage_existsUnique
    f (coefficients B X) (coefficients C X) (coefficients B Y) (coefficients C Y)
    (coefficientMap a X) (coefficientMap a Y) (constantRingIso B f) (constantRingIso C f)
    (coefficientSquare a f))).1 M V m

end

section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] Scheme.proEtaleRingModulePullback

-- Compare compositors on direct images, where their section formulas are explicit.

end

/-- The scalar comparison for extension is the mate of the inverse pullback comparison.
Source: Stacks Tag 03DI, direct-sum adjunction construction
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
def openResMap (a : B →+* C) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    res a U ⋙ moduleJ B j ⟶ moduleJ C j ⋙ res a X :=
  (mateEquiv (moduleJAdj C j) (moduleJAdj B j)).symm (pullRes a j).inv

section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The normalized open scalar mate is invertible, including for the empty open.
Source: Stacks Tag 03DI (blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: transport the pullback comparison through the equivalence between constant-ring
module sheaves and sheaves of modules over the coefficient ring. Its direct-image mate
is identity on sections, so it agrees with the ordinary scalar comparison. The ordinary
open mate is invertible. Inverse-mate pasting transports this fact back through the
coordinate equivalences and identifies the resulting mate with openResMap. -/
theorem openResMap_isIso [Finite B] [Finite C] (a : B →+* C)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] : IsIso (openResMap a j) := by
  -- Paste through fixed coefficient coordinates, then take open inverse mates.
  let α := TwoSquare.mk _ _ _ _ (pullRes a j).hom
  let β := fixedPull (A := B) j
  let γ := fixedPull (A := C) j
  let δ := TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso a j).hom
  have : IsIso α.natTrans := by dsimp only [α, TwoSquare.mk]; infer_instance
  have : IsIso β.natTrans := fixedPull_isIso j
  have : IsIso γ.natTrans := fixedPull_isIso j
  have : IsIso δ.natTrans := by dsimp only [δ, TwoSquare.mk]; infer_instance
  have : IsIso (TwoSquare.hComp γ δ).natTrans := by
    dsimp only [TwoSquare.hComp, TwoSquare.mk]
    infer_instance
  let oa := moduleJAdj C j
  let ob := moduleJAdj B j
  let oc := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j
  let od := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} C) j
  have := fixedRestriction_equivalence B U
  have := fixedRestriction_equivalence B X
  have := fixedRestriction_equivalence C U
  have := fixedRestriction_equivalence C X
  have : IsIso ((mateEquiv oa od).symm
      (TwoSquare.mk _ _ _ _ (CategoryTheory.inv γ.natTrans))).natTrans :=
    inverseMate_isIso_of_equivalences oa od _
  have : IsIso ((mateEquiv od oc).symm
      (TwoSquare.mk _ _ _ _ (CategoryTheory.inv δ.natTrans))).natTrans := by
    simp only [δ, TwoSquare.mk, TwoSquare.natTrans, IsIso.Iso.inv_hom]
    rw [← scalarPullbackModel_eq B j C a]
    exact scalarOpenModel_isIso B j C a
  have hw : IsIso ((mateEquiv oa oc).symm
      (TwoSquare.mk _ _ _ _
        (CategoryTheory.inv (TwoSquare.hComp γ δ).natTrans))).natTrans := by
    rw [inv_hComp, inverseMate_vComp oa od oc]
    dsimp only [TwoSquare.hComp, TwoSquare.mk]
    infer_instance
  let w := TwoSquare.mk _ _ _ _ (CategoryTheory.inv (TwoSquare.hComp γ δ).natTrans)
  let t := TwoSquare.hComp α β
  have : IsIso t.natTrans := by
    dsimp only [t, TwoSquare.hComp, TwoSquare.mk]
    infer_instance
  let z := Functor.isoWhiskerRight (resFixed a X) _ ≪≫
    asIso (TwoSquare.hComp γ δ).natTrans ≪≫
    Functor.isoWhiskerLeft (modulePullback C j) (resFixed a U).symm
  have ht : CategoryTheory.inv t.natTrans =
      ((w.whiskerRight (resFixed a U).hom).whiskerLeft (resFixed a X).inv).natTrans := by
    have hz : t.natTrans = z.hom := congrArg TwoSquare.natTrans (resPull_fixed a j)
    calc
      CategoryTheory.inv t.natTrans = CategoryTheory.inv z.hom :=
        IsIso.inv_eq_inv.mpr hz
      _ = _ := by
        simp only [IsIso.Iso.inv_hom, z, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
          Functor.isoWhiskerRight_inv, Iso.symm_inv, asIso_inv, w,
          TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.mk, Category.assoc]
  have hi : IsIso ((mateEquiv oa oc).symm
      (TwoSquare.mk _ _ _ _ (CategoryTheory.inv t.natTrans))).natTrans := by
    rw [ht]
    exact inverseMate_iso_edges oa oc (resFixed a U) (resFixed a X).symm w
  let x := (mateEquiv oa ob).symm (TwoSquare.mk _ _ _ _ (pullRes a j).inv)
  let y := (mateEquiv ob oc).symm
    (TwoSquare.mk _ _ _ _ (CategoryTheory.inv β.natTrans))
  have : IsIso y.natTrans := inverseMate_isIso_of_equivalences ob oc _
  have he : (mateEquiv oa oc).symm
      (TwoSquare.mk _ _ _ _ (CategoryTheory.inv t.natTrans)) = TwoSquare.hComp x y := by
    dsimp only [t]
    rw [inv_hComp]
    exact inverseMate_vComp oa ob oc _ _
  rw [he] at hi
  exact isIso_of_hComp x y

end

/-- The canonical scalar-restriction identification for open extension.
Source: Stacks Tag 03DI (blueprint: lem-cbc-finite-open-exchange-scalars). -/
def openRes [Finite B] [Finite C] (a : B →+* C)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    res a U ⋙ moduleJ B j ≅ moduleJ C j ⋙ res a X :=
  @asIso _ _ _ _ (openResMap a j) (openResMap_isIso a j)

/-- The recorded canonical open exchange on sheaves, before degreewise extension.
Its inverse is exactly singleBetaInv, the pulled-back open-unit transpose.
Source: Stacks Tag 09AE (blueprint: lem-cbc-finite-open-exchange-scalars). -/
def beta (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) (hsq : IsPullback gU j' j g) :
    moduleJ A j ⋙ modulePullback A g ≅ modulePullback A gU ⋙ moduleJ A j' :=
  (@asIso _ _ _ _ (singleBetaInv A gU j' j g h)
    (singleBetaInv_isIso A gU j' j g h hsq)).symm

/-- The scalar identification on the source of open exchange.
Source: Stacks Tags 03DI and 03CY
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
def sourceRes [Finite B] [Finite C] (a : B →+* C)
    {U X' X : Scheme.{u}} (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] :
    res a U ⋙ (moduleJ B j ⋙ modulePullback B g) ≅
      (moduleJ C j ⋙ modulePullback C g) ⋙ res a X' :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (openRes a j) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (pullRes a g) ≪≫
    (Functor.associator _ _ _).symm

/-- The scalar identification on the target of open exchange.
Source: Stacks Tags 03DI and 03CY
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
def targetRes [Finite B] [Finite C] (a : B →+* C)
    {U' U X' : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X') [IsOpenImmersion j'] :
    res a U ⋙ (modulePullback B gU ⋙ moduleJ B j') ≅
      (modulePullback C gU ⋙ moduleJ C j') ⋙ res a X' :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (pullRes a gU) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (openRes a j') ≪≫
    (Functor.associator _ _ _).symm

/-- Scalar restriction on unbounded complexes, with all terms and differentials retained.
Source: blueprint finite exchange paragraph
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
abbrev resC (a : B →+* C) (X : Scheme.{u}) :
    CochainComplex (Modules C X) ℤ ⥤ CochainComplex (Modules B X) ℤ :=
  (res a X).mapHomologicalComplex (.up ℤ)

/-- The complex-level exchange, from the recorded sheaf exchange term by term.
Source: Stacks Tag 09AE (blueprint: lem-cbc-finite-open-exchange-scalars). -/
def betaC (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) (hsq : IsPullback gU j' j g) :
    (moduleJ A j ⋙ modulePullback A g).mapHomologicalComplex (.up ℤ) ≅
      (modulePullback A gU ⋙ moduleJ A j').mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex (beta A gU j' j g h hsq) (.up ℤ)

/-- The source identification on complexes.
Source: blueprint finite exchange paragraph
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
def sourceResC [Finite B] [Finite C] (a : B →+* C)
    {U X' X : Scheme.{u}} (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] :
    (res a U ⋙ (moduleJ B j ⋙ modulePullback B g)).mapHomologicalComplex (.up ℤ) ≅
      ((moduleJ C j ⋙ modulePullback C g) ⋙ res a X').mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex (sourceRes a j g) (.up ℤ)

/-- The target identification on complexes.
Source: blueprint finite exchange paragraph
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
def targetResC [Finite B] [Finite C] (a : B →+* C)
    {U' U X' : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X') [IsOpenImmersion j'] :
    (res a U ⋙ (modulePullback B gU ⋙ moduleJ B j')).mapHomologicalComplex (.up ℤ) ≅
      ((modulePullback C gU ⋙ moduleJ C j') ⋙ res a X').mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex (targetRes a gU j') (.up ℤ)

/-- Compatible ambient coefficient actions give a unique identity-on-sections comparison.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: the equation on ring maps says the two restricted actions agree. Identity on
every section is therefore linear, natural, and its own inverse. Sectionwise faithfulness
makes the resulting natural isomorphism unique. -/
theorem ambientRes_existsUnique (a : B →+* C) (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1})
    (rB : R ⟶ ringCoefficients B X) (rC : R ⟶ ringCoefficients C X)
    (hr : rB ≫ ringCoefficientMap a X = rC) :
    ∃! e : res a X ⋙ SheafOfModules.restrictScalars.{u + 1} rB ≅
        SheafOfModules.restrictScalars.{u + 1} rC,
      ∀ (M : Modules C X) (W : X.ProEtᵒᵖ) (m : M.val.obj W),
        (e.hom.app M).val.app W m = m := by
  let e : res a X ⋙ SheafOfModules.restrictScalars.{u + 1} rB ≅
      SheafOfModules.restrictScalars.{u + 1} rC :=
    NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun W ↦
        (ModuleCat.restrictScalarsComp'App (rB.hom.app W).hom
          ((ringCoefficientMap a X).hom.app W).hom (rC.hom.app W).hom
          (congrArg (fun k ↦ (k.hom.app W).hom) hr.symm) (M.val.obj W)).symm) (by
        intro W W' f
        ext m
        rfl))) (by
      intro M N f
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro W
      ext m
      rfl)
  refine ⟨e, fun _ _ _ ↦ rfl, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext m
  exact he' M W m

/-- The fixed comparison for restriction to compatible ambient actions.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
def ambientRes (a : B →+* C) (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1})
    (rB : R ⟶ ringCoefficients B X) (rC : R ⟶ ringCoefficients C X)
    (hr : rB ≫ ringCoefficientMap a X = rC) :
    res a X ⋙ SheafOfModules.restrictScalars.{u + 1} rB ≅
      SheafOfModules.restrictScalars.{u + 1} rC :=
  Classical.choose (ambientRes_existsUnique a X R rB rC hr)

section

set_option backward.isDefEq.respectTransparency false

end

section

attribute [local irreducible] sourceResC targetResC betaC sourceRes targetRes openRes pullRes
  pushRes beta openResMap Scheme.proEtaleRingModulePullback

end

section

attribute [local irreducible] ambientRes sourceResC targetResC betaC sourceRes targetRes openRes
  pullRes Scheme.proEtaleRingModulePullback

end

end AlgebraicGeometry.ProEtale.StrictTower.FiniteOpenScalars
