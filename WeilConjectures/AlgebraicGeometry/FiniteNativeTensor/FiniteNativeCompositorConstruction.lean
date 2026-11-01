/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteNativeTensor.FiniteNativeTensorComparisonData

/-! # Construction of finite native compositors

Source: the finite native tensor comparison argument.
(blueprint: lem-pur-finite-native-compositor-construction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
universe u u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.FiniteNativeTensor
open FiniteDiscreteOrdinary
-- Discard the imported instance with a free coefficient universe.
attribute [-instance] WeilConjectures.scalarReductionSiteSmall
attribute [local instance 20000] sheafBraidedCategory sheafSymmetricCategory
  sheafMonoidalCategory sheafMonoidalClosed
  preservesColimitsOfSize_tensorLeft_sheaf preservesColimitsOfSize_tensorRight_sheaf
attribute [local instance 2000] Mod.monoidalCategory Mod.monoidalClosed
attribute [local irreducible] Mod.monoidalClosed
attribute [local irreducible] Sheaf.monoidalCategory SheafOfModules.monoidalCategory

variable (A : Type u) [CommRing A] [Finite A]
  [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]

variable (ordinary : Bool) (E : ∀ T : Scheme.{u}, Encoding A T)
  {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  [QuasiCompact f] [QuasiCompact g]
  [DomainComparison A ordinary E X] [DomainComparison A ordinary E Y]
  [DomainComparison A ordinary E Z]
  (cf : Compactification f) (cg : Compactification g) (ch : Compactification (f ≫ g))
  (sf : ArrowComparison A ordinary E f cf)
  (sg : ArrowComparison A ordinary E g cg)
  (sh : ArrowComparison A ordinary E (f ≫ g) ch)

/-- Restrict the actual bounded-below etale compositor through its unbounded compatibility
isomorphisms. Source: finite native comparison, Step 8.
(blueprint: lem-pur-finite-native-compositor-construction). -/
def canonicalEtaleCompositor :
    sf.etaleRestriction.lower ⋙ sg.etaleRestriction.lower ≅ sh.etaleRestriction.lower := by
  let P := etaleDomain A X
  let Λ := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let L : P.FullSubcategory ⥤ DerivedCategory.Plus (Sheaf X.smallEtaleTopology Λ) :=
    ObjectProperty.lift _ P.ι (fun M ↦ (etalePlus A X M).property)
  let F := Etale.rightDerivedLowerShriekOfCompactificationPlus Λ cf
  let a := Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility Λ cf
  let b := Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility Λ cg
  let c := Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility Λ ch
  let e : (P.ι ⋙ etaleF A cf) ⋙ etaleF A cg ≅ P.ι ⋙ etaleF A ch :=
    (Functor.isoWhiskerRight (Functor.isoWhiskerLeft L a) (etaleF A cg)).symm ≪≫
      (Functor.isoWhiskerLeft (L ⋙ F) b).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft L (coherenceEtaleCompositor (ULift.{u + 1} A) cf cg ch))
        DerivedCategory.Plus.ι ≪≫ Functor.isoWhiskerLeft L c
  exact NatIso.ofComponents (fun M ↦ (etaleDomain A Z).isoMk (e.app M))
    (fun r ↦ by
      apply ObjectProperty.hom_ext
      exact e.hom.naturality r)

omit [DiscreteTopology A] in
/-- The restriction keeps the prescribed component, including all four boundary factors.
Source: the definition of the bounded/unbounded comparison paste.
(blueprint: lem-pur-finite-native-compositor-construction). -/
theorem canonicalEtaleCompositor_normalization (M : (etaleDomain A X).FullSubcategory) :
    (etaleDomain A Z).ι.mapIso
        ((canonicalEtaleCompositor A ordinary E cf cg ch sf sg sh).app M) =
      etaleCompositorAt A cf cg ch M := by
  rfl

/-- The fully specified B-conjugation paste before descent along the domain equivalence.
Source: finite native comparison, Step 8.
(blueprint: lem-pur-finite-native-compositor-construction). -/
def canonicalCompositorPaste :
    V A ordinary E X ⋙ (sf.nativeRestriction.lower ⋙ sg.nativeRestriction.lower) ≅
      V A ordinary E X ⋙ sh.nativeRestriction.lower :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight sf.B.symm sg.nativeRestriction.lower ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft sf.etaleRestriction.lower sg.B.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (canonicalEtaleCompositor A ordinary E cf cg ch sf sg sh) (V A ordinary E Z) ≪≫ sh.B

/-- Descend the etale compositor through the domain equivalence and normalized B squares.
This fixes the native natural isomorphism without selecting a compactification triangle.
Source: finite native comparison, Step 8; full faithfulness of precomposition by an
 equivalence. (blueprint: lem-pur-finite-native-compositor-construction). -/
def canonicalNativeCompositor :
    sf.nativeRestriction.lower ⋙ sg.nativeRestriction.lower ≅ sh.nativeRestriction.lower :=
  ((Functor.whiskeringLeft _ _ ((nativeDomain A ordinary Z).FullSubcategory)).obj
    (V A ordinary E X)).preimageIso
    (canonicalCompositorPaste A ordinary E cf cg ch sf sg sh)

omit [DiscreteTopology A] in
/-- The descended compositor satisfies the comparison square by its preimage equation.
Source: the normalized B conjugation defining the compositor.
(blueprint: lem-pur-finite-native-compositor-construction). -/
theorem canonicalNativeCompositor_square (M : (etaleDomain A X).FullSubcategory) :
    (V A ordinary E Z).map
        ((canonicalEtaleCompositor A ordinary E cf cg ch sf sg sh).hom.app M) ≫
      sh.B.hom.app M =
    sg.B.hom.app (sf.etaleRestriction.lower.obj M) ≫
      sg.nativeRestriction.lower.map (sf.B.hom.app M) ≫
      (canonicalNativeCompositor A ordinary E cf cg ch sf sg sh).hom.app
        ((V A ordinary E X).obj M) := by
  let W := (Functor.whiskeringLeft _ _ ((nativeDomain A ordinary Z).FullSubcategory)).obj
    (V A ordinary E X)
  have hn : (canonicalNativeCompositor A ordinary E cf cg ch sf sg sh).hom.app
      ((V A ordinary E X).obj M) =
      (canonicalCompositorPaste A ordinary E cf cg ch sf sg sh).hom.app M := by
    exact NatTrans.congr_app
      (W.map_preimage (canonicalCompositorPaste A ordinary E cf cg ch sf sg sh).hom) M
  rw [hn]
  simp [canonicalCompositorPaste]

omit [DiscreteTopology A] in
/-- The descended compositor square in the original ambient categories, with the
three B comparisons replaced by their prescribed geometric components.
Source: finite native comparison, Step 8; the B normalization equations.
(blueprint: lem-pur-finite-native-compositor-construction). -/
theorem canonicalNativeCompositor_ambientSquare (M : (etaleDomain A X).FullSubcategory) :
    (realization A ordinary E Z).map (etaleCompositorAt A cf cg ch M).hom ≫
        (nativeB A ordinary E ch (etalePlus A X M)).hom =
      (nativeB A ordinary E cg
        (etalePlus A Y (sf.etaleRestriction.lower.obj M))).hom ≫
        (nativeCompact A ordinary cg).map
          (nativeB A ordinary E cf (etalePlus A X M)).hom ≫
        (nativeDomain A ordinary Z).ι.map
          ((canonicalNativeCompositor A ordinary E cf cg ch sf sg sh).hom.app
            ((V A ordinary E X).obj M)) := by
  have h := congrArg ((nativeDomain A ordinary Z).ι.map)
    (canonicalNativeCompositor_square A ordinary E cf cg ch sf sg sh M)
  simp only [Functor.map_comp] at h
  change (realization A ordinary E Z).map
      ((etaleDomain A Z).ι.map
        ((canonicalEtaleCompositor A ordinary E cf cg ch sf sg sh).hom.app M)) ≫
      (nativeDomain A ordinary Z).ι.map (sh.B.hom.app M) =
    (nativeDomain A ordinary Z).ι.map (sg.B.hom.app (sf.etaleRestriction.lower.obj M)) ≫
      (nativeCompact A ordinary cg).map
        ((nativeDomain A ordinary Y).ι.map (sf.B.hom.app M)) ≫
      (nativeDomain A ordinary Z).ι.map
        ((canonicalNativeCompositor A ordinary E cf cg ch sf sg sh).hom.app
          ((V A ordinary E X).obj M)) at h
  have he := congrArg Iso.hom
    (canonicalEtaleCompositor_normalization A ordinary E cf cg ch sf sg sh M)
  have hf := congrArg Iso.hom (sf.B_normalization M)
  have hg := congrArg Iso.hom (sg.B_normalization (sf.etaleRestriction.lower.obj M))
  have hh := congrArg Iso.hom (sh.B_normalization M)
  simp only [Functor.mapIso_hom, Iso.app_hom] at he hf hg hh
  erw [he, hf, hg, hh] at h
  exact h

end AlgebraicGeometry.ProEtale.FiniteNativeTensor
