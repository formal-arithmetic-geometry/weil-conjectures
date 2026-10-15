/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapHomContinuityData
public import Sheaf.AlgebraicGeometry.PerfectHomTransport
public import Sheaf.AlgebraicGeometry.PerfectOverlapStageEquivalence
public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionLocalization
public import Sheaf.AlgebraicGeometry.SingleComplexOpenRestrictionData
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
import Sheaf.AlgebraicGeometry.TwoOpenComparisonDiagram
import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionIsoDescent

/-! # Core object comparison data (without the final Hom pin).

Source: Stacks Project, Tags 09RE, 08DW and 0D5S.
(blueprint: lem-pc-perfect-overlap-object-realization-core-data).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w v h v' h'
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem cancel_iso_pasting {C : Type*} [Category C]
    {A B D E : C} (f : A ⟶ B) (s : D ≅ B)
    (g : D ⟶ E) (h : E ⟶ D) (gh : g ≫ h = 𝟙 D) :
    f = 𝟙 A ≫ f ≫ s.inv ≫ g ≫ 𝟙 E ≫ h ≫ s.hom := by
  simp only [Category.id_comp, Category.comp_id,
    ← Category.assoc, gh, Category.comp_id, Iso.inv_hom_id]

/-- The fixed pullback from a finite overlap stage to the colimit overlap. -/
noncomputable def perfectOverlapCoreTransition
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (Y : Scheme.{u}) (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (k : Set.Ici i) :
    schemeDerivedCategory (pullback s (Spec.map (R.map (homOfLE k.property)))) ⥤
      schemeDerivedCategory (pullback s (Spec.map (c.ι.app i))) :=
  derivedPullback (baseChangeMap s (overlapLimitArrow R c k))

/-- The fixed composition comparison for the overlap transition. -/
@[no_expose] noncomputable def perfectOverlapCoreBaseComparison
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (Y : Scheme.{u}) (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (k : Set.Ici i) :
    derivedPullback (pullback.fst s (Spec.map (c.ι.app i))) ≅
      derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE k.property)))) ⋙
        perfectOverlapCoreTransition R c i Y s k :=
  let hX : pullback.fst s (Spec.map (c.ι.app i)) =
      pullback.fst s (Over.mk (Spec.map (c.ι.app i))).hom := rfl
  let hY : pullback.fst s (Spec.map (R.map (homOfLE k.property))) =
      pullback.fst s (Over.mk (Spec.map (R.map (homOfLE k.property)))).hom := rfl
  let eX := eqToIso (congrArg (fun f ↦ derivedPullback f) hX)
  let eY := eqToIso (congrArg (fun f ↦ derivedPullback f) hY)
  (by
    simpa only [perfectOverlapCoreTransition] using
      (eX ≪≫ perfectHomComparison s (overlapLimitArrow R c k) ≪≫
        (Functor.isoWhiskerRight eY
          (derivedPullback (baseChangeMap s (overlapLimitArrow R c k)))).symm))

/-- Natural derived-pullback comparison for two cartesian identifications.
Source: Stacks Project, Tag 0D5S. The two sides are pullbacks along the same
scheme map after `h`. Compose the fixed pullback-composition isomorphism for
`e.inv` and `r`, transport across `h`, and invert the fixed comparison for
`m` and `d.inv`. Naturality follows from that of each factor. -/
noncomputable def perfectOverlapDerivedPullbackTransport
    {Y Z A B : Scheme.{u}}
    [∀ T : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (r : Y ⟶ Z) (e : Y ≅ A) (d : Z ≅ B) (m : A ⟶ B)
    (h : e.inv ≫ r = m ≫ d.inv) :
    derivedPullback r ⋙ derivedPullback e.inv ≅
      derivedPullback d.inv ⋙ derivedPullback m :=
  perfectHomComposition e.inv r ≪≫
    eqToIso (congrArg (fun f ↦ derivedPullback f) h) ≪≫
      (perfectHomComposition m d.inv).symm

attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian

/-- The derived equivalence between the localized module site and its open scheme. -/
@[no_expose] noncomputable def perfectOverlapOpenSiteDerivedEquiv
    (X : Scheme.{u}) (W : X.Opens)
    [∀ T : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((moduleRings X.toRingedSpace).over W))] :
    DerivedCategory (SheafOfModules.{u}
      ((moduleRings X.toRingedSpace).over W)) ≌ schemeDerivedCategory W.toScheme := by
  let e : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W) ≌
      SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) :=
    Scheme.Modules.overEquiv W
  letI : e.functor.IsEquivalence := e.isEquivalence_functor
  letI : e.inverse.IsEquivalence := e.isEquivalence_inverse
  letI : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  letI : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  exact e.mapDerivedCategory

/-- The natural comparison after returning from the open site to its scheme.
The site counit removes the inverse/direct equivalence pair. The resulting two
pullback compositions agree by the given geometric square. -/
noncomputable def perfectOverlapNaturalComparisonFromGeometry
    {X Z A B : Scheme.{u}} (W : X.Opens)
    [∀ T : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((moduleRings X.toRingedSpace).over W))]
    (r : W.toScheme ⟶ Z) (e : W.toScheme ≅ A) (d : Z ≅ B)
    (m : A ⟶ B) (h : e.inv ≫ r = m ≫ d.inv) :
    (derivedPullback r ⋙ (perfectOverlapOpenSiteDerivedEquiv X W).inverse) ⋙
      ((perfectOverlapOpenSiteDerivedEquiv X W).functor ⋙
        derivedPullback e.inv) ≅
      derivedPullback d.inv ⋙ derivedPullback m := by
  let site := perfectOverlapOpenSiteDerivedEquiv X W
  let cancel := site.counitIso
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (derivedPullback r) (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft (derivedPullback r)
      (Functor.isoWhiskerRight cancel (derivedPullback e.inv)) ≪≫
    Functor.isoWhiskerLeft (derivedPullback r) (Functor.leftUnitor _) ≪≫
    perfectOverlapDerivedPullbackTransport r e d m h

/-- The component equation for the cartesian overlap comparison.
The two maps into the later open subscheme agree after its open immersion: the
first projection follows from the restricted-map equations and the pullback
first projections, and the second from the base-change square and pullback
second projections. The later cartesian square then identifies the maps. -/
theorem perfectOverlapCartesianComponent
    {X Y K C T S : Scheme.{u}}
    (g : X ⟶ Y) (gk : X ⟶ K) (f : K ⟶ Y)
    (pX : X ⟶ C) (pK : K ⟶ T) (pY : Y ⟶ S)
    (a : C ⟶ T) (q : T ⟶ S)
    (hgf : gk ≫ f = g) (hgk : gk ≫ pK = pX ≫ a)
    (hf : IsPullback f pK pY q) (W : Y.Opens)
    (r : (g ⁻¹ᵁ W).toScheme ⟶ (f ⁻¹ᵁ W).toScheme)
    (hr : r ≫ (f ⁻¹ᵁ W).ι = (g ⁻¹ᵁ W).ι ≫ gk)
    (eY : (g ⁻¹ᵁ W).toScheme ≅ pullback (W.ι ≫ pY) (a ≫ q))
    (eK : (f ⁻¹ᵁ W).toScheme ≅ pullback (W.ι ≫ pY) q)
    (hYfst : eY.inv ≫ (g ∣_ W) = pullback.fst (W.ι ≫ pY) (a ≫ q))
    (hYsnd : eY.inv ≫ (g ⁻¹ᵁ W).ι ≫ pX =
      pullback.snd (W.ι ≫ pY) (a ≫ q))
    (hKfst : eK.inv ≫ (f ∣_ W) = pullback.fst (W.ι ≫ pY) q)
    (hKsnd : eK.inv ≫ (f ⁻¹ᵁ W).ι ≫ pK = pullback.snd (W.ι ≫ pY) q) :
    eY.inv ≫ r =
      baseChangeMap (W.ι ≫ pY)
        (Over.homMk a (by rfl) : Over.mk (a ≫ q) ⟶ Over.mk q) ≫ eK.inv := by
  let m := baseChangeMap (W.ι ≫ pY)
    (Over.homMk a (by rfl) : Over.mk (a ≫ q) ⟶ Over.mk q)
  have hrf : r ≫ (f ⁻¹ᵁ W).ι ≫ f = (g ⁻¹ᵁ W).ι ≫ g := by
    rw [← Category.assoc r (f ⁻¹ᵁ W).ι f, hr, Category.assoc, hgf]
  have hrpK : r ≫ (f ⁻¹ᵁ W).ι ≫ pK = (g ⁻¹ᵁ W).ι ≫ pX ≫ a := by
    rw [← Category.assoc r (f ⁻¹ᵁ W).ι pK, hr, Category.assoc, hgk]
  have hYtoY : eY.inv ≫ (g ⁻¹ᵁ W).ι ≫ g =
      pullback.fst (W.ι ≫ pY) (a ≫ q) ≫ W.ι := by
    calc
      eY.inv ≫ (g ⁻¹ᵁ W).ι ≫ g = eY.inv ≫ (g ∣_ W) ≫ W.ι := by
        simpa only [Category.assoc] using
          congrArg (fun z ↦ eY.inv ≫ z) (morphismRestrict_ι g W).symm
      _ = pullback.fst (W.ι ≫ pY) (a ≫ q) ≫ W.ι := by
        simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ W.ι) hYfst
  have hKtoY : eK.inv ≫ (f ⁻¹ᵁ W).ι ≫ f =
      pullback.fst (W.ι ≫ pY) q ≫ W.ι := by
    calc
      eK.inv ≫ (f ⁻¹ᵁ W).ι ≫ f = eK.inv ≫ (f ∣_ W) ≫ W.ι := by
        simpa only [Category.assoc] using
          congrArg (fun z ↦ eK.inv ≫ z) (morphismRestrict_ι f W).symm
      _ = pullback.fst (W.ι ≫ pY) q ≫ W.ι := by
        simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ W.ι) hKfst
  have hmfst : m ≫ pullback.fst (W.ι ≫ pY) q =
      pullback.fst (W.ι ≫ pY) (a ≫ q) := by
    exact baseChangeMap_fst _ _
  have hmsnd : m ≫ pullback.snd (W.ι ≫ pY) q =
      pullback.snd (W.ι ≫ pY) (a ≫ q) ≫ a := by
    exact baseChangeMap_snd _ _
  apply (cancel_mono (f ⁻¹ᵁ W).ι).1
  apply hf.hom_ext
  · calc
      eY.inv ≫ r ≫ (f ⁻¹ᵁ W).ι ≫ f =
        eY.inv ≫ (g ⁻¹ᵁ W).ι ≫ g := by
          simpa only [Category.assoc] using congrArg (fun z ↦ eY.inv ≫ z) hrf
      _ = pullback.fst (W.ι ≫ pY) (a ≫ q) ≫ W.ι := hYtoY
      _ = m ≫ pullback.fst (W.ι ≫ pY) q ≫ W.ι := by
        simpa only [Category.assoc] using
          congrArg (fun z ↦ z ≫ W.ι) hmfst.symm
      _ = m ≫ eK.inv ≫ (f ⁻¹ᵁ W).ι ≫ f := by
        simpa only [Category.assoc] using congrArg (fun z ↦ m ≫ z) hKtoY.symm
  · calc
      eY.inv ≫ r ≫ (f ⁻¹ᵁ W).ι ≫ pK =
        eY.inv ≫ (g ⁻¹ᵁ W).ι ≫ pX ≫ a := by
          simpa only [Category.assoc] using congrArg (fun z ↦ eY.inv ≫ z) hrpK
      _ = pullback.snd (W.ι ≫ pY) (a ≫ q) ≫ a := by
        simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ a) hYsnd
      _ = m ≫ pullback.snd (W.ι ≫ pY) q := by
        exact hmsnd.symm
      _ = m ≫ eK.inv ≫ (f ⁻¹ᵁ W).ι ≫ pK := by
        simpa only [Category.assoc] using congrArg (fun z ↦ m ≫ z) hKsnd.symm

/-- The component equation for the cartesian overlap comparison.
The two maps into the later open subscheme agree after its open immersion: the
first projection follows from the restricted-map equations and the pullback
first projections, and the second from the base-change square and pullback
second projections. The later cartesian square then identifies the maps. -/
theorem perfectOverlapCartesianComponentOver
    {X Y K C T S : Scheme.{u}}
    (g : X ⟶ Y) (gk : X ⟶ K) (f : K ⟶ Y)
    (pX : X ⟶ C) (pK : K ⟶ T) (pY : Y ⟶ S)
    (b : C ⟶ S) (q : T ⟶ S)
    (l : Over.mk b ⟶ Over.mk q)
    (hgf : gk ≫ f = g) (hgk : gk ≫ pK = pX ≫ l.left)
    (hf : IsPullback f pK pY q) (W : Y.Opens)
    (r : (g ⁻¹ᵁ W).toScheme ⟶ (f ⁻¹ᵁ W).toScheme)
    (hr : r ≫ (f ⁻¹ᵁ W).ι = (g ⁻¹ᵁ W).ι ≫ gk)
    (eY : (g ⁻¹ᵁ W).toScheme ≅ pullback (W.ι ≫ pY) b)
    (eK : (f ⁻¹ᵁ W).toScheme ≅ pullback (W.ι ≫ pY) q)
    (hYfst : eY.inv ≫ (g ∣_ W) = pullback.fst (W.ι ≫ pY) b)
    (hYsnd : eY.inv ≫ (g ⁻¹ᵁ W).ι ≫ pX =
      pullback.snd (W.ι ≫ pY) b)
    (hKfst : eK.inv ≫ (f ∣_ W) = pullback.fst (W.ι ≫ pY) q)
    (hKsnd : eK.inv ≫ (f ⁻¹ᵁ W).ι ≫ pK = pullback.snd (W.ι ≫ pY) q) :
    eY.inv ≫ r =
      baseChangeMap (W.ι ≫ pY)
        l ≫ eK.inv := by
  let m := baseChangeMap (W.ι ≫ pY)
    l
  have hrf : r ≫ (f ⁻¹ᵁ W).ι ≫ f = (g ⁻¹ᵁ W).ι ≫ g := by
    rw [← Category.assoc r (f ⁻¹ᵁ W).ι f, hr, Category.assoc, hgf]
  have hrpK : r ≫ (f ⁻¹ᵁ W).ι ≫ pK = (g ⁻¹ᵁ W).ι ≫ pX ≫ l.left := by
    rw [← Category.assoc r (f ⁻¹ᵁ W).ι pK, hr, Category.assoc, hgk]
  have hYtoY : eY.inv ≫ (g ⁻¹ᵁ W).ι ≫ g =
      pullback.fst (W.ι ≫ pY) b ≫ W.ι := by
    calc
      eY.inv ≫ (g ⁻¹ᵁ W).ι ≫ g = eY.inv ≫ (g ∣_ W) ≫ W.ι := by
        simpa only [Category.assoc] using
          congrArg (fun z ↦ eY.inv ≫ z) (morphismRestrict_ι g W).symm
      _ = pullback.fst (W.ι ≫ pY) b ≫ W.ι := by
        simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ W.ι) hYfst
  have hKtoY : eK.inv ≫ (f ⁻¹ᵁ W).ι ≫ f =
      pullback.fst (W.ι ≫ pY) q ≫ W.ι := by
    calc
      eK.inv ≫ (f ⁻¹ᵁ W).ι ≫ f = eK.inv ≫ (f ∣_ W) ≫ W.ι := by
        simpa only [Category.assoc] using
          congrArg (fun z ↦ eK.inv ≫ z) (morphismRestrict_ι f W).symm
      _ = pullback.fst (W.ι ≫ pY) q ≫ W.ι := by
        simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ W.ι) hKfst
  have hmfst : m ≫ pullback.fst (W.ι ≫ pY) q =
      pullback.fst (W.ι ≫ pY) b := by
    exact baseChangeMap_fst _ _
  have hmsnd : m ≫ pullback.snd (W.ι ≫ pY) q =
      pullback.snd (W.ι ≫ pY) b ≫ l.left := by
    exact baseChangeMap_snd _ _
  apply (cancel_mono (f ⁻¹ᵁ W).ι).1
  apply hf.hom_ext
  · calc
      eY.inv ≫ r ≫ (f ⁻¹ᵁ W).ι ≫ f =
        eY.inv ≫ (g ⁻¹ᵁ W).ι ≫ g := by
          simpa only [Category.assoc] using congrArg (fun z ↦ eY.inv ≫ z) hrf
      _ = pullback.fst (W.ι ≫ pY) b ≫ W.ι := hYtoY
      _ = m ≫ pullback.fst (W.ι ≫ pY) q ≫ W.ι := by
        simpa only [Category.assoc] using
          congrArg (fun z ↦ z ≫ W.ι) hmfst.symm
      _ = m ≫ eK.inv ≫ (f ⁻¹ᵁ W).ι ≫ f := by
        simpa only [Category.assoc] using congrArg (fun z ↦ m ≫ z) hKtoY.symm
  · calc
      eY.inv ≫ r ≫ (f ⁻¹ᵁ W).ι ≫ pK =
        eY.inv ≫ (g ⁻¹ᵁ W).ι ≫ pX ≫ l.left := by
          simpa only [Category.assoc] using congrArg (fun z ↦ eY.inv ≫ z) hrpK
      _ = pullback.snd (W.ι ≫ pY) b ≫ l.left := by
        simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ l.left) hYsnd
      _ = m ≫ pullback.snd (W.ι ≫ pY) q := by
        exact hmsnd.symm
      _ = m ≫ eK.inv ≫ (f ⁻¹ᵁ W).ι ≫ pK := by
        simpa only [Category.assoc] using congrArg (fun z ↦ m ≫ z) hKsnd.symm

/-- The two canonical overlap object comparisons packaged without expanding
the stagewise transport record. The branch equations are exactly the
comparison, transported local identification, and site restriction maps. -/
noncomputable def perfectOverlapPsiFromDiagram
    {C D A B W P Q T : Type*}
    [Category* C] [Category* D] [Category* A] [Category* B]
    [Category* W] [Category* P] [Category* Q] [Category* T]
    {L : C ⥤ D} {TU : C ⥤ A} {TV : C ⥤ B} {TW : C ⥤ W}
    {SU : A ⥤ W} {SV : B ⥤ W}
    {RU : D ⥤ P} {RV : D ⥤ Q} {RW : D ⥤ T}
    {SP : P ⥤ T} {SQ : Q ⥤ T}
    {αU : TU ⋙ SU ≅ TW} {αV : TV ⋙ SV ≅ TW}
    {τU : RU ⋙ SP ≅ RW} {τV : RV ⋙ SQ ≅ RW}
    (d : TwoOpenComparisonDiagram L TU TV TW SU SV RU RV RW SP SQ
      αU αV τU τV)
    (A' : A) (B' : B) (E : D)
    (θU : d.HU.obj A' ≅ RU.obj E)
    (θV : d.HV.obj B' ≅ RV.obj E)
    (b : Bool) :
    d.HW.obj (if b then SV.obj B' else SU.obj A') ≅ RW.obj E :=
  match b with
  | false => d.γU.symm.app A' ≪≫ SP.mapIso θU ≪≫ τU.app E
  | true => d.γV.symm.app B' ≪≫ SQ.mapIso θV ≪≫ τV.app E

/-- The first component of the canonical overlap object comparison.
Source: Stacks Project, Tags 08DW and 0D5S. On the first open, invert the
intersection comparison `γU`, map the transported local identification through
the smaller-open restriction, then use `τU` to identify the two site restrictions.
This is exactly the false branch of the defining comparison. -/
@[simp] theorem perfectOverlapPsiFromDiagram_false
    {C D A B W P Q T : Type*}
    [Category* C] [Category* D] [Category* A] [Category* B]
    [Category* W] [Category* P] [Category* Q] [Category* T]
    {L : C ⥤ D} {TU : C ⥤ A} {TV : C ⥤ B} {TW : C ⥤ W}
    {SU : A ⥤ W} {SV : B ⥤ W}
    {RU : D ⥤ P} {RV : D ⥤ Q} {RW : D ⥤ T}
    {SP : P ⥤ T} {SQ : Q ⥤ T}
    {αU : TU ⋙ SU ≅ TW} {αV : TV ⋙ SV ≅ TW}
    {τU : RU ⋙ SP ≅ RW} {τV : RV ⋙ SQ ≅ RW}
    (d : TwoOpenComparisonDiagram L TU TV TW SU SV RU RV RW SP SQ
      αU αV τU τV)
    (A' : A) (B' : B) (E : D)
    (θU : d.HU.obj A' ≅ RU.obj E)
    (θV : d.HV.obj B' ≅ RV.obj E) :
    perfectOverlapPsiFromDiagram d A' B' E θU θV false =
      d.γU.symm.app A' ≪≫ SP.mapIso θU ≪≫ τU.app E := by
  rfl

/-- The second component of the canonical overlap object comparison.
Source: Stacks Project, Tags 08DW and 0D5S. On the second open, invert the
intersection comparison `γV`, map the transported local identification through
the smaller-open restriction, then use `τV` to identify the two site restrictions.
This is exactly the true branch of the defining comparison. -/
@[simp] theorem perfectOverlapPsiFromDiagram_true
    {C D A B W P Q T : Type*}
    [Category* C] [Category* D] [Category* A] [Category* B]
    [Category* W] [Category* P] [Category* Q] [Category* T]
    {L : C ⥤ D} {TU : C ⥤ A} {TV : C ⥤ B} {TW : C ⥤ W}
    {SU : A ⥤ W} {SV : B ⥤ W}
    {RU : D ⥤ P} {RV : D ⥤ Q} {RW : D ⥤ T}
    {SP : P ⥤ T} {SQ : Q ⥤ T}
    {αU : TU ⋙ SU ≅ TW} {αV : TV ⋙ SV ≅ TW}
    {τU : RU ⋙ SP ≅ RW} {τV : RV ⋙ SQ ≅ RW}
    (d : TwoOpenComparisonDiagram L TU TV TW SU SV RU RV RW SP SQ
      αU αV τU τV)
    (A' : A) (B' : B) (E : D)
    (θU : d.HU.obj A' ≅ RU.obj E)
    (θV : d.HV.obj B' ≅ RV.obj E) :
    perfectOverlapPsiFromDiagram d A' B' E θU θV true =
      d.γV.symm.app B' ≪≫ SQ.mapIso θV ≪≫ τV.app E := by
  rfl

/-- Invert the first-open coherence square at a global object.
Source: Stacks Project, Tag 08DW. The defining square says that the path through
`τU⁻¹`, `βU`, and `γU` equals the path through `βW` and `αU⁻¹`.
Compose on the left with `αU` and `βW⁻¹`, then cancel `γU` on the right.
Functoriality and the inverse laws for the natural isomorphisms give the formula. -/
theorem overlapDiagram_gammaU_inv_on_image
    {C D A B W P Q T : Type*}
    [Category* C] [Category* D] [Category* A] [Category* B]
    [Category* W] [Category* P] [Category* Q] [Category* T]
    {L : C ⥤ D} {TU : C ⥤ A} {TV : C ⥤ B} {TW : C ⥤ W}
    {SU : A ⥤ W} {SV : B ⥤ W}
    {RU : D ⥤ P} {RV : D ⥤ Q} {RW : D ⥤ T}
    {SP : P ⥤ T} {SQ : Q ⥤ T}
    {αU : TU ⋙ SU ≅ TW} {αV : TV ⋙ SV ≅ TW}
    {τU : RU ⋙ SP ≅ RW} {τV : RV ⋙ SQ ≅ RW}
    (d : TwoOpenComparisonDiagram L TU TV TW SU SV RU RV RW SP SQ
      αU αV τU τV) (F : C) :
    d.γU.inv.app (TU.obj F) =
      d.HW.map (αU.hom.app F) ≫ d.βW.inv.app F ≫
        τU.inv.app (L.obj F) ≫ SP.map (d.βU.hom.app F) := by
  apply (cancel_mono (d.γU.hom.app (TU.obj F))).1
  calc
    d.γU.inv.app (TU.obj F) ≫ d.γU.hom.app (TU.obj F) = 𝟙 _ := by simp
    _ = d.HW.map (αU.hom.app F) ≫ d.βW.inv.app F ≫
          (d.βW.hom.app F ≫ d.HW.map (αU.inv.app F)) := by simp
    _ = (d.HW.map (αU.hom.app F) ≫ d.βW.inv.app F ≫
          τU.inv.app (L.obj F) ≫ SP.map (d.βU.hom.app F)) ≫
          d.γU.hom.app (TU.obj F) := by
      simp only [Category.assoc]
      rw [d.coherenceU F]

/-- Invert the second-open coherence square at a global object.
Source: Stacks Project, Tag 08DW. Compose the defining second-open square
with the inverses of `αV`, `βW`, and `γV`. The inverse laws cancel these
isomorphisms and leave the displayed expression for the inverse component. -/
theorem overlapDiagram_gammaV_inv_on_image
    {C D A B W P Q T : Type*}
    [Category* C] [Category* D] [Category* A] [Category* B]
    [Category* W] [Category* P] [Category* Q] [Category* T]
    {L : C ⥤ D} {TU : C ⥤ A} {TV : C ⥤ B} {TW : C ⥤ W}
    {SU : A ⥤ W} {SV : B ⥤ W}
    {RU : D ⥤ P} {RV : D ⥤ Q} {RW : D ⥤ T}
    {SP : P ⥤ T} {SQ : Q ⥤ T}
    {αU : TU ⋙ SU ≅ TW} {αV : TV ⋙ SV ≅ TW}
    {τU : RU ⋙ SP ≅ RW} {τV : RV ⋙ SQ ≅ RW}
    (d : TwoOpenComparisonDiagram L TU TV TW SU SV RU RV RW SP SQ
      αU αV τU τV) (F : C) :
    d.γV.inv.app (TV.obj F) =
      d.HW.map (αV.hom.app F) ≫ d.βW.inv.app F ≫
        τV.inv.app (L.obj F) ≫ SQ.map (d.βV.hom.app F) := by
  apply (cancel_mono (d.γV.hom.app (TV.obj F))).1
  calc
    d.γV.inv.app (TV.obj F) ≫ d.γV.hom.app (TV.obj F) = 𝟙 _ := by simp
    _ = d.HW.map (αV.hom.app F) ≫ d.βW.inv.app F ≫
          (d.βW.hom.app F ≫ d.HW.map (αV.inv.app F)) := by simp
    _ = (d.HW.map (αV.hom.app F) ≫ d.βW.inv.app F ≫
          τV.inv.app (L.obj F) ≫ SQ.map (d.βV.hom.app F)) ≫
          d.γV.hom.app (TV.obj F) := by
      simp only [Category.assoc]
      rw [d.coherenceV F]



/-- Geometric object comparisons and their natural compatibility with apex pullback.
The transition functors and their fixed conjugation formula are recorded explicitly;
the Hom pin will be derived from naturality, rather than included as a field.
Source: Stacks Project, Tags 08DW and 0D5S.
(blueprint: lem-pc-perfect-overlap-object-realization-core-data). -/
structure PerfectHomObjectRealizationCore
    {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (i : I)
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (C : Set.Ici i → Type v) [∀ k, Category.{h} (C k)]
    (F : ∀ k, Bool → C k) (D : Type v') [Category.{h'} D]
    (O : Bool → D) (G : ∀ k, C k ⥤ D)
    (ψ : ∀ k b, (G k).obj (F k b) ≅ O b)
    (Y : Scheme.{u}) (s : Y ⟶ Spec (R.obj i)) (objects : Bool → schemeDerivedCategory Y)
    (stageEquiv : ∀ k : Set.Ici i, C k ≌
      schemeDerivedCategory (pullback s (Spec.map (R.map (homOfLE k.property)))))
    (apexEquiv : D ≌ schemeDerivedCategory (pullback s (Spec.map (c.ι.app i))))
    where
  stageObj : ∀ k b, (stageEquiv k).functor.obj (F k b) ≅
    (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE k.property))))).obj
      (objects b)
  apexObj : ∀ b, apexEquiv.functor.obj (O b) ≅
    (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj (objects b)

  transition : ∀ k : Set.Ici i,
    schemeDerivedCategory (pullback s (Spec.map (R.map (homOfLE k.property)))) ⥤
      schemeDerivedCategory (pullback s (Spec.map (c.ι.app i)))
  baseComparison : ∀ k : Set.Ici i,
    derivedPullback (pullback.fst s (Spec.map (c.ι.app i))) ≅
      derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE k.property)))) ⋙ transition k
  transition_pin : ∀ (k : Set.Ici i) (P Q : schemeDerivedCategory Y)
    (f : (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE k.property))))).obj P ⟶
      (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE k.property))))).obj Q),
    perfectLimitMap R c s k.property f =
      (baseComparison k).hom.app P ≫ (transition k).map f ≫ (baseComparison k).inv.app Q
  comparison : ∀ k : Set.Ici i,
    G k ⋙ apexEquiv.functor ≅ (stageEquiv k).functor ⋙ transition k
  object_pin : ∀ (k : Set.Ici i) (b : Bool),
    apexEquiv.functor.map (ψ k b).hom ≫ (apexObj b).hom ≫
      (baseComparison k).hom.app (objects b) =
        (comparison k).hom.app (F k b) ≫ (transition k).map (stageObj k b).hom

attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
  schemeOpenRestriction_additive schemeOpenRestriction_preservesFiniteLimits
  schemeOpenRestriction_preservesFiniteColimits schemeOpenOverlapRestriction_additive
  schemeOpenOverlapRestriction_preservesFiniteLimits
  schemeOpenOverlapRestriction_preservesFiniteColimits

/-- The object-comparison proposition for the fixed overlap scheme and pullback objects.
Source: Stacks Project, Tags 09RE, 08DW and 0D5S.
(blueprint: lem-pc-perfect-overlap-object-realization-core-data). -/
@[irreducible] noncomputable def perfectOverlapObjectRealizationCoreStatement
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    (hstage : ∀ (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens),
      ∃ k : I, j ≤ k)
    : Prop :=
    let Yj := pullback t (Spec.map (R.map (homOfLE hij)))
    let X := pullback t (Spec.map (c.ι.app i))
    let gj := baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))
    ∀ (U V : Yj.Opens) (hcover : U ⊔ V = ⊤)
      (hU : IsCompact (U : Set Yj)) (hV : IsCompact (V : Set Yj))
      (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
      (hA : U.toScheme.IsPerfect A) (hB : V.toScheme.IsPerfect B)
      (E : schemeDerivedCategory X),
    let instP : Category (schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme) := inferInstance
    let instQ : Category (schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme) := inferInstance
    let instX : Category (schemeDerivedCategory X) := inferInstance
    let PU : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ U)).mapDerivedCategory
    let PV : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ V)).mapDerivedCategory
    ∀ (φU : (derivedPullback (gj ∣_ U)).obj A ≅
        PU.obj E)
      (φV : (derivedPullback (gj ∣_ V)).obj B ≅
        PV.obj E),
      let P := gj ⁻¹ᵁ U
      let Q := gj ⁻¹ᵁ V
      let RU := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) P).mapDerivedCategory
      let RV := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) Q).mapDerivedCategory
      let RW := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) (P ⊓ Q)).mapDerivedCategory
      let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ P from inf_le_left))).mapDerivedCategory
      let SQ := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ Q from inf_le_right))).mapDerivedCategory
      let τU : RU ⋙ SP ≅ RW := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ P from inf_le_left)))
      let τV : RV ⋙ SQ ≅ RW := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ Q from inf_le_right)))
    Nonempty (
      Σ data : (k : I) → (hjk : j ≤ k) →
        perfectOverlapComparisonDataType R c hc i Z t j hij hstage
          U V hcover hU hV A B hA hB E φU φV k hjk,
      let K := {k : I // j ≤ k}
      let C : K → Type (u + 1) := fun k ↦
        let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans k.property))))
        let f := baseChangeMap t
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))))
          (Over.homMk (Spec.map (R.map (homOfLE k.property)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let U' := f ⁻¹ᵁ U
        let V' := f ⁻¹ᵁ V
        schemeDerivedCategory (U' ⊓ V').toScheme
      let F : (k : K) → Bool → C k := fun k b ↦
        let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans k.property))))
        let f := baseChangeMap t
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))))
          (Over.homMk (Spec.map (R.map (homOfLE k.property)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let U' := f ⁻¹ᵁ U
        let V' := f ⁻¹ᵁ V
        let A' : schemeDerivedCategory U'.toScheme := (derivedPullback (f ∣_ U)).obj A
        let B' : schemeDerivedCategory V'.toScheme := (derivedPullback (f ∣_ V)).obj B
        let SU : schemeDerivedCategory U'.toScheme ⥤
            schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
          (homOfLE (show U' ⊓ V' ≤ U' from inf_le_left))).mapDerivedCategory
        let SV : schemeDerivedCategory V'.toScheme ⥤
            schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
          (homOfLE (show U' ⊓ V' ≤ V' from inf_le_right))).mapDerivedCategory
        if b then SV.obj B' else SU.obj A'
      let G : (k : K) → C k ⥤
          DerivedCategory (SheafOfModules.{u}
            ((moduleRings X.toRingedSpace).over (P ⊓ Q))) := fun k ↦
        (data k.val k.property).d.toDiagram.HW
      let ψ : ∀ k b, (G k).obj (F k b) ≅ RW.obj E := fun k b ↦
        let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans k.property))))
        let f := baseChangeMap t
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))))
          (Over.homMk (Spec.map (R.map (homOfLE k.property)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let U' := f ⁻¹ᵁ U
        let V' := f ⁻¹ᵁ V
        let A' : schemeDerivedCategory U'.toScheme := (derivedPullback (f ∣_ U)).obj A
        let B' : schemeDerivedCategory V'.toScheme := (derivedPullback (f ∣_ V)).obj B
        let d := (data k.val k.property).d
        let θU := (data k.val k.property).θU
        let θV := (data k.val k.property).θV
        match b with
        | true => d.toDiagram.γV.symm.app B' ≪≫ SQ.mapIso θV ≪≫ τV.app E
        | false => d.toDiagram.γU.symm.app A' ≪≫ SP.mapIso θU ≪≫ τU.app E
      let stageEquiv : ∀ k : K, C k ≌
          schemeDerivedCategory (pullback
            ((U ⊓ V).ι ≫ pullback.snd t (Spec.map (R.map (homOfLE hij))))
            (Spec.map (R.map (homOfLE k.property)))) := fun k ↦
        let arrow : Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))) ⟶
            Over.mk (Spec.map (R.map (homOfLE hij))) :=
          Over.homMk (Spec.map (R.map (homOfLE k.property)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)
        perfectOverlapStageEquivalence (baseChangeMap t arrow)
          (pullback.snd t (Spec.map (R.map (homOfLE (hij.trans k.property)))))
          (pullback.snd t (Spec.map (R.map (homOfLE hij))))
          (Spec.map (R.map (homOfLE k.property))) (isPullback_baseChangeMap t arrow) U V
      let apexEquiv : DerivedCategory (SheafOfModules.{u}
          ((moduleRings X.toRingedSpace).over (P ⊓ Q))) ≌
          schemeDerivedCategory (pullback
            ((U ⊓ V).ι ≫ pullback.snd t (Spec.map (R.map (homOfLE hij))))
            (Spec.map (c.ι.app j))) :=
        let arrow : Over.mk (Spec.map (c.ι.app i)) ⟶
            Over.mk (Spec.map (R.map (homOfLE hij))) :=
          Over.homMk (Spec.map (c.ι.app j))
            (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])
        perfectOverlapApexEquivalence gj
          (pullback.snd t (Spec.map (c.ι.app i)))
          (pullback.snd t (Spec.map (R.map (homOfLE hij))))
          (Spec.map (c.ι.app j)) (isPullback_baseChangeMap t arrow) U V
      PerfectHomObjectRealizationCore R c j C F _ (fun _ ↦ RW.obj E) G ψ
        (U ⊓ V).toScheme
        ((U ⊓ V).ι ≫ pullback.snd t (Spec.map (R.map (homOfLE hij))))
        (fun b ↦ if b then
          (derivedPullback (Yj.homOfLE (inf_le_right : U ⊓ V ≤ V))).obj B
          else (derivedPullback (Yj.homOfLE (inf_le_left : U ⊓ V ≤ U))).obj A) stageEquiv apexEquiv)

section

/-- Lift the two overlap comparisons through localization of the restriction functors.
The inverse restrictions of beta, tau, betaW and alpha define the whiskered comparison;
`map_preimage` and cancellation give the two required coherence equations. -/
noncomputable def comparisonFromRestrictions
    {C D A B W P Q T : Type*}
    [Category* C] [Category* D] [Category* A] [Category* B]
    [Category* W] [Category* P] [Category* Q] [Category* T]
    (L : C ⥤ D) (TU : C ⥤ A) (TV : C ⥤ B) (TW : C ⥤ W)
    (SU : A ⥤ W) (SV : B ⥤ W)
    (RU : D ⥤ P) (RV : D ⥤ Q) (RW : D ⥤ T)
    (SP : P ⥤ T) (SQ : Q ⥤ T)
    (αU : TU ⋙ SU ≅ TW) (αV : TV ⋙ SV ≅ TW)
    (τU : RU ⋙ SP ≅ RW) (τV : RV ⋙ SQ ≅ RW)
    [((Functor.whiskeringLeft C A T).obj TU).Full]
    [((Functor.whiskeringLeft C A T).obj TU).Faithful]
    [((Functor.whiskeringLeft C B T).obj TV).Full]
    [((Functor.whiskeringLeft C B T).obj TV).Faithful]
    (HU : A ⥤ P) (HV : B ⥤ Q) (HW : W ⥤ T)
    (βU : L ⋙ RU ≅ TU ⋙ HU) (βV : L ⋙ RV ≅ TV ⋙ HV)
    (βW : L ⋙ RW ≅ TW ⋙ HW) :
    TwoOpenComparisonDiagram L TU TV TW SU SV RU RV RW SP SQ αU αV τU τV := by
  let δU : TU ⋙ (HU ⋙ SP) ≅ TU ⋙ (SU ⋙ HW) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight βU.symm SP ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft L τU ≪≫ βW ≪≫
      Functor.isoWhiskerRight αU.symm HW ≪≫ Functor.associator _ _ _
  let δV : TV ⋙ (HV ⋙ SQ) ≅ TV ⋙ (SV ⋙ HW) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight βV.symm SQ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft L τV ≪≫ βW ≪≫
      Functor.isoWhiskerRight αV.symm HW ≪≫ Functor.associator _ _ _
  let γU := ((Functor.whiskeringLeft C A T).obj TU).preimageIso δU
  let γV := ((Functor.whiskeringLeft C B T).obj TV).preimageIso δV
  have hγU (F : C) : γU.hom.app (TU.obj F) = δU.hom.app F :=
    congrArg (fun a ↦ a.app F)
      (((Functor.whiskeringLeft C A T).obj TU).map_preimage δU.hom)
  have hγV (F : C) : γV.hom.app (TV.obj F) = δV.hom.app F :=
    congrArg (fun a ↦ a.app F)
      (((Functor.whiskeringLeft C B T).obj TV).map_preimage δV.hom)
  refine ⟨HU, HV, HW, βU, βV, βW, γU, γV, ?_, ?_⟩
  · intro F
    rw [hγU]
    simp [δU]
  · intro F
    rw [hγV]
    simp [δV]

/-- The first localization-lifted comparison evaluated on a restricted object.
Source: Stacks Project, Tag 08DW. The lifted isomorphism is the preimage of
the composite of the first-open comparison, the site restriction comparison,
the intersection comparison, and the inverse open restriction comparison.
Whiskering the preimage back along `TU` recovers that composite exactly. -/
theorem comparisonFromRestrictions_gammaU_on_image
    {C D A B W P Q T : Type*}
    [Category* C] [Category* D] [Category* A] [Category* B]
    [Category* W] [Category* P] [Category* Q] [Category* T]
    (L : C ⥤ D) (TU : C ⥤ A) (TV : C ⥤ B) (TW : C ⥤ W)
    (SU : A ⥤ W) (SV : B ⥤ W)
    (RU : D ⥤ P) (RV : D ⥤ Q) (RW : D ⥤ T)
    (SP : P ⥤ T) (SQ : Q ⥤ T)
    (αU : TU ⋙ SU ≅ TW) (αV : TV ⋙ SV ≅ TW)
    (τU : RU ⋙ SP ≅ RW) (τV : RV ⋙ SQ ≅ RW)
    [((Functor.whiskeringLeft C A T).obj TU).Full]
    [((Functor.whiskeringLeft C A T).obj TU).Faithful]
    [((Functor.whiskeringLeft C B T).obj TV).Full]
    [((Functor.whiskeringLeft C B T).obj TV).Faithful]
    (HU : A ⥤ P) (HV : B ⥤ Q) (HW : W ⥤ T)
    (βU : L ⋙ RU ≅ TU ⋙ HU) (βV : L ⋙ RV ≅ TV ⋙ HV)
    (βW : L ⋙ RW ≅ TW ⋙ HW) (F : C) :
    let δU : TU ⋙ (HU ⋙ SP) ≅ TU ⋙ (SU ⋙ HW) :=
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight βU.symm SP ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft L τU ≪≫ βW ≪≫
        Functor.isoWhiskerRight αU.symm HW ≪≫ Functor.associator _ _ _
    ((comparisonFromRestrictions L TU TV TW SU SV RU RV RW SP SQ
      αU αV τU τV HU HV HW βU βV βW).γU).hom.app (TU.obj F) =
      δU.hom.app F := by
  let δU : TU ⋙ (HU ⋙ SP) ≅ TU ⋙ (SU ⋙ HW) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight βU.symm SP ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft L τU ≪≫ βW ≪≫
      Functor.isoWhiskerRight αU.symm HW ≪≫ Functor.associator _ _ _
  change (((Functor.whiskeringLeft C A T).obj TU).preimageIso δU).hom.app
    (TU.obj F) = δU.hom.app F
  rw [Functor.preimageIso_hom]
  exact congrArg (fun a ↦ a.app F)
    (((Functor.whiskeringLeft C A T).obj TU).map_preimage δU.hom)

/-- The second localization-lifted comparison evaluated on a restricted object.
Source: Stacks Project, Tag 08DW. Whiskering the lifted second-open
isomorphism along `TV` recovers the composite of the second-open comparison,
the site restriction comparison, the intersection comparison, and the inverse
open restriction comparison. -/
theorem comparisonFromRestrictions_gammaV_on_image
    {C D A B W P Q T : Type*}
    [Category* C] [Category* D] [Category* A] [Category* B]
    [Category* W] [Category* P] [Category* Q] [Category* T]
    (L : C ⥤ D) (TU : C ⥤ A) (TV : C ⥤ B) (TW : C ⥤ W)
    (SU : A ⥤ W) (SV : B ⥤ W)
    (RU : D ⥤ P) (RV : D ⥤ Q) (RW : D ⥤ T)
    (SP : P ⥤ T) (SQ : Q ⥤ T)
    (αU : TU ⋙ SU ≅ TW) (αV : TV ⋙ SV ≅ TW)
    (τU : RU ⋙ SP ≅ RW) (τV : RV ⋙ SQ ≅ RW)
    [((Functor.whiskeringLeft C A T).obj TU).Full]
    [((Functor.whiskeringLeft C A T).obj TU).Faithful]
    [((Functor.whiskeringLeft C B T).obj TV).Full]
    [((Functor.whiskeringLeft C B T).obj TV).Faithful]
    (HU : A ⥤ P) (HV : B ⥤ Q) (HW : W ⥤ T)
    (βU : L ⋙ RU ≅ TU ⋙ HU) (βV : L ⋙ RV ≅ TV ⋙ HV)
    (βW : L ⋙ RW ≅ TW ⋙ HW) (F : C) :
    let δV : TV ⋙ (HV ⋙ SQ) ≅ TV ⋙ (SV ⋙ HW) :=
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight βV.symm SQ ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft L τV ≪≫ βW ≪≫
        Functor.isoWhiskerRight αV.symm HW ≪≫ Functor.associator _ _ _
    ((comparisonFromRestrictions L TU TV TW SU SV RU RV RW SP SQ
      αU αV τU τV HU HV HW βU βV βW).γV).hom.app (TV.obj F) =
      δV.hom.app F := by
  let δV : TV ⋙ (HV ⋙ SQ) ≅ TV ⋙ (SV ⋙ HW) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight βV.symm SQ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft L τV ≪≫ βW ≪≫
      Functor.isoWhiskerRight αV.symm HW ≪≫ Functor.associator _ _ _
  change (((Functor.whiskeringLeft C B T).obj TV).preimageIso δV).hom.app
    (TV.obj F) = δV.hom.app F
  rw [Functor.preimageIso_hom]
  exact congrArg (fun a ↦ a.app F)
    (((Functor.whiskeringLeft C B T).obj TV).map_preimage δV.hom)

/-- Evaluate a natural isomorphism at an object transported from a known component.
Source: Stacks Project, Tag 08DW, functoriality of open restriction. Naturality
along the isomorphism identifies the two components after mapping its forward
arrow. Precompose with the mapped inverse and cancel the mapped inverse-forward
composite to obtain the displayed conjugation. -/
theorem overlapNatIso_hom_app_of_iso
    {A T : Type*} [Category* A] [Category* T]
    (H K : A ⥤ T) (γ : H ≅ K) {x y : A} (e : x ≅ y) :
    γ.hom.app y = H.map e.inv ≫ γ.hom.app x ≫ K.map e.hom := by
  calc
    γ.hom.app y = H.map (𝟙 y) ≫ γ.hom.app y := by simp
    _ = H.map (e.inv ≫ e.hom) ≫ γ.hom.app y := by rw [e.inv_hom_id]
    _ = H.map e.inv ≫ (H.map e.hom ≫ γ.hom.app y) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = H.map e.inv ≫ (γ.hom.app x ≫ K.map e.hom) := by
      rw [γ.hom.naturality e.hom]
    _ = H.map e.inv ≫ γ.hom.app x ≫ K.map e.hom := by
      simp only

/-- The inverse component satisfies the same naturality transport equation.
Source: Stacks Project, Tag 08DW. Apply the forward equation to the inverse
natural isomorphism, whose source and target functors are interchanged. -/
theorem overlapNatIso_inv_app_of_iso
    {A T : Type*} [Category* A] [Category* T]
    (H K : A ⥤ T) (γ : H ≅ K) {x y : A} (e : x ≅ y) :
    γ.inv.app y = K.map e.inv ≫ γ.inv.app x ≫ H.map e.hom := by
  exact overlapNatIso_hom_app_of_iso K H γ.symm e

/-- The first open-site comparison at any object is determined by its
localization-lifted component on a restricted object.
Source: Stacks Project, Tag 08DW. Transport the inverse comparison along an
isomorphism from a restricted object by naturality. On that restricted object,
the defining preimage equation identifies it with the inverse of the explicit
comparison through `βU`, `τU`, `βW`, and `αU`. -/
theorem comparisonFromRestrictions_gammaU_inv_at_iso
    {C D A B W P Q T : Type*}
    [Category* C] [Category* D] [Category* A] [Category* B]
    [Category* W] [Category* P] [Category* Q] [Category* T]
    (L : C ⥤ D) (TU : C ⥤ A) (TV : C ⥤ B) (TW : C ⥤ W)
    (SU : A ⥤ W) (SV : B ⥤ W)
    (RU : D ⥤ P) (RV : D ⥤ Q) (RW : D ⥤ T)
    (SP : P ⥤ T) (SQ : Q ⥤ T)
    (αU : TU ⋙ SU ≅ TW) (αV : TV ⋙ SV ≅ TW)
    (τU : RU ⋙ SP ≅ RW) (τV : RV ⋙ SQ ≅ RW)
    [((Functor.whiskeringLeft C A T).obj TU).Full]
    [((Functor.whiskeringLeft C A T).obj TU).Faithful]
    [((Functor.whiskeringLeft C B T).obj TV).Full]
    [((Functor.whiskeringLeft C B T).obj TV).Faithful]
    (HU : A ⥤ P) (HV : B ⥤ Q) (HW : W ⥤ T)
    (βU : L ⋙ RU ≅ TU ⋙ HU) (βV : L ⋙ RV ≅ TV ⋙ HV)
    (βW : L ⋙ RW ≅ TW ⋙ HW)
    (F : C) {A' : A} (e : TU.obj F ≅ A') :
    let d := comparisonFromRestrictions L TU TV TW SU SV RU RV RW SP SQ
      αU αV τU τV HU HV HW βU βV βW
    let δU : TU ⋙ (HU ⋙ SP) ≅ TU ⋙ (SU ⋙ HW) :=
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight βU.symm SP ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft L τU ≪≫ βW ≪≫
        Functor.isoWhiskerRight αU.symm HW ≪≫ Functor.associator _ _ _
    d.γU.inv.app A' =
      (SU ⋙ d.HW).map e.inv ≫ δU.inv.app F ≫ (d.HU ⋙ SP).map e.hom := by
  let d := comparisonFromRestrictions L TU TV TW SU SV RU RV RW SP SQ
    αU αV τU τV HU HV HW βU βV βW
  let δU : TU ⋙ (HU ⋙ SP) ≅ TU ⋙ (SU ⋙ HW) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight βU.symm SP ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft L τU ≪≫ βW ≪≫
      Functor.isoWhiskerRight αU.symm HW ≪≫ Functor.associator _ _ _
  have hImage : d.γU.hom.app (TU.obj F) = δU.hom.app F :=
    comparisonFromRestrictions_gammaU_on_image L TU TV TW SU SV
      RU RV RW SP SQ αU αV τU τV HU HV HW βU βV βW F
  have hInv : d.γU.inv.app (TU.obj F) = δU.inv.app F :=
    (Iso.inv_eq_inv (d.γU.app (TU.obj F)) (δU.app F)).2 hImage
  change d.γU.inv.app A' =
    (SU ⋙ HW).map e.inv ≫ δU.inv.app F ≫ (HU ⋙ SP).map e.hom
  rw [overlapNatIso_inv_app_of_iso (d.HU ⋙ SP) (SU ⋙ d.HW) d.γU e, hInv]
  rfl

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (Z : Scheme.{u}) (U : Z.Opens),
  HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]

/-- The inverse site equivalence with its module universe fixed. -/
noncomputable abbrev overlapSiteInverse {X : Scheme.{u}} (U : X.Opens) :
    SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) ⥤
      SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) :=
  (Scheme.Modules.overEquiv U).inverse

/-- Natural comparison between the canonical open-site overlap functor and the
scheme pullback at the next stage. The open-site equivalence cancels by its
counit; the remaining functors agree by the cartesian component equation and
the fixed composition comparisons for derived pullback. -/
noncomputable def perfectOverlapNaturalComparisonOfSquare
    {X Y K C T S : Scheme.{u}}
    (g : X ⟶ Y) (f : K ⟶ Y)
    (pX : X ⟶ C) (pK : K ⟶ T) (pY : Y ⟶ S)
    (b : C ⟶ S) (q : T ⟶ S)
    (hg : IsPullback g pX pY b) (hf : IsPullback f pK pY q)
    (U V : Y.Opens)
    (r : (g ⁻¹ᵁ (U ⊓ V)).toScheme ⟶ (f ⁻¹ᵁ (U ⊓ V)).toScheme)
    (m : pullback ((U ⊓ V).ι ≫ pY) b ⟶
      pullback ((U ⊓ V).ι ≫ pY) q)
    (hmap :
      ((isPullback_morphismRestrict g (U ⊓ V)).paste_vert hg).isoPullback.inv ≫ r =
        m ≫ ((isPullback_morphismRestrict f (U ⊓ V)).paste_vert hf).isoPullback.inv) :
    (derivedPullback r ⋙
        (overlapSiteInverse (g ⁻¹ᵁ (U ⊓ V))).mapDerivedCategory) ⋙
      (perfectOverlapApexEquivalence g pX pY b hg U V).functor ≅
    (perfectOverlapStageEquivalence f pK pY q hf U V).functor ⋙
      derivedPullback m := by
  let Wg := g ⁻¹ᵁ (U ⊓ V)
  let eY := ((isPullback_morphismRestrict g (U ⊓ V)).paste_vert hg).isoPullback
  let eK := ((isPullback_morphismRestrict f (U ⊓ V)).paste_vert hf).isoPullback
  letI := openComparisonOverModuleAbelian X.toRingedSpace Wg
  letI := openComparisonModuleAbelian Wg.toScheme.toRingedSpace
  let site : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over Wg) ≌
      SheafOfModules.{u} (moduleRings Wg.toScheme.toRingedSpace) :=
    Scheme.Modules.overEquiv Wg
  letI : site.functor.IsEquivalence := site.isEquivalence_functor
  letI : site.inverse.IsEquivalence := site.isEquivalence_inverse
  letI : site.functor.Additive := Functor.additive_of_preserves_binary_products _
  letI : site.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let cancel := site.mapDerivedCategory.counitIso
  change (derivedPullback r ⋙ site.inverse.mapDerivedCategory) ⋙
    (site.functor.mapDerivedCategory ⋙ derivedPullback eY.inv) ≅
    derivedPullback eK.inv ⋙ derivedPullback m
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (derivedPullback r) (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft (derivedPullback r)
      (Functor.isoWhiskerRight cancel (derivedPullback eY.inv)) ≪≫
    Functor.isoWhiskerLeft (derivedPullback r) (Functor.leftUnitor _) ≪≫
    perfectOverlapDerivedPullbackTransport r eY eK m hmap

/-- Exact restriction followed by the inverse site equivalence returns to the over-site.
Use the derived site equivalence's unit and the exact-functor composition comparison. -/
noncomputable def openSiteReturnIso (X : Scheme.{u}) (U : X.Opens) :
    (schemeOpenRestriction X U).mapDerivedCategory ⋙
      (overlapSiteInverse U).mapDerivedCategory ≅
        (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory := by
  let e : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ≌
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) := Scheme.Modules.overEquiv U
  exact Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryCompIso _ _) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ e.mapDerivedCategory.unitIso.symm ≪≫
    Functor.rightUnitor _

/-- The open-site overlap comparison can be pinned to the ambient restriction
triangle. Source: Stacks Project, Tags 08BT and 08BV. Restriction to an open is
a localization, so its precomposition is fully faithful on functor categories.
Descend the pasting of the two site-return maps, the over-site comparison and
the nested scheme restriction comparison. The descent equation is the asserted
triangle and holds also for the empty open. -/
theorem openSiteOverlapIso_exists (X : Scheme.{u}) {W U : X.Opens} (i : W ⟶ U) :
    let PU := (schemeOpenRestriction X U).mapDerivedCategory
    let LU := (overlapSiteInverse U).mapDerivedCategory
    let LW := (overlapSiteInverse W).mapDerivedCategory
    let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i).mapDerivedCategory
    let SU := (schemeOpenOverlapRestriction X i).mapDerivedCategory
    let RU := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory
    let RW := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W).mapDerivedCategory
    let siteU := openSiteReturnIso X U
    let siteW := openSiteReturnIso X W
    let τ : RU ⋙ SP ≅ RW := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace) i)
    let σ := schemeDerivedOpenRestrictionCompIso X i
    ∃ ω : LU ⋙ SP ≅ SU ⋙ LW,
      Functor.isoWhiskerRight siteU SP ≪≫ τ =
        Functor.associator PU LU SP ≪≫
          Functor.isoWhiskerLeft PU ω ≪≫
            (Functor.associator PU SU LW).symm ≪≫
              Functor.isoWhiskerRight σ LW ≪≫ siteW := by
  intro PU LU LW SP SU RU RW siteU siteW τ σ
  let alpha : PU ⋙ (LU ⋙ SP) ≅ PU ⋙ (SU ⋙ LW) :=
    (Functor.associator PU LU SP).symm ≪≫
      Functor.isoWhiskerRight siteU SP ≪≫ τ ≪≫ siteW.symm ≪≫
        Functor.isoWhiskerRight σ.symm LW ≪≫ Functor.associator PU SU LW
  obtain ⟨ω, hω⟩ := Scheme.derived_open_restriction_iso_descent X U
    (LU ⋙ SP) (SU ⋙ LW) alpha
  refine ⟨ω, ?_⟩
  rw [hω]
  dsimp only [alpha]
  apply Iso.ext
  ext K
  have hσ : LW.map (σ.inv.app K) ≫ LW.map (σ.hom.app K) = 𝟙 _ := by
    rw [← LW.map_comp, Iso.inv_hom_id_app, LW.map_id]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.assoc, Category.id_comp]
  simpa only [PU, LU, SU, Functor.comp_obj, Category.assoc,
    Iso.app_hom, Iso.app_inv] using
    (cancel_iso_pasting
      (SP.map (siteU.hom.app K) ≫ τ.hom.app K) (siteW.app K)
      (LW.map (σ.inv.app K)) (LW.map (σ.hom.app K)) hσ)

/-- The natural open-site overlap comparison pinned by restriction descent. -/
noncomputable def openSiteOverlapIso (X : Scheme.{u}) {W U : X.Opens} (i : W ⟶ U) :
    (overlapSiteInverse U).mapDerivedCategory ⋙
      (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i).mapDerivedCategory ≅
    (schemeOpenOverlapRestriction X i).mapDerivedCategory ⋙
      (overlapSiteInverse W).mapDerivedCategory :=
  Classical.choose (openSiteOverlapIso_exists X i)

/-- The site-return comparison is coherent with nested open restriction.
Source: Stacks Project, Tags 08BV and 05RU. Both composites insert the same
equivalence unit on the larger open, apply the over-site restriction comparison,
and cancel the smaller-open equivalence by its unit. Exact derivation preserves
these associators and natural isomorphisms. -/
theorem openSiteReturn_overlap_triangle (X : Scheme.{u}) {W U : X.Opens}
    (i : W ⟶ U) :
    let PU := (schemeOpenRestriction X U).mapDerivedCategory
    let PW := (schemeOpenRestriction X W).mapDerivedCategory
    let LU := (overlapSiteInverse U).mapDerivedCategory
    let LW := (overlapSiteInverse W).mapDerivedCategory
    let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i).mapDerivedCategory
    let SU := (schemeOpenOverlapRestriction X i).mapDerivedCategory
    let RU := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory
    let RW := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W).mapDerivedCategory
    let siteU := openSiteReturnIso X U
    let siteW := openSiteReturnIso X W
    let τ : RU ⋙ SP ≅ RW := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace) i)
    let σ := schemeDerivedOpenRestrictionCompIso X i
    let ω := openSiteOverlapIso X i
    Functor.isoWhiskerRight siteU SP ≪≫ τ =
      Functor.associator PU LU SP ≪≫
        Functor.isoWhiskerLeft PU ω ≪≫
          (Functor.associator PU SU LW).symm ≪≫
            Functor.isoWhiskerRight σ LW ≪≫ siteW := by
  intro PU PW LU LW SP SU RU RW siteU siteW τ σ ω
  exact Classical.choose_spec (openSiteOverlapIso_exists X i)

/-- Component form of the open-site restriction triangle.
Source: Stacks Project, Tags 08BT and 08BV. Evaluate the natural triangle at
the given derived object; its associator components are identities. -/
theorem openSiteReturn_overlap_triangle_app (X : Scheme.{u}) {W U : X.Opens}
    (i : W ⟶ U) (E : schemeDerivedCategory X) :
    let PU := (schemeOpenRestriction X U).mapDerivedCategory
    let LW := (overlapSiteInverse W).mapDerivedCategory
    let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i).mapDerivedCategory
    let RU := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory
    let RW := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W).mapDerivedCategory
    let τ : RU ⋙ SP ≅ RW := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace) i)
    SP.map ((openSiteReturnIso X U).hom.app E) ≫ τ.hom.app E =
      (openSiteOverlapIso X i).hom.app (PU.obj E) ≫
        LW.map ((schemeDerivedOpenRestrictionCompIso X i).hom.app E) ≫
          (openSiteReturnIso X W).hom.app E := by
  intro PU LW SP RU RW τ
  have h := congrArg (fun e ↦ e.hom.app E) (openSiteReturn_overlap_triangle X i)
  simpa only [PU, LW, SP, RU, RW, τ, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Iso.symm_hom,
    Functor.comp_obj, Category.id_comp, Category.assoc] using h



/-- The two paths around an open-restriction square agree by pullback composition.
Use the fixed composition comparisons and the constructed open-pullback comparisons. -/
noncomputable def openPullbackRestrictionIso
    {X Y : Scheme.{u}} (g : X ⟶ Y) (P : X.Opens) (U : Y.Opens)
    (h : P ≤ g ⁻¹ᵁ U) :
    derivedPullback g ⋙ (schemeOpenRestriction X P).mapDerivedCategory ≅
      (schemeOpenRestriction Y U).mapDerivedCategory ⋙ derivedPullback (g.resLE U P h) :=
  Functor.isoWhiskerLeft _ (singleComplexOpenPullbackIso X P).symm ≪≫
    perfectHomComposition P.ι g ≪≫
    eqToIso (congrArg (fun f ↦ derivedPullback f) (g.resLE_comp_ι h).symm) ≪≫
    (perfectHomComposition (g.resLE U P h) U.ι).symm ≪≫
    Functor.isoWhiskerRight (singleComplexOpenPullbackIso Y U) _

/-- A global object whose pullback restricts to the pullback of an open object.
The global precursor exists because derived restriction to an open is a
localization and hence essentially surjective. -/
noncomputable def perfectOverlapOpenLiftObject
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (A : schemeDerivedCategory U.toScheme) : schemeDerivedCategory X := by
  let rY := (schemeOpenRestriction Y U).mapDerivedCategory
  let W := (MorphismProperty.isomorphisms _).inverseImage rY
  letI : rY.IsLocalization W := schemeDerivedOpenRestriction_isLocalization Y U
  letI : rY.EssSurj := Localization.essSurj rY W
  exact (derivedPullback f).obj (rY.objPreimage A)

/-- The chosen global lift restricts to the pulled-back open object.
Source: Stacks Project, Tag 08DW. Choose the localization preimage of the
original open object. The open-pullback square identifies restriction after
pullback with pullback after restriction; map the preimage isomorphism through
the restricted pullback functor. Their composite gives the displayed iso. -/
noncomputable def perfectOverlapOpenLiftIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (A : schemeDerivedCategory U.toScheme) :
    (schemeOpenRestriction X (f ⁻¹ᵁ U)).mapDerivedCategory.obj
        (perfectOverlapOpenLiftObject f U A) ≅
      (derivedPullback (f ∣_ U)).obj A := by
  let rY := (schemeOpenRestriction Y U).mapDerivedCategory
  let W := (MorphismProperty.isomorphisms _).inverseImage rY
  letI : rY.IsLocalization W := schemeDerivedOpenRestriction_isLocalization Y U
  letI : rY.EssSurj := Localization.essSurj rY W
  let M := rY.objPreimage A
  let e := rY.objObjPreimageIso A
  let β := openPullbackRestrictionIso f (f ⁻¹ᵁ U) U le_rfl
  change ((schemeOpenRestriction X (f ⁻¹ᵁ U)).mapDerivedCategory.obj
    ((derivedPullback f).obj M)) ≅ (derivedPullback (f ∣_ U)).obj A
  have β' :
      (schemeOpenRestriction X (f ⁻¹ᵁ U)).mapDerivedCategory.obj
          ((derivedPullback f).obj M) ≅
        (derivedPullback (f ∣_ U)).obj (rY.obj M) := by
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict, Functor.comp_obj, rY]
      using β.app M
  exact β' ≪≫ (derivedPullback (f ∣_ U)).mapIso e

/-- The fixed restriction/pullback comparison on one open. Its implementation
contains the derived open-site return, associator, and cartesian pullback
comparison; keeping this composition named avoids unfolding it while
constructing and comparing the three overlap diagram components. -/
@[irreducible] noncomputable def perfectOverlapRestrictionBeta
    {X Y : Scheme.{u}} (g : X ⟶ Y) (W : Y.Opens) (T : X.Opens)
    (hT : T ≤ g ⁻¹ᵁ W) :
    derivedPullback g ⋙
        (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) T).mapDerivedCategory ≅
      (schemeOpenRestriction Y W).mapDerivedCategory ⋙
        (derivedPullback (g.resLE W T hT) ⋙ (overlapSiteInverse T).mapDerivedCategory) :=
  Functor.isoWhiskerLeft _ (openSiteReturnIso X T).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (openPullbackRestrictionIso g T W hT) _ ≪≫
      Functor.associator _ _ _

/-- Construct a simultaneous diagram from restricted pullbacks and site equivalences.
Open restriction is a localization, so its fully faithful precomposition functor lifts
both overlap comparisons and their coherence from the global restriction diagram. -/
noncomputable def schemeComparisonFromRestrictions
    {X Y : Scheme.{u}} (g : X ⟶ Y) (U V : Y.Opens) (P Q : X.Opens)
    (hP : P ≤ g ⁻¹ᵁ U) (hQ : Q ≤ g ⁻¹ᵁ V) :
    SchemeTwoOpenComparisonDiagram X Y g U V P Q := by
  let S (W : X.Opens) := (overlapSiteInverse W).mapDerivedCategory
  let H (W : Y.Opens) (T : X.Opens) (hT : T ≤ g ⁻¹ᵁ W) :=
    derivedPullback (g.resLE W T hT) ⋙ S T
  let HU := H U P hP
  let HV := H V Q hQ
  let HW := H (U ⊓ V) (P ⊓ Q) (by
    intro x hx
    exact ⟨hP hx.1, hQ hx.2⟩)
  let β (W : Y.Opens) (T : X.Opens) (hT : T ≤ g ⁻¹ᵁ W) :
      derivedPullback g ⋙
          (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) T).mapDerivedCategory ≅
        (schemeOpenRestriction Y W).mapDerivedCategory ⋙ H W T hT :=
    perfectOverlapRestrictionBeta g W T hT
  let TU := (schemeOpenRestriction Y U).mapDerivedCategory
  let TV := (schemeOpenRestriction Y V).mapDerivedCategory
  let T := DerivedCategory (SheafOfModules.{u}
    ((moduleRings X.toRingedSpace).over (P ⊓ Q)))
  have : TU.IsLocalization ((MorphismProperty.isomorphisms _).inverseImage TU) :=
    schemeDerivedOpenRestriction_isLocalization Y U
  have : TV.IsLocalization ((MorphismProperty.isomorphisms _).inverseImage TV) :=
    schemeDerivedOpenRestriction_isLocalization Y V
  have := Localization.full_whiskeringLeft TU
    ((MorphismProperty.isomorphisms _).inverseImage TU) T
  have := Localization.faithful_whiskeringLeft TU
    ((MorphismProperty.isomorphisms _).inverseImage TU) T
  have := Localization.full_whiskeringLeft TV
    ((MorphismProperty.isomorphisms _).inverseImage TV) T
  have := Localization.faithful_whiskeringLeft TV
    ((MorphismProperty.isomorphisms _).inverseImage TV) T
  refine ⟨comparisonFromRestrictions (derivedPullback g) TU TV _ _ _ _ _ _ _ _ _ _ _ _
    HU HV HW (β U P hP) (β V Q hQ) (β (U ⊓ V) (P ⊓ Q) _)⟩

/-- Construct the transport data for two composable scheme maps.
The restricted composites agree after their open inclusions; pullback composition gives
kappa. Set theta equal to kappa, the supplied local isomorphism, and the site comparison. -/
noncomputable def transportDataOfComposite
    {X Y Y₀ : Scheme.{u}} (f : Y ⟶ Y₀) (g : X ⟶ Y) (gf : X ⟶ Y₀)
    (hgf : g ≫ f = gf) (U V : Y₀.Opens)
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (E : schemeDerivedCategory X)
    (φU : (derivedPullback (gf ∣_ U)).obj A ≅
      (schemeOpenRestriction X (gf ⁻¹ᵁ U)).mapDerivedCategory.obj E)
    (φV : (derivedPullback (gf ∣_ V)).obj B ≅
      (schemeOpenRestriction X (gf ⁻¹ᵁ V)).mapDerivedCategory.obj E) :
    let P := gf ⁻¹ᵁ U
    let Q := gf ⁻¹ᵁ V
    let RU := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) P).mapDerivedCategory
    let RV := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) Q).mapDerivedCategory
    let LU := (overlapSiteInverse P).mapDerivedCategory
    let LV := (overlapSiteInverse Q).mapDerivedCategory
    TwoOpenTransportData (SchemeTwoOpenComparisonDiagram X Y g (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) P Q)
      (fun d ↦ d.toDiagram.HU) (fun d ↦ d.toDiagram.HV)
      (derivedPullback (f ∣_ U)) (derivedPullback (f ∣_ V))
      (derivedPullback (gf ∣_ U)) (derivedPullback (gf ∣_ V)) LU LV
      (schemeOpenRestriction X P).mapDerivedCategory
      (schemeOpenRestriction X Q).mapDerivedCategory RU RV A B E φU φV := by
  let hP (W : Y₀.Opens) : gf ⁻¹ᵁ W ≤ g ⁻¹ᵁ (f ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, hgf]
  let d := schemeComparisonFromRestrictions g (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)
    (gf ⁻¹ᵁ U) (gf ⁻¹ᵁ V) (hP U) (hP V)
  let κ (W : Y₀.Opens) :
      derivedPullback (f ∣_ W) ⋙
          (derivedPullback (g.resLE (f ⁻¹ᵁ W) (gf ⁻¹ᵁ W) (hP W)) ⋙
            (overlapSiteInverse (gf ⁻¹ᵁ W)).mapDerivedCategory) ≅
        derivedPullback (gf ∣_ W) ⋙
          (overlapSiteInverse (gf ⁻¹ᵁ W)).mapDerivedCategory := by
    have eqW : g.resLE (f ⁻¹ᵁ W) (gf ⁻¹ᵁ W) (hP W) ≫ (f ∣_ W) = gf ∣_ W := by
      apply (cancel_mono W.ι).1
      simp only [Category.assoc, morphismRestrict_ι]
      rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hgf]
    exact (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (perfectHomComposition _ _ ≪≫
        eqToIso (congrArg (fun a ↦ derivedPullback a) eqW)) _
  exact {
    d := d
    κU := κ U
    κV := κ V
    siteU := openSiteReturnIso X (gf ⁻¹ᵁ U)
    siteV := openSiteReturnIso X (gf ⁻¹ᵁ V)
    θU := (κ U).app A ≪≫ (overlapSiteInverse (gf ⁻¹ᵁ U)).mapDerivedCategory.mapIso φU ≪≫
      (openSiteReturnIso X (gf ⁻¹ᵁ U)).app E
    θV := (κ V).app B ≪≫ (overlapSiteInverse (gf ⁻¹ᵁ V)).mapDerivedCategory.mapIso φV ≪≫
      (openSiteReturnIso X (gf ⁻¹ᵁ V)).app E
    hθU := rfl
    hθV := rfl }

/-- The diagram field of composite transport is the restriction diagram for the
second map.
Source: Stacks Project, Tags 08DW and 0D5S. The composite transport first
constructs the restriction comparison for `g` on both inverse-image opens; its
remaining fields add the two pullback-composition isomorphisms and the local
object identifications. Projecting the diagram field therefore returns that
restriction comparison. The two inclusion proofs agree by the equality
`g ≫ f = gf`, and proof irrelevance identifies their presentations. -/
theorem transportDataOfComposite_diagram
    {X Y Y₀ : Scheme.{u}} (f : Y ⟶ Y₀) (g : X ⟶ Y) (gf : X ⟶ Y₀)
    (hgf : g ≫ f = gf) (U V : Y₀.Opens)
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (E : schemeDerivedCategory X)
    (φU : (derivedPullback (gf ∣_ U)).obj A ≅
      (schemeOpenRestriction X (gf ⁻¹ᵁ U)).mapDerivedCategory.obj E)
    (φV : (derivedPullback (gf ∣_ V)).obj B ≅
      (schemeOpenRestriction X (gf ⁻¹ᵁ V)).mapDerivedCategory.obj E) :
    (transportDataOfComposite f g gf hgf U V A B E φU φV).d =
      schemeComparisonFromRestrictions g (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)
        (gf ⁻¹ᵁ U) (gf ⁻¹ᵁ V)
        (by rw [← Scheme.Hom.comp_preimage, hgf])
        (by rw [← Scheme.Hom.comp_preimage, hgf]) := by
  unfold transportDataOfComposite
  rfl

/-- The first site field is the fixed return comparison for the inverse-image open.
This follows by projecting the first site component of the composite transport
construction; no choice of restriction diagram affects the component. -/
theorem transportDataOfComposite_siteU
    {X Y Y₀ : Scheme.{u}} (f : Y ⟶ Y₀) (g : X ⟶ Y) (gf : X ⟶ Y₀)
    (hgf : g ≫ f = gf) (U V : Y₀.Opens)
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (E : schemeDerivedCategory X)
    (φU : (derivedPullback (gf ∣_ U)).obj A ≅
      (schemeOpenRestriction X (gf ⁻¹ᵁ U)).mapDerivedCategory.obj E)
    (φV : (derivedPullback (gf ∣_ V)).obj B ≅
      (schemeOpenRestriction X (gf ⁻¹ᵁ V)).mapDerivedCategory.obj E) :
    (transportDataOfComposite f g gf hgf U V A B E φU φV).siteU =
      openSiteReturnIso X (gf ⁻¹ᵁ U) := by
  rfl

/-- The second site field is the fixed return comparison for its inverse-image open.
Projecting the second site component of the composite transport gives this equation. -/
theorem transportDataOfComposite_siteV
    {X Y Y₀ : Scheme.{u}} (f : Y ⟶ Y₀) (g : X ⟶ Y) (gf : X ⟶ Y₀)
    (hgf : g ≫ f = gf) (U V : Y₀.Opens)
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (E : schemeDerivedCategory X)
    (φU : (derivedPullback (gf ∣_ U)).obj A ≅
      (schemeOpenRestriction X (gf ⁻¹ᵁ U)).mapDerivedCategory.obj E)
    (φV : (derivedPullback (gf ∣_ V)).obj B ≅
      (schemeOpenRestriction X (gf ⁻¹ᵁ V)).mapDerivedCategory.obj E) :
    (transportDataOfComposite f g gf hgf U V A B E φU φV).siteV =
      openSiteReturnIso X (gf ⁻¹ᵁ V) := by
  rfl



end

/-- The fixed restriction and pullback comparison at each later stage. -/
@[no_expose] noncomputable def perfectOverlapCanonicalComparisonFamily
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    (hstage : ∀ (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens),
      ∃ k : I, j ≤ k)
    (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens)
    (hcover : U ⊔ V = ⊤)
    (hU : IsCompact (U : Set (↥(pullback t (Spec.map (R.map (homOfLE hij)))))))
    (hV : IsCompact (V : Set (↥(pullback t (Spec.map (R.map (homOfLE hij)))))))
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (hA : U.toScheme.IsPerfect A) (hB : V.toScheme.IsPerfect B)
    (E : schemeDerivedCategory (pullback t (Spec.map (c.ι.app i))))
    (φU : (derivedPullback (baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])) ∣_ U)).obj A ≅
      (schemeOpenRestriction _ _).mapDerivedCategory.obj E)
    (φV : (derivedPullback (baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])) ∣_ V)).obj B ≅
      (schemeOpenRestriction _ _).mapDerivedCategory.obj E) :
    (k : I) → (hjk : j ≤ k) →
      perfectOverlapComparisonDataType R c hc i Z t j hij hstage
        U V hcover hU hV A B hA hB E φU φV k hjk := by
  intro k hjk
  let aj : Over.mk (Spec.map (c.ι.app i)) ⟶
      Over.mk (Spec.map (R.map (homOfLE hij))) :=
    Over.homMk (Spec.map (c.ι.app j))
      (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])
  let ak : Over.mk (Spec.map (c.ι.app i)) ⟶
      Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))) :=
    Over.homMk (Spec.map (c.ι.app k))
      (by dsimp; rw [← Spec.map_comp, c.w (homOfLE (hij.trans hjk))])
  let jk : Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))) ⟶
      Over.mk (Spec.map (R.map (homOfLE hij))) :=
    Over.homMk (Spec.map (R.map (homOfLE hjk)))
      (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)
  have hcomp : ak ≫ jk = aj := by
    ext
    change Spec.map (c.ι.app k) ≫ Spec.map (R.map (homOfLE hjk)) = Spec.map (c.ι.app j)
    rw [← Spec.map_comp, c.w (homOfLE hjk)]
  have hgf : baseChangeMap t ak ≫ baseChangeMap t jk = baseChangeMap t aj := by
    rw [← baseChangeMap_comp, hcomp]
  exact transportDataOfComposite (baseChangeMap t jk) (baseChangeMap t ak)
    (baseChangeMap t aj) hgf U V A B E φU φV

/-- Comparison data for one fixed later stage of the overlap construction.
The construction is the single-stage restriction and pullback comparison from
Tags 09RE and 08DW; the family theorem only packages these independent choices.
(blueprint: lem-pc-perfect-overlap-object-realization-core-data-at).
-/
theorem perfect_overlap_object_realization_core_data_at
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} ((SheafOfModules.{u})
        ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    (hstage : ∀ (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens),
      ∃ k : I, j ≤ k)
    (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens)
    (hcover : U ⊔ V = ⊤)
    (hU : IsCompact (U : Set (↥(pullback t (Spec.map (R.map (homOfLE hij)))))))
    (hV : IsCompact (V : Set (↥(pullback t (Spec.map (R.map (homOfLE hij)))))))
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (hA : U.toScheme.IsPerfect A) (hB : V.toScheme.IsPerfect B)
    (E : schemeDerivedCategory (pullback t (Spec.map (c.ι.app i))))
    (φU : (derivedPullback (baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])) ∣_ U)).obj A ≅
      (schemeOpenRestriction _ _).mapDerivedCategory.obj E)
    (φV : (derivedPullback (baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])) ∣_ V)).obj B ≅
      (schemeOpenRestriction _ _).mapDerivedCategory.obj E)
    (k : I) (hjk : j ≤ k) :
    Nonempty (perfectOverlapComparisonDataType R c hc i Z t j hij hstage
      U V hcover hU hV A B hA hB E φU φV k hjk) := by
  exact ⟨perfectOverlapCanonicalComparisonFamily R c hc i Z t j hij hstage
    U V hcover hU hV A B hA hB E φU φV k hjk⟩

/-- The prescribed overlap comparison data exists simultaneously at every stage.
For each later index, identify the inverse-image intersection with the cartesian
base change of `U ⊓ V`, pull back along this identification, and apply the inverse
open-site equivalence. Restriction and derived-pullback composition comparisons
provide the transport data and theta equations.
(blueprint: lem-pc-perfect-overlap-object-realization-core-data-family).
-/
theorem perfect_overlap_object_realization_core_data_family
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} ((SheafOfModules.{u})
        ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    (hstage : ∀ (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens),
      ∃ k : I, j ≤ k)
    (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens)
    (hcover : U ⊔ V = ⊤)
    (hU : IsCompact (U : Set (↥(pullback t (Spec.map (R.map (homOfLE hij)))))))
    (hV : IsCompact (V : Set (↥(pullback t (Spec.map (R.map (homOfLE hij)))))))
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (hA : U.toScheme.IsPerfect A) (hB : V.toScheme.IsPerfect B)
    (E : schemeDerivedCategory (pullback t (Spec.map (c.ι.app i))))
    (φU : (derivedPullback (baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])) ∣_ U)).obj A ≅
      (schemeOpenRestriction _ _).mapDerivedCategory.obj E)
    (φV : (derivedPullback (baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])) ∣_ V)).obj B ≅
      (schemeOpenRestriction _ _).mapDerivedCategory.obj E) :
    Nonempty (Σ data : (k : I) → (hjk : j ≤ k) →
      perfectOverlapComparisonDataType R c hc i Z t j hij hstage
        U V hcover hU hV A B hA hB E φU φV k hjk, Unit) := by
  classical
  let data : (k : I) → (hjk : j ≤ k) →
      perfectOverlapComparisonDataType R c hc i Z t j hij hstage
        U V hcover hU hV A B hA hB E φU φV k hjk := fun k hjk ↦
    Classical.choice (perfect_overlap_object_realization_core_data_at R c hc i Z t j hij
      hstage U V hcover hU hV A B hA hB E φU φV k hjk)
  exact ⟨data, ()⟩

set_option maxHeartbeats 8000000 in
-- The dependent core record has seven large functorial fields.
/-- Given the canonical stagewise comparison data, the transition and object pins
are assembled into the core realization structure.  The transition is obtained by
conjugating the overlap pullback functor by the fixed stage and apex equivalences.
The counit-pinned derived-pullback composition comparison gives `baseComparison`
and `transition_pin`; its naturality gives `comparison`.  Expanding the prescribed
`ψ` and the theta equations cancels the site unit and counit and proves `object_pin`.
This is the cartesian composition calculation from Tags 08DW and 0D5S.
(blueprint: lem-pc-perfect-overlap-object-realization-core-of-data).
-/
-- The canonicality hypothesis rules out independently twisted transports, which
-- make the unrestricted statement false (K1 delivery report).
theorem perfect_overlap_object_realization_core_of_data
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} ((SheafOfModules.{u})
        ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    (hstage : ∀ (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens),
      ∃ k : I, j ≤ k) :
    let Yj := pullback t (Spec.map (R.map (homOfLE hij)))
    let X := pullback t (Spec.map (c.ι.app i))
    let gj := baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))
    ∀ (U V : Yj.Opens) (hcover : U ⊔ V = ⊤)
      (hU : IsCompact (U : Set Yj)) (hV : IsCompact (V : Set Yj))
      (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
      (hA : U.toScheme.IsPerfect A) (hB : V.toScheme.IsPerfect B)
      (E : schemeDerivedCategory X),
    let instP : Category (schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme) := inferInstance
    let instQ : Category (schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme) := inferInstance
    let instX : Category (schemeDerivedCategory X) := inferInstance
    let PU : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ U)).mapDerivedCategory
    let PV : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ V)).mapDerivedCategory
    ∀ (φU : (derivedPullback (gj ∣_ U)).obj A ≅
        PU.obj E)
      (φV : (derivedPullback (gj ∣_ V)).obj B ≅
        PV.obj E),
      let P := gj ⁻¹ᵁ U
      let Q := gj ⁻¹ᵁ V
      let RU := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) P).mapDerivedCategory
      let RV := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) Q).mapDerivedCategory
      let RW := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) (P ⊓ Q)).mapDerivedCategory
      let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ P from inf_le_left))).mapDerivedCategory
      let SQ := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ Q from inf_le_right))).mapDerivedCategory
      let τU : RU ⋙ SP ≅ RW := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ P from inf_le_left)))
      let τV : RV ⋙ SQ ≅ RW := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ Q from inf_le_right)))
    ∀ (data : (k : I) → (hjk : j ≤ k) →
      perfectOverlapComparisonDataType R c hc i Z t j hij hstage
        U V hcover hU hV A B hA hB E φU φV k hjk),
    data = perfectOverlapCanonicalComparisonFamily R c hc i Z t j hij hstage
      U V hcover hU hV A B hA hB E φU φV →
    Nonempty (
      let K := {k : I // j ≤ k}
      let C : K → Type (u + 1) := fun k ↦
        let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans k.property))))
        let f := baseChangeMap t
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))))
          (Over.homMk (Spec.map (R.map (homOfLE k.property)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let U' := f ⁻¹ᵁ U
        let V' := f ⁻¹ᵁ V
        schemeDerivedCategory (U' ⊓ V').toScheme
      let F : (k : K) → Bool → C k := fun k b ↦
        let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans k.property))))
        let f := baseChangeMap t
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))))
          (Over.homMk (Spec.map (R.map (homOfLE k.property)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let U' := f ⁻¹ᵁ U
        let V' := f ⁻¹ᵁ V
        let A' : schemeDerivedCategory U'.toScheme := (derivedPullback (f ∣_ U)).obj A
        let B' : schemeDerivedCategory V'.toScheme := (derivedPullback (f ∣_ V)).obj B
        let SU : schemeDerivedCategory U'.toScheme ⥤
            schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
          (homOfLE (show U' ⊓ V' ≤ U' from inf_le_left))).mapDerivedCategory
        let SV : schemeDerivedCategory V'.toScheme ⥤
            schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
          (homOfLE (show U' ⊓ V' ≤ V' from inf_le_right))).mapDerivedCategory
        if b then SV.obj B' else SU.obj A'
      let G : (k : K) → C k ⥤
          DerivedCategory (SheafOfModules.{u}
            ((moduleRings X.toRingedSpace).over (P ⊓ Q))) := fun k ↦
        (data k.val k.property).d.toDiagram.HW
      let ψ : ∀ k b, (G k).obj (F k b) ≅ RW.obj E := fun k b ↦
        let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans k.property))))
        let f := baseChangeMap t
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))))
          (Over.homMk (Spec.map (R.map (homOfLE k.property)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let U' := f ⁻¹ᵁ U
        let V' := f ⁻¹ᵁ V
        let A' : schemeDerivedCategory U'.toScheme := (derivedPullback (f ∣_ U)).obj A
        let B' : schemeDerivedCategory V'.toScheme := (derivedPullback (f ∣_ V)).obj B
        let d := (data k.val k.property).d
        let θU := (data k.val k.property).θU
        let θV := (data k.val k.property).θV
        match b with
        | true => d.toDiagram.γV.symm.app B' ≪≫ SQ.mapIso θV ≪≫ τV.app E
        | false => d.toDiagram.γU.symm.app A' ≪≫ SP.mapIso θU ≪≫ τU.app E
      let stageEquiv : ∀ k : K, C k ≌
          schemeDerivedCategory (pullback
            ((U ⊓ V).ι ≫ pullback.snd t (Spec.map (R.map (homOfLE hij))))
            (Spec.map (R.map (homOfLE k.property)))) := fun k ↦
        let arrow : Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))) ⟶
            Over.mk (Spec.map (R.map (homOfLE hij))) :=
          Over.homMk (Spec.map (R.map (homOfLE k.property)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)
        perfectOverlapStageEquivalence (baseChangeMap t arrow)
          (pullback.snd t (Spec.map (R.map (homOfLE (hij.trans k.property)))))
          (pullback.snd t (Spec.map (R.map (homOfLE hij))))
          (Spec.map (R.map (homOfLE k.property))) (isPullback_baseChangeMap t arrow) U V
      let apexEquiv : DerivedCategory (SheafOfModules.{u}
          ((moduleRings X.toRingedSpace).over (P ⊓ Q))) ≌
          schemeDerivedCategory (pullback
            ((U ⊓ V).ι ≫ pullback.snd t (Spec.map (R.map (homOfLE hij))))
            (Spec.map (c.ι.app j))) :=
        let arrow : Over.mk (Spec.map (c.ι.app i)) ⟶
            Over.mk (Spec.map (R.map (homOfLE hij))) :=
          Over.homMk (Spec.map (c.ι.app j))
            (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])
        perfectOverlapApexEquivalence gj
          (pullback.snd t (Spec.map (c.ι.app i)))
          (pullback.snd t (Spec.map (R.map (homOfLE hij))))
          (Spec.map (c.ι.app j)) (isPullback_baseChangeMap t arrow) U V
      PerfectHomObjectRealizationCore R c j C F _ (fun _ ↦ RW.obj E) G ψ
        (U ⊓ V).toScheme
        ((U ⊓ V).ι ≫ pullback.snd t (Spec.map (R.map (homOfLE hij))))
        (fun b ↦ if b then
          (derivedPullback (Yj.homOfLE (inf_le_right : U ⊓ V ≤ V))).obj B
          else (derivedPullback (Yj.homOfLE (inf_le_left : U ⊓ V ≤ U))).obj A)
        stageEquiv apexEquiv) := by
  classical
  intro Yj X gj U V hcover hU hV A B hA hB E instP instQ instX PU PV φU φV
    P Q RU RV RW SP SQ τU τV data hdata
  sorry

set_option maxHeartbeats 8000000 in
-- The Hom-continuity packaging unfolds a large dependent proposition.
/-- Geometric natural comparison and pinned object comparisons.
Source: Stacks Project, Tags 09RE, 08DW and 0D5S.
(blueprint: lem-pc-perfect-overlap-object-realization-core-data).

Proof: Identify the inverse-image intersections with the base changes of U intersection V
by the universal property of pullbacks. Derive pullback along these scheme isomorphisms,
and compose the apex equivalence with the inverse open-site equivalence. The restriction
and composition isomorphisms give the stage object isomorphisms. Restrict phiU and phiV
and compose with the apex cartesian isomorphism to give the apex object isomorphisms.
Construct the comparison diagrams using these same pullbacks and open-site equivalences.
Set theta to kappa followed by the image of phi followed by site; both theta equations
are reflexive. The cartesian composition comparison gives the natural comparison.
Expanding psi and theta, the site unit/counit cancel. Restriction coherence cancels
gamma and tau. Associativity of the fixed counit-pinned comparison gives object_pin.
All constructions apply to empty and coincident opens as well as arbitrary objects.
-/
theorem perfect_overlap_object_realization_core_data
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    (hstage : ∀ (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens),
      ∃ k : I, j ≤ k)
    : perfectOverlapObjectRealizationCoreStatement R c hc i Z t j hij hstage := by
  unfold perfectOverlapObjectRealizationCoreStatement
  intro Yj X gj U V hcover hU hV A B hA hB E instP instQ instX PU PV φU φV
    P Q RU RV RW SP SQ τU τV
  let data := perfectOverlapCanonicalComparisonFamily R c hc i Z t j hij hstage
    U V hcover hU hV A B hA hB E φU φV
  exact ⟨⟨data, Classical.choice
    (perfect_overlap_object_realization_core_of_data R c hc i Z t j hij hstage
      U V hcover hU hV A B hA hB E φU φV data rfl)⟩⟩

end AlgebraicGeometry
