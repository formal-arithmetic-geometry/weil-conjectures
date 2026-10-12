/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
public import Sheaf.AlgebraicGeometry.Picard.CanonicalSingleDirectImageComparison
public import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.AlgebraicGeometry.Picard.CanonicalSingleAdjunctionTranspose
import Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackSquare
import Sheaf.AlgebraicGeometry.Picard.CanonicalDirectImageH0Unit
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction

/-! # Degree-zero compatibility square for the canonical mate

Source: Stacks Project, Cohomology, Remark 08HY.
(blueprint: lem-pc-canonical-degree-zero-mate-square).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

private theorem transposeCounit {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (M : D) :
    adj.homEquiv _ _ (adj.counit.app M) = 𝟙 _ := by
  change adj.homEquiv (R.obj M) M (adj.counit.app M) = _
  rw [← adj.homEquiv_symm_id]
  exact Equiv.apply_symm_apply _ _

private theorem counitOfTranspose {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {X : C} {Y : D}
    (a : L.obj X ⟶ Y) (b : X ⟶ R.obj Y) (h : adj.homEquiv X Y a = b) :
    L.map b ≫ adj.counit.app Y = a := by
  exact (adj.homEquiv_counit X Y b).symm.trans
    ((adj.homEquiv X Y).symm_apply_eq.mpr h.symm)

private theorem transposeComposite {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {X X' : C} {Y Y' : D}
    (u : X' ⟶ X) (a : L.obj X ⟶ Y) (v : Y ⟶ Y') :
    u ≫ adj.homEquiv _ _ a ≫ R.map v = adj.homEquiv _ _ (L.map u ≫ a ≫ v) := by
  exact (congrArg (fun q ↦ u ≫ q) (adj.homEquiv_naturality_right a v).symm).trans
    (adj.homEquiv_naturality_left u (a ≫ v)).symm

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The standard degree-zero direct-image identification, computed by the existing
comparison of unbounded and bounded below derived functors.
Source: Stacks, Tags 079V and 0A1G
(blueprint: lem-pc-canonical-degree-zero-mate-square). -/
def canonicalDirectImageH0Iso {X S : Scheme.{u}} (f : X ⟶ S)
    [HasInjectiveResolutions X.Modules] (M : X.Modules) :
    (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
        ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M)) ≅
      (pushforward f).obj M :=
  (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).homologyRightDerivedFunctorObjSingleFunctorIso
      M 0 ≪≫
    (pushforward f).rightDerivedZeroIsoSelf.app M

private theorem canonicalSingleMateSquare
    {X S X' S' : Scheme.{u}} (f : X ⟶ S)
    (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (h : g' ≫ f = f' ≫ g) (M : X.Modules) :
    let E := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M
    let c := (pullbackComp g' f).app ((pushforward f).obj M) ≪≫
      (pullbackCongr h).app ((pushforward f).obj M) ≪≫
      ((pullbackComp f' g).app ((pushforward f).obj M)).symm
    canonicalSinglePullbackMap g ((pushforward f).obj M) ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0).map
          ((pullbackPushforwardAdjunction f').homEquiv _ _
            (c.inv ≫ (pullback g').map ((pullbackPushforwardAdjunction f).counit.app M))) ≫
        canonicalSingleDirectImageMap f' ((pullback g').obj M) =
      (derivedPullback g).map (canonicalSingleDirectImageMap f M) ≫
        schemeDerivedBaseChangeMap f f' g g' h E ≫
        (schemeDerivedDirectImage f').map (canonicalSinglePullbackMap g' M) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let adj := (Classical.choose (exists_schemeDerivedAdjunction.{u, w} f
    (hAdd := (Classical.choose exists_derivedPullbackComposition.{u, w}) f)
    ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) f)
    ((Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))) f)))
  let adj' := (Classical.choose (exists_schemeDerivedAdjunction.{u, w} f'
    (hAdd := (Classical.choose exists_derivedPullbackComposition.{u, w}) f')
    ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) f')
    ((Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))) f')))
  let d : derivedPullback g ⋙ derivedPullback f' ≅
      derivedPullback f ⋙ derivedPullback g' :=
    ((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))) f' g) ≪≫
      eqToIso (congrArg (fun k : X' ⟶ S ↦ derivedPullback.{u, w} k) h.symm) ≪≫
      ((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))) g' f).symm
  let E := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M
  let a := (pullbackPushforwardAdjunction f).counit.app M
  let u := canonicalSingleDirectImageMap f M
  let c := (pullbackComp g' f).app ((pushforward f).obj M) ≪≫
    (pullbackCongr h).app ((pushforward f).obj M) ≪≫
    ((pullbackComp f' g).app ((pushforward f).obj M)).symm
  let b := c.inv ≫ (pullback g').map a
  have ht := canonicalSingleAdjunctionTranspose f ((pushforward f).obj M) M a
  have htranspose : adj.homEquiv _ _
      (canonicalSinglePullbackMap f ((pushforward f).obj M) ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map a) = u := by
    have ha := transposeCounit (pullbackPushforwardAdjunction f) M
    let T := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0
    change adj.homEquiv _ _
      (canonicalSinglePullbackMap f ((pushforward f).obj M) ≫
        (DerivedCategory.singleFunctor _ 0).map a) = u
    calc
      _ = T.map ((pullbackPushforwardAdjunction f).homEquiv _ _ a) ≫ u := ht
      _ = T.map (𝟙 _) ≫ u := congrArg (fun q ↦ T.map q ≫ u) ha
      _ = u := (congrArg (fun q ↦ q ≫ u) (T.map_id _)).trans (Category.id_comp _)
  have hcounit : (derivedPullback f).map u ≫ adj.counit.app E =
      canonicalSinglePullbackMap f ((pushforward f).obj M) ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map a := by
    exact counitOfTranspose adj _ u htranspose
  have hp := canonicalSinglePullbackSquare f g g' f' h ((pushforward f).obj M) M a
  have htp := canonicalSingleAdjunctionTranspose f' ((pullback g).obj
    ((pushforward f).obj M)) ((pullback g').obj M) b
  have hn := d.hom.naturality u
  dsimp only [Functor.comp_map] at hn
  have hbeta : schemeDerivedBaseChangeMap f f' g g' h E =
      adj'.homEquiv _ _
        (d.hom.app ((schemeDerivedDirectImage f).obj E) ≫
          (derivedPullback g').map (adj.counit.app E)) := by
    simp only [schemeDerivedBaseChangeMap, d, Iso.trans_hom, NatTrans.comp_app,
      Iso.symm_hom, eqToIso.hom, eqToHom_app, Category.assoc]
    rfl
  have hp' : d.hom.app ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj ((pushforward f).obj M)) ≫
      (derivedPullback g').map
        (canonicalSinglePullbackMap f ((pushforward f).obj M) ≫
          (DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map a) ≫
      canonicalSinglePullbackMap g' M =
    (derivedPullback f').map (canonicalSinglePullbackMap g ((pushforward f).obj M)) ≫
      canonicalSinglePullbackMap f' ((pullback g).obj ((pushforward f).obj M)) ≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).map b := by
    simpa only [d, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, eqToIso.hom,
      eqToHom_app, Category.assoc] using hp
  rw [hbeta]
  have hright := transposeComposite adj' ((derivedPullback g).map u)
    (d.hom.app ((schemeDerivedDirectImage f).obj E) ≫
      (derivedPullback g').map (adj.counit.app E)) (canonicalSinglePullbackMap g' M)
  have hs : (derivedPullback f').map ((derivedPullback g).map u) ≫
      (d.hom.app ((schemeDerivedDirectImage f).obj E) ≫
        (derivedPullback g').map (adj.counit.app E)) ≫
      canonicalSinglePullbackMap g' M =
    (derivedPullback f').map (canonicalSinglePullbackMap g ((pushforward f).obj M)) ≫
      canonicalSinglePullbackMap f' ((pullback g).obj ((pushforward f).obj M)) ≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).map b := by
    rw [← Category.assoc, ← Category.assoc, hn]
    simp only [Category.assoc]
    erw [← Functor.map_comp_assoc, hcounit]
    exact hp'
  calc
    _ = canonicalSinglePullbackMap g ((pushforward f).obj M) ≫
        adj'.homEquiv _ _ (canonicalSinglePullbackMap f'
          ((pullback g).obj ((pushforward f).obj M)) ≫
            (DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).map b) :=
      congrArg (fun q ↦ canonicalSinglePullbackMap g ((pushforward f).obj M) ≫ q) htp.symm
    _ = adj'.homEquiv _ _
        ((derivedPullback f').map (canonicalSinglePullbackMap g ((pushforward f).obj M)) ≫
          canonicalSinglePullbackMap f' ((pullback g).obj ((pushforward f).obj M)) ≫
          (DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).map b) :=
      (adj'.homEquiv_naturality_left _ _).symm
    _ = _ := (congrArg (adj'.homEquiv _ _) hs.symm).trans hright.symm


/-- The comparison square commutes for every module and every commutative square.
It asserts no invertibility of the single-complex comparisons or of base change.
Source: Stacks, Cohomology, Remark 08HY; canonical mates and derived adjunctions.
(blueprint: lem-pc-canonical-degree-zero-mate-square).

Proof: Apply the pinned derived Hom equivalence to the underived counit, embedded
as a single-complex morphism. Its defining factorization through the left-derived
counit and right-derived unit is exists_schemeDerivedAdjunction. The derived
composition comparisons are the lifts of the corresponding underived comparisons
through those same left-derived counits. Naturality of these counits and the
right-derived unit therefore identifies the two transposes around the square.
Transport tensor pullback to ordinary pullback by leftAdjointUniq; its counit law
identifies the tensor transpose with the displayed ordinary mate. Take H^0.
The single-complex homology identification is natural. For direct image, the
unbounded-to-bounded-below comparison is characterized by its right-derived unit;
the injective-resolution H^0 comparison followed by rightDerivedZeroIsoSelf takes
that unit to the identity. Thus these identifications give exactly the displayed
square. No quasi-isomorphism of a pullback comparison is used. The proof applies
also to zero modules and empty schemes. -/
theorem canonicalDegreeZeroMateSquare
    {X S X' S' : Scheme.{u}} (f : X ⟶ S)
    (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (h : g' ≫ f = f' ≫ g)
    [HasInjectiveResolutions X'.Modules] (M : X.Modules) :
    let E := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0
    let c := (pullbackComp g' f).app ((pushforward f).obj M) ≪≫
      (pullbackCongr h).app ((pushforward f).obj M) ≪≫
      ((pullbackComp f' g).app ((pushforward f).obj M)).symm
    let k := (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0).app
        ((pullback g).obj ((pushforward f).obj M))
    H.map (canonicalSinglePullbackMap g ((pushforward f).obj M)) ≫ k.hom ≫
        (pullbackPushforwardAdjunction f').homEquiv _ _
          (c.inv ≫ (pullback g').map ((pullbackPushforwardAdjunction f).counit.app M)) =
      H.map ((derivedPullback g).map (canonicalSingleDirectImageMap f M)) ≫
        H.map (schemeDerivedBaseChangeMap f f' g g' h E) ≫
        H.map ((schemeDerivedDirectImage f').map (canonicalSinglePullbackMap g' M)) ≫
        (canonicalDirectImageH0Iso f' ((pullback g').obj M)).hom := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0
  let c := (pullbackComp g' f).app ((pushforward f).obj M) ≪≫
    (pullbackCongr h).app ((pushforward f).obj M) ≪≫
    ((pullbackComp f' g).app ((pushforward f).obj M)).symm
  let m : (pullback g).obj ((pushforward f).obj M) ⟶
      (pushforward f').obj ((pullback g').obj M) :=
    (pullbackPushforwardAdjunction f').homEquiv _ _
    (c.inv ≫ (pullback g').map ((pullbackPushforwardAdjunction f).counit.app M))
  have hn := (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0).hom.naturality m
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  have hu := canonicalDirectImageH0Unit f' ((pullback g').obj M)
  change H.map (canonicalSingleDirectImageMap f' ((pullback g').obj M)) ≫
    (canonicalDirectImageH0Iso f' ((pullback g').obj M)).hom = _ at hu
  change H.map (canonicalSingleDirectImageMap f' ((pullback g').obj M)) ≫
      (canonicalDirectImageH0Iso f' ((pullback g').obj M)).hom =
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0).hom.app
        ((pushforward f').obj ((pullback g').obj M)) at hu
  have hs := congrArg H.map (canonicalSingleMateSquare f g g' f' h M)
  simp only [Functor.map_comp] at hs
  have hn' := hn.symm.trans
    (congrArg (fun q ↦ H.map ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0).map m) ≫ q) hu.symm)
  change H.map (canonicalSinglePullbackMap g ((pushforward f).obj M)) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0).hom.app
        ((pullback g).obj ((pushforward f).obj M)) ≫ m = _
  calc
    _ = H.map (canonicalSinglePullbackMap g ((pushforward f).obj M)) ≫
        H.map ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0).map m) ≫
        H.map (canonicalSingleDirectImageMap f' ((pullback g').obj M)) ≫
        (canonicalDirectImageH0Iso f' ((pullback g').obj M)).hom :=
      congrArg (fun q ↦ H.map (canonicalSinglePullbackMap g ((pushforward f).obj M)) ≫ q) hn'
    _ = _ := by
      simpa only [Category.assoc, m, c, H, Functor.id_obj] using
        congrArg (fun q ↦ q ≫ (canonicalDirectImageH0Iso f' ((pullback g').obj M)).hom) hs

end AlgebraicGeometry.Scheme.Modules
