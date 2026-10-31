/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfPackageLocalizationBoundaryData

/-! # Rationalization of a tower-pinned localization boundary -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u v w v' w'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

section CoefficientSquares
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {D : FiniteFieldDatum.{u}}
  {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
  {B' : SixFunctorSpace D → Type v'} [∀ X, Category.{w'} (B' X)]
  {P : SixFunctorPushStage D B} {P' : SixFunctorPushStage D B'}
  {L : ∀ X, B X ⥤ B' X} (a : SixFunctorCoefficientComparison P P' L)
  {Z U X Y : SixFunctorSpace D} (i : Z ⟶ X) (j : U ⟶ X) (f : X ⟶ Y)
  [IsProper i.hom.left] (hj : IsOpenImmersion j.hom.left)
  (c : Compactification f.hom.left)
  (cj : Compactification (j ≫ f).hom.left) (ci : Compactification (i ≫ f).hom.left)

private theorem sfPackageCoefficientOpen (K : B U) :
    (L Y).map ((P.composition j f (sixFunctorOpenCompactification j hj) c cj).hom.app K ≫
        (P.support f c).map ((P.openIdentification j hj).hom.app K)) ≫
      (a.supportAdjunction f c).left.hom.app ((P.openExtension j hj).obj K) ≫
      (P'.support f c).map ((a.openExtension j hj).hom.app K) =
    (a.supportAdjunction (j ≫ f) cj).left.hom.app K ≫
      (P'.composition j f (sixFunctorOpenCompactification j hj) c cj).hom.app ((L U).obj K) ≫
      (P'.support f c).map ((P'.openIdentification j hj).hom.app ((L U).obj K)) := by
  have hn := (a.supportAdjunction f c).left.hom.naturality
    ((P.openIdentification j hj).hom.app K)
  simp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  rw [← Functor.map_comp, a.openIdentification, Functor.map_comp]
  simpa only [Category.assoc] using
    congrArg (fun z ↦ z ≫ (P'.support f c).map
      ((P'.openIdentification j hj).hom.app ((L U).obj K)))
      (a.composition j f (sixFunctorOpenCompactification j hj) c cj K)

private theorem sfPackageCoefficientClosed (K : B Z) :
    (L Y).map ((P.composition i f (.ofIsProper i.hom.left) c ci).hom.app K ≫
        (P.support f c).map ((P.properIdentity i).hom.app K)) ≫
      (a.supportAdjunction f c).left.hom.app ((P.direct i).obj K) ≫
      (P'.support f c).map ((a.directAdjunction i).right.hom.app K) =
    (a.supportAdjunction (i ≫ f) ci).left.hom.app K ≫
      (P'.composition i f (.ofIsProper i.hom.left) c ci).hom.app ((L Z).obj K) ≫
      (P'.support f c).map ((P'.properIdentity i).hom.app ((L Z).obj K)) := by
  have hn := (a.supportAdjunction f c).left.hom.naturality
    ((P.properIdentity i).hom.app K)
  simp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  rw [← Functor.map_comp, a.properIdentity, Functor.map_comp]
  simpa only [Category.assoc] using
    congrArg (fun z ↦ z ≫ (P'.support f c).map
      ((P'.properIdentity i).hom.app ((L Z).obj K)))
      (a.composition i f (.ofIsProper i.hom.left) c ci K)

private def sfPackageCoefficientOuter (g : Z ⟶ X)
    (cg : Compactification (g ≫ f).hom.left) :
    (P.pull g ⋙ P.support (g ≫ f) cg) ⋙ L Y ≅
      L X ⋙ (P'.pull g ⋙ P'.support (g ≫ f) cg) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (a.supportAdjunction (g ≫ f) cg).left ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (a.directAdjunction g).left _ ≪≫
    Functor.associator _ _ _

private theorem sfPackageCoefficientFirst (K : B X) :
    (L Y).map ((sfPackageLocalizationFirst P j f hj c cj).app K) ≫
      (a.supportAdjunction f c).left.hom.app K =
    (sfPackageLocalizationCoefficientVertex a j f cj K).hom ≫
      (sfPackageLocalizationFirst P' j f hj c cj).app ((L X).obj K) := by
  let t := P.composition j f (sixFunctorOpenCompactification j hj) c cj ≪≫
    Functor.isoWhiskerRight (P.openIdentification j hj) (P.support f c)
  let t' := P'.composition j f (sixFunctorOpenCompactification j hj) c cj ≪≫
    Functor.isoWhiskerRight (P'.openIdentification j hj) (P'.support f c)
  have ht := sfPackageCoefficientOpen a j f hj c cj ((P.pull j).obj K)
  dsimp only [sfPackageLocalizationFirst, sfPackageLocalizationOpenComparison,
    NatTrans.comp_app, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app]
  simp only [Functor.comp_obj, Functor.id_obj, Category.comp_id]
  dsimp only [sfPackageLocalizationCoefficientVertex, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom]
  change (L Y).map (t.hom.app _ ≫ (P.support f c).map
      ((P.openAdjunction j hj).counit.app K)) ≫
      (a.supportAdjunction f c).left.hom.app K =
    ((a.supportAdjunction (j ≫ f) cj).left.hom.app _ ≫
      (P'.support (j ≫ f) cj).map ((a.directAdjunction j).left.hom.app K)) ≫
      (t'.hom.app _ ≫ (P'.support f c).map ((P'.openAdjunction j hj).counit.app _))
  have hco : (a.openExtension j hj).hom.app ((P.pull j).obj K) ≫
      (P'.openExtension j hj).map ((a.directAdjunction j).left.hom.app K) ≫
      (P'.openAdjunction j hj).counit.app ((L X).obj K) =
        (L X).map ((P.openAdjunction j hj).counit.app K) := by
    rw [← a.openAdjunction_left j hj, ← a.openAdjunction_right j hj]
    rw [(a.openAdjunction j hj).counit, Iso.hom_inv_id_app_assoc]
  have ht' : (L Y).map (t.hom.app ((P.pull j).obj K)) ≫
      (a.supportAdjunction f c).left.hom.app _ ≫
      (P'.support f c).map ((a.openExtension j hj).hom.app ((P.pull j).obj K)) =
    (a.supportAdjunction (j ≫ f) cj).left.hom.app _ ≫ t'.hom.app _ := by
    simpa only [t, t', Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.map_comp,
      Category.assoc] using ht
  have hn₀ := (a.supportAdjunction f c).left.hom.naturality
    ((P.openAdjunction j hj).counit.app K)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn₀
  rw [Functor.map_comp, Category.assoc, hn₀]
  simp only [Category.assoc]
  rw [← hco, Functor.map_comp, Functor.map_comp]
  have h := congrArg (fun z ↦ z ≫
    (P'.support f c).map ((P'.openExtension j hj).map
      ((a.directAdjunction j).left.hom.app K)) ≫
    (P'.support f c).map ((P'.openAdjunction j hj).counit.app ((L X).obj K))) ht'
  have hn := congrArg (fun z ↦
    (a.supportAdjunction (j ≫ f) cj).left.hom.app ((P.pull j).obj K) ≫ z ≫
      (P'.support f c).map ((P'.openAdjunction j hj).counit.app ((L X).obj K)))
    (t'.hom.naturality ((a.directAdjunction j).left.hom.app K))
  simp only [Functor.comp_map, Category.assoc] at h hn ⊢
  exact h.trans hn.symm

private theorem sfPackageCoefficientSecond (K : B X) :
    (L Y).map ((sfPackageLocalizationSecond P i f c ci).app K) ≫
      (sfPackageLocalizationCoefficientVertex a i f ci K).hom =
    (a.supportAdjunction f c).left.hom.app K ≫
      (sfPackageLocalizationSecond P' i f c ci).app ((L X).obj K) := by
  let t := P.composition i f (.ofIsProper i.hom.left) c ci ≪≫
    Functor.isoWhiskerRight (P.properIdentity i) (P.support f c)
  let t' := P'.composition i f (.ofIsProper i.hom.left) c ci ≪≫
    Functor.isoWhiskerRight (P'.properIdentity i) (P'.support f c)
  let q := (a.directAdjunction i).right.hom.app ((P.pull i).obj K) ≫
    (P'.direct i).map ((a.directAdjunction i).left.hom.app K)
  have ht := sfPackageCoefficientClosed a i f c ci ((P.pull i).obj K)
  have hcomp :
      (sfPackageLocalizationCoefficientVertex a i f ci K).hom ≫ t'.hom.app _ =
    (L Y).map (t.hom.app _) ≫ (a.supportAdjunction f c).left.hom.app _ ≫
      (P'.support f c).map q := by
    dsimp only [sfPackageLocalizationCoefficientVertex, Iso.trans_hom,
      Functor.mapIso_hom, Iso.app_hom]
    have hn := congrArg (fun z ↦
      (a.supportAdjunction (i ≫ f) ci).left.hom.app ((P.pull i).obj K) ≫ z)
      (t'.hom.naturality ((a.directAdjunction i).left.hom.app K))
    have h := congrArg (fun z ↦ z ≫ (P'.support f c).map
      ((P'.direct i).map ((a.directAdjunction i).left.hom.app K))) ht
    simp only [Functor.comp_map] at hn
    simp only [t', Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Category.assoc] at hn
    simp only [Category.assoc] at h
    simpa only [q, t, t', Functor.comp_obj, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.map_comp, Category.assoc] using hn.trans h.symm
  dsimp only [sfPackageLocalizationSecond, sfPackageLocalizationClosedComparison,
    NatTrans.comp_app, Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.leftUnitor_inv_app]
  simp only [Category.id_comp]
  apply (cancel_mono (t'.hom.app ((P'.pull i).obj ((L X).obj K)))).mp
  change ((L Y).map ((P.support f c).map ((P.pullDirectAdjunction i).unit.app K) ≫
      t.inv.app _) ≫ (sfPackageLocalizationCoefficientVertex a i f ci K).hom) ≫
        t'.hom.app _ =
    ((a.supportAdjunction f c).left.hom.app K ≫
      (P'.support f c).map ((P'.pullDirectAdjunction i).unit.app _) ≫ t'.inv.app _) ≫
        t'.hom.app _
  rw [Category.assoc, hcomp]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app]
  rw [← Category.assoc ((L Y).map (t.inv.app _)), ← Functor.map_comp,
    Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]
  have hn := (a.supportAdjunction f c).left.hom.naturality
    ((P.pullDirectAdjunction i).unit.app K)
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  rw [← Functor.map_comp]
  exact congrArg (fun z ↦ (a.supportAdjunction f c).left.hom.app K ≫
    (P'.support f c).map z) ((a.directAdjunction i).unit K)


end CoefficientSquares

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
  {Z U X Y : SixFunctorSpace D}
  [IsSeparated Z.obj.hom] [IsSeparated U.obj.hom]
  [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
  (i : Z ⟶ X) (j : U ⟶ X) (f : X ⟶ Y)
  [IsClosedImmersion i.hom.left] (hj : IsOpenImmersion j.hom.left)
  [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
  (c : Compactification f.hom.left)
  (cj : Compactification (j ≫ f).hom.left) (ci : Compactification (i ≫ f).hom.left)

/-- Raw rationalization carries a supplied tower boundary to the actual rational
support values, with the prescribed rationalization comparisons and shift.
Source: current blueprint prop-functor-package.proof.md, clause (3), coefficient
passage; prop-weil-pbc-rational-transport.
(blueprint: lem-sf-package-localization-rational-transport).

Proof: the tower witness supplies a natural integral boundary and an ambient
triangle. The full exact constructible inclusion reflects distinguished triangles,
so this is a distinguished integral triangle. Apply the canonical scalar-localization
functor to its three maps, including its connecting arrow and prescribed shift.
Conjugate by the outer pullback/support comparisons of H.rationalization. The
unit/counit equations and compatibility with composition, open identification and
proper coincidence identify the first two maps with the displayed rational ones.
The scalar-localization universal property extends the resulting boundary uniquely
from integral morphisms to fractions; naturality follows by linearity. Every raw
rational object has the same underlying integral object, so the distinguishedness
holds on every input. The third conjugation equation is exactly the asserted
coefficient-boundary equation. This argument works for either empty stratum. -/
theorem sfPackageLocalizationRationalTransport
    (H : SixFunctorHigherOperations D C E)
    (hl : IsUnit (C.l : D.k))
    (δI : SfPackageLocalizationBoundary H.integral i j f cj ci
      (𝟭 (sfIntegralConstructibleCategory C.l E Y.obj.left)))
    (hI : SfPackageLocalizationTowerBoundary i j f hj c cj ci H hl δI) :
    ∃ δR : SfPackageLocalizationBoundary H.rational i j f cj ci
        (𝟭 (sfRationalConstructibleCategory C.l E Y.obj.left)),
      SfPackageLocalizationCoefficientBoundary H.rationalization f i j cj ci
        (sfRationalLocalizationCommShift C.l E Y.obj.left) δI δR ∧
      ∀ K : sfRationalConstructibleCategory C.l E X.obj.left,
        sfPackageLocalizationTriangle H.rational i j f hj c cj ci
          (𝟭 (sfRationalConstructibleCategory C.l E Y.obj.left)) δR K ∈ distTriang _ := by
  sorry
end WeilConjectures
