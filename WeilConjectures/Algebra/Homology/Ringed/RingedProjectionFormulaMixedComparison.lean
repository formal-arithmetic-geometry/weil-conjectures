/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Projection.ProjectionFormulaArrows
import WeilConjectures.Algebra.Homology.Ringed.RingedProjectionFormulaMixedNaturality
import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral

/-! The canonical tensor comparison with one flat K-flat input. -/

@[expose] public section
set_option autoImplicit false
universe u v u' v' w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
attribute [local instance 2000] Limits.instHasColimitOfHasColimitsOfShape
  Limits.instHasLimitOfHasLimitsOfShape

open CategoryTheory.Functor in
set_option synthInstance.maxSize 2048 in
private theorem tensorMap_factor
    {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A] [HasCoproducts.{0} A]
    {P P' Q Q' : CochainComplex A ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    HomologicalComplex.mapBifunctorMap f (𝟙 Q) (curriedTensor A) (.up ℤ) ≫
      HomologicalComplex.mapBifunctorMap (𝟙 P') g (curriedTensor A) (.up ℤ) =
      HomologicalComplex.mapBifunctorMap f g (curriedTensor A) (.up ℤ) := by
  simp [HomologicalComplex.mapBifunctorMap, ← HomologicalComplex₂.total.map_comp]

open CategoryTheory.Functor in
set_option synthInstance.maxSize 2048 in
private theorem tensorPullbackTotal_naturality
    {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory A]
    {B : Type u'} [Category.{v'} B] [Abelian B] [MonoidalCategory B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    [HasCoproducts.{0} A] [HasCoproducts.{0} B]
    (L : A ⥤ B) [L.Additive]
    (e : ∀ X Y : A, L.obj (X ⊗ Y) ≅ L.obj X ⊗ L.obj Y)
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom =
        (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    {P P' Q Q' : CochainComplex A ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    HomologicalComplex.mapBifunctorMap
      ((L.mapHomologicalComplex (.up ℤ)).map f)
      ((L.mapHomologicalComplex (.up ℤ)).map g) (curriedTensor B) (.up ℤ) ≫
        tensorPullbackTotal L e he P' Q' =
      tensorPullbackTotal L e he P Q ≫ (L.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap f g (curriedTensor A) (.up ℤ)) := by
  have hi {X X' Y Y' : A} (a : X ⟶ X') (b : Y ⟶ Y') :
      (L.map a ⊗ₘ L.map b) ≫ (e X' Y').inv =
        (e X Y).inv ≫ L.map (a ⊗ₘ b) := by
    apply (cancel_mono (e X' Y').hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [he, Iso.inv_hom_id_assoc]
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  simp only [HomologicalComplex.comp_f, tensorPullbackTotal]
  erw [HomologicalComplex.ι_mapBifunctorMap_assoc]
  erw [tensorPullbackTotalComponent, HomologicalComplex.ι_mapBifunctorDesc]
  erw [HomologicalComplex.ι_mapBifunctorDesc_assoc]
  change (L.map (f.f a) ▷ L.obj (Q.X b)) ≫
    (L.obj (P'.X a) ◁ L.map (g.f b)) ≫ (e (P'.X a) (Q'.X b)).inv ≫
      L.map (CochainComplex.ιMapBifunctor P' Q' (curriedTensor A) a b n hab) =
    ((e (P.X a) (Q.X b)).inv ≫
      L.map (CochainComplex.ιMapBifunctor P Q (curriedTensor A) a b n hab)) ≫
        L.map ((HomologicalComplex.mapBifunctorMap f g (curriedTensor A) (.up ℤ)).f n)
  rw [← tensorHom_def_assoc, Category.assoc]
  rw [← Category.assoc, hi, Category.assoc, ← L.map_comp]
  congr 2
  rw [← L.map_comp]
  congr 1
  rw [HomologicalComplex.ι_mapBifunctorMap]
  rw [tensorHom_def, Category.assoc]
  rfl


set_option maxHeartbeats 1000000 in
-- Normalize the defining square at the identity total tensor maps.
/-- At a flat pair, apply the defining resolution square to the identity resolution.
The two localized identities and the tensor of the identities are identities, leaving
exactly the inverse representative isomorphism rR. -/
private theorem mixedTensorRepresentative_flat
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u}) [HasDerivedCategory.{w} (SheafOfModules.{u} ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
  (PR : ObjectProperty (CochainComplex (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ))
  (hPR : ∀ P, PR P ↔ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat)
  (TR : DerivedCategory (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) × DerivedCategory (SheafOfModules.{u} ((sheafCompose J (forget₂
      CommRingCat.{u} RingCat.{u})).obj R)) ⥤ DerivedCategory (SheafOfModules.{u} ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))
  (rR : (PR.ι.prod PR.ι) ⋙ Functor.uncurry.obj
    ((@curriedTensor (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R)) _ (monoidalCategory R)).map₂HomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
        ((PR.ι ⋙ DerivedCategory.Q).prod (PR.ι ⋙ DerivedCategory.Q)) ⋙ TR)
    (P F : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (hp : PR P) (hf : PR F) :
    (mixedTensorRepresentative R PR hPR TR rR P F hf).hom =
      rR.inv.app (⟨P, hp⟩, ⟨F, hf⟩) := by
  have hh := Classical.choose_spec
    (mixedTensorRepresentative_existsUnique R PR hPR TR rR P F hf).exists
      P hp (𝟙 P) (by infer_instance)
  have hi : HomologicalComplex.mapBifunctorMap (𝟙 P) (𝟙 F)
      (@curriedTensor (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) _
          (monoidalCategory R)) (.up ℤ) = 𝟙 _ := by
    simp [HomologicalComplex.mapBifunctorMap]
  erw [hi] at hh
  erw [DerivedCategory.Q.map_id, DerivedCategory.Q.map_id] at hh
  change TR.map (𝟙 _) ≫ (mixedTensorRepresentative R PR hPR TR rR P F hf).hom =
    rR.inv.app (⟨P, hp⟩, ⟨F, hf⟩) ≫ 𝟙 _ at hh
  erw [TR.map_id, Category.id_comp, Category.comp_id] at hh
  exact hh

set_option maxHeartbeats 3000000 in
-- The comparison transports several total-complex functors with large instance arguments.
set_option synthInstance.maxHeartbeats 100000 in
/-- The canonical derived tensor comparison on a mixed representative is the localization
of the inverse of the levelwise canonical tensor comparison.
Source: Stacks 07A4 and the representative characterization in definition 1264.
(blueprint: new-lem-weil-pbc-projection-mixed-tensor-comparison).
Proof: resolve A by a flat-term K-flat complex P. The defining squares of the two
mixed representatives identify their composites with the images of that resolution.
The canonical comparison square applies to the flat pair (P,F); at these inputs the
mixed comparisons are exactly the inverses of rR and rS. Naturality of the derived
comparison, the pullback comparison, the mixed representatives, and the total chain
comparison transports this square along P to A. Cancel the invertible localization
of the resolution in the source. -/
theorem ringedTensorComparison_mixed
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{u}} {S RI : Sheaf JD CommRingCat.{u}}
    (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (uPush : Sheaf JD (Type u) ⥤ Sheaf JC (Type u))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (uStar : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
    (hobj : ∀ M : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R), uStar.obj M = changeOfRings
        c (I.modules.obj M))
    (hmap : ∀ {M N : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)} (a : M ⟶ N), uStar.map a =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫
        eqToHom (hobj N).symm)
    [uStar.Additive]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))]
    (LF : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
    (epsilon : DerivedCategory.Qh ⋙ LF ⟶
      uStar.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hLF : LF.IsLeftDerivedFunctor epsilon
      (HomotopyCategory.quasiIso (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (ComplexShape.up ℤ)))
    (PR : ObjectProperty (CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ))
    (PS : ObjectProperty (CochainComplex (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) ℤ))
    (hPR : ∀ P, PR P ↔ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat)
    (hPS : ∀ P, PS P ↔ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat)
    (TR : (DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) × (DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))
    (TS : (DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))) × (DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
    (rR : (PR.ι.prod PR.ι) ⋙ Functor.uncurry.obj
        ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) _
          (SheafOfModules.monoidalCategory R)).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      ((PR.ι ⋙ DerivedCategory.Q).prod (PR.ι ⋙ DerivedCategory.Q)) ⋙ TR)
    (rS : (PS.ι.prod PS.ι) ⋙ Functor.uncurry.obj
        ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) _
          (SheafOfModules.monoidalCategory S)).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      ((PS.ι ⋙ DerivedCategory.Q).prod (PS.ι ⋙ DerivedCategory.Q)) ⋙ TS)
    (k : CanonicalRingedTensorComparison R S RI uInv I c uStar hobj)
    (V : SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⥤
      SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (am :
      uStar ⊣ V)
    (A F : CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (hf : PR F) (huf : PS ((uStar.mapHomologicalComplex (.up ℤ)).obj F)) :
    LF.map (mixedTensorRepresentative R PR hPR TR rR A F hf).hom ≫
        derivedPullbackComplexComparison uStar LF epsilon
          (CochainComplex.mapBifunctor A F
            (@curriedTensor (SheafOfModules.{u}
              ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) _
                (monoidalCategory R))) ≫
        DerivedCategory.Q.map (k.totalIso R S RI uInv I c uStar hobj V am A F).inv =
      (ringedTopoiCanonicalDerivedTensorComparison uInv uPush adj I c uStar hobj hmap LF
        epsilon hLF PR PS hPR hPS TR TS rR rS k V am).hom.app
          (DerivedCategory.Q.obj A, DerivedCategory.Q.obj F) ≫
        TS.map (Prod.mkHom (derivedPullbackComplexComparison uStar LF epsilon A)
          (derivedPullbackComplexComparison uStar LF epsilon F)) ≫
        (mixedTensorRepresentative S PS hPS TS rS
          ((uStar.mapHomologicalComplex (.up ℤ)).obj A)
          ((uStar.mapHomologicalComplex (.up ℤ)).obj F) huf).hom := by
  let M := SheafOfModules.{u}
    ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
  let N := SheafOfModules.{u}
    ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)
  let : MonoidalCategory M := monoidalCategory R
  let : MonoidalCategory N := monoidalCategory S
  let : MonoidalPreadditive M := ringedTensorPreadditive R
  let : MonoidalPreadditive N := ringedTensorPreadditive S
  let U := uStar.mapHomologicalComplex (.up ℤ)
  let tR := Functor.uncurry.obj ((@curriedTensor M _ (monoidalCategory R)).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ))
  let tS := Functor.uncurry.obj ((@curriedTensor N _ (monoidalCategory S)).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ))
  let eps : DerivedCategory.Q ⋙ LF ⟶ U ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso M).inv LF ≫
      Functor.whiskerLeft (HomotopyCategory.quotient M (.up ℤ)) epsilon ≫
      Functor.whiskerRight (uStar.mapHomotopyCategoryFactors (.up ℤ)).hom DerivedCategory.Qh ≫
      Functor.whiskerLeft U (DerivedCategory.quotientCompQhIso N).hom
  let alpha := ringedTopoiCanonicalDerivedTensorComparison uInv uPush adj I c uStar hobj hmap
    LF epsilon hLF PR PS hPR hPS TR TS rR rS k V am
  let mR (X : CochainComplex M ℤ) :
      TR.obj (DerivedCategory.Q.obj X, DerivedCategory.Q.obj F) ≅
        DerivedCategory.Q.obj (tR.obj (X, F)) :=
    mixedTensorRepresentative R PR hPR TR rR X F hf
  let mS (X : CochainComplex N ℤ) :
      TS.obj (DerivedCategory.Q.obj X, DerivedCategory.Q.obj (U.obj F)) ≅
        DerivedCategory.Q.obj (tS.obj (X, U.obj F)) :=
    mixedTensorRepresentative S PS hPS TS rS X (U.obj F) huf
  let b : (U.prod U) ⋙ tS ≅ tR ⋙ U := NatIso.ofComponents
    (fun X ↦ k.totalIso R S RI uInv I c uStar hobj V am X.1 X.2)
    (by
      intro X Y f
      simp only [CanonicalRingedTensorComparison.totalIso, asIso_hom]
      dsimp only [U, tR, tS, Functor.comp_map, Functor.prod_map, Functor.prod_obj,
        CanonicalRingedTensorComparison.total]
      simp only [Functor.uncurry_obj_map, Functor.map₂HomologicalComplex, tensorMap_factor]
      exact tensorPullbackTotal_naturality uStar k.mu k.naturality f.1 f.2)
  obtain ⟨P, p, hk, ht, hq, _⟩ := CochainComplex.exists_isKFlatResolutionGeneral A
  have hp : PR P := (hPR P).2 ⟨hk, ht⟩
  obtain ⟨hp', _, hflat⟩ := Classical.choose_spec
    (ringedTopoiCanonicalDerivedTensorPullback uInv uPush adj I c uStar hobj hmap LF epsilon
      hLF PR PS hPR hPS TR TS rR rS k V am).2.exists P F hp hf
  have hmR := mixedTensorRepresentative_flat R PR hPR TR rR P F hp hf
  have hmS := mixedTensorRepresentative_flat S PS hPS TS rS (U.obj P) (U.obj F) hp' huf
  have hflat' : LF.map (mR P).hom ≫ eps.app (tR.obj (P, F)) ≫
        DerivedCategory.Q.map (b.inv.app (P, F)) =
      alpha.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj F) ≫
        TS.map (Prod.mkHom (eps.app P) (eps.app F)) ≫ (mS (U.obj P)).hom := by
    apply (cancel_epi (LF.map (rR.hom.app (⟨P, hp⟩, ⟨F, hf⟩)))).1
    erw [hmR, hmS]
    erw [← LF.map_comp_assoc, Iso.hom_inv_id_app, LF.map_id, Category.id_comp]
    have hh0 : LF.map (rR.hom.app (⟨P, hp⟩, ⟨F, hf⟩)) ≫
        alpha.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj F) ≫
          TS.map (Prod.mkHom (eps.app P) (eps.app F)) =
        eps.app (tR.obj (P, F)) ≫ DerivedCategory.Q.map (b.inv.app (P, F)) ≫
          rS.hom.app (⟨U.obj P, hp'⟩, ⟨U.obj F, huf⟩) := by exact hflat
    have hh := congrArg (fun z ↦ z ≫ rS.inv.app (⟨U.obj P, hp'⟩, ⟨U.obj F, huf⟩)) hh0
    simp only [Category.assoc] at hh
    erw [Iso.hom_inv_id_app, Category.comp_id] at hh
    exact hh.symm
  have hqp : IsIso (DerivedCategory.Q.{w}.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso M p).2 hq
  let := hqp
  have : IsIso (Prod.mkHom (DerivedCategory.Q.map p) (𝟙 (DerivedCategory.Q.obj F))) :=
    (isIso_prod_iff _ _).2 ⟨by infer_instance, by infer_instance⟩
  have : IsIso (LF.map (TR.map
      (Prod.mkHom (DerivedCategory.Q.map p) (𝟙 (DerivedCategory.Q.obj F))))) := by
    infer_instance
  apply (cancel_epi (LF.map (TR.map
    (Prod.mkHom (DerivedCategory.Q.map p) (𝟙 (DerivedCategory.Q.obj F)))))).1
  change LF.map (TR.map (Prod.mkHom (DerivedCategory.Q.map p) (𝟙 _))) ≫
      (LF.map (mR A).hom ≫ eps.app (tR.obj (A, F)) ≫
        DerivedCategory.Q.map (b.inv.app (A, F))) =
    LF.map (TR.map (Prod.mkHom (DerivedCategory.Q.map p) (𝟙 _))) ≫
      (alpha.hom.app (DerivedCategory.Q.obj A, DerivedCategory.Q.obj F) ≫
        TS.map (Prod.mkHom (eps.app A) (eps.app F)) ≫ (mS (U.obj A)).hom)
  have hnr := mixedTensorRepresentative_naturality R PR hPR TR rR p F hf
  have hns := mixedTensorRepresentative_naturality S PS hPS TS rS (U.map p) (U.obj F) huf
  have hna := alpha.hom.naturality
    (Prod.mkHom (DerivedCategory.Q.map p) (𝟙 (DerivedCategory.Q.obj F)))
  have hne := eps.naturality p
  have hnet := eps.naturality (tR.map (Prod.mkHom p (𝟙 F)))
  have hnb := b.inv.naturality (Prod.mkHom p (𝟙 F))
  change LF.map (DerivedCategory.Q.map (tR.map (Prod.mkHom p (𝟙 F)))) ≫
    eps.app (tR.obj (A, F)) = eps.app (tR.obj (P, F)) ≫
      DerivedCategory.Q.map (U.map (tR.map (Prod.mkHom p (𝟙 F)))) at hnet
  change LF.map (TR.map (Prod.mkHom (DerivedCategory.Q.map p) (𝟙 _))) ≫
      alpha.hom.app (DerivedCategory.Q.obj A, DerivedCategory.Q.obj F) =
    alpha.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj F) ≫
      TS.map (Prod.mkHom (LF.map (DerivedCategory.Q.map p))
        (LF.map (𝟙 (DerivedCategory.Q.obj F)))) at hna
  erw [LF.map_id] at hna
  change LF.map (DerivedCategory.Q.map p) ≫ eps.app A =
    eps.app P ≫ DerivedCategory.Q.map (U.map p) at hne
  change U.map (tR.map (Prod.mkHom p (𝟙 F))) ≫ b.inv.app (A, F) =
    b.inv.app (P, F) ≫ tS.map (Prod.mkHom (U.map p) (U.map (𝟙 F))) at hnb
  erw [U.map_id] at hnb
  have htR : tR.map (Prod.mkHom p (𝟙 F)) =
      HomologicalComplex.mapBifunctorMap p (𝟙 F)
        (@curriedTensor M _ (monoidalCategory R)) (.up ℤ) := by
    simp only [tR, Functor.uncurry_obj_map, Functor.map₂HomologicalComplex, tensorMap_factor]
  have htS : tS.map (Prod.mkHom (U.map p) (𝟙 (U.obj F))) =
      HomologicalComplex.mapBifunctorMap (U.map p) (𝟙 (U.obj F))
        (@curriedTensor N _ (monoidalCategory S)) (.up ℤ) := by
    simp only [tS, Functor.uncurry_obj_map, Functor.map₂HomologicalComplex, tensorMap_factor]
  erw [← htR] at hnr
  erw [← htS] at hns
  change TR.map (Prod.mkHom (DerivedCategory.Q.map p) (𝟙 _)) ≫ (mR A).hom =
    (mR P).hom ≫ DerivedCategory.Q.map (tR.map (Prod.mkHom p (𝟙 F))) at hnr
  change TS.map (Prod.mkHom (DerivedCategory.Q.map (U.map p)) (𝟙 _)) ≫
      (mS (U.obj A)).hom = (mS (U.obj P)).hom ≫
        DerivedCategory.Q.map (tS.map (Prod.mkHom (U.map p) (𝟙 (U.obj F)))) at hns
  calc
    _ = LF.map (mR P).hom ≫ LF.map (DerivedCategory.Q.map
        (tR.map (Prod.mkHom p (𝟙 F)))) ≫ eps.app (tR.obj (A, F)) ≫
          DerivedCategory.Q.map (b.inv.app (A, F)) := by
      rw [← LF.map_comp_assoc, hnr, LF.map_comp, Category.assoc]
    _ = LF.map (mR P).hom ≫ eps.app (tR.obj (P, F)) ≫
        DerivedCategory.Q.map (U.map (tR.map (Prod.mkHom p (𝟙 F)))) ≫
          DerivedCategory.Q.map (b.inv.app (A, F)) := by rw [reassoc_of% hnet]
    _ = LF.map (mR P).hom ≫ eps.app (tR.obj (P, F)) ≫
        DerivedCategory.Q.map (b.inv.app (P, F)) ≫
          DerivedCategory.Q.map (tS.map (Prod.mkHom (U.map p) (𝟙 (U.obj F)))) := by
      rw [← DerivedCategory.Q.map_comp, hnb, DerivedCategory.Q.map_comp]
    _ = alpha.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj F) ≫
        TS.map (Prod.mkHom (eps.app P) (eps.app F)) ≫ (mS (U.obj P)).hom ≫
          DerivedCategory.Q.map (tS.map (Prod.mkHom (U.map p) (𝟙 (U.obj F)))) := by
      simpa only [Category.assoc] using congrArg
        (fun z ↦ z ≫ DerivedCategory.Q.map
          (tS.map (Prod.mkHom (U.map p) (𝟙 (U.obj F))))) hflat'
    _ = alpha.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj F) ≫
        TS.map (Prod.mkHom (eps.app P) (eps.app F)) ≫
          TS.map (Prod.mkHom (DerivedCategory.Q.map (U.map p)) (𝟙 _)) ≫
            (mS (U.obj A)).hom := by erw [hns]
    _ = alpha.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj F) ≫
        TS.map (Prod.mkHom (LF.map (DerivedCategory.Q.map p)) (𝟙 _)) ≫
          TS.map (Prod.mkHom (eps.app A) (eps.app F)) ≫ (mS (U.obj A)).hom := by
      rw [← TS.map_comp_assoc, ← TS.map_comp_assoc]
      congr 2
      congr 1
      ext
      · exact hne.symm
      · simp
    _ = _ := by rw [reassoc_of% hna]

end SheafOfModules
