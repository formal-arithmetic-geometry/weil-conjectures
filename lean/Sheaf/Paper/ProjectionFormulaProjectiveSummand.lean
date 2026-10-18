/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.Paper.ProjectionFormulaArrows
public import Sheaf.Algebra.Homology.CochainTensorHasMapBifunctor
import Sheaf.Paper.ProjectionFormulaFiniteFree
import Sheaf.Paper.ProjectionFormulaCoefficientNaturality

/-!
# Finite-projective summand equations

Source: Weil conjectures blueprint, proper base change, lemma 1266
(blueprint: lemma-weil-pbc-projection-formula-projective-summand).
-/

@[expose] public section



universe u v u' v' w

open CategoryTheory CategoryTheory.Limits

attribute [local instance] CategoryTheory.cochainTensorHasMapBifunctor

set_option backward.isDefEq.respectTransparency true

namespace CategoryTheory

open MonoidalCategory

private theorem map_retract
    {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B]
    (T : A ⥤ B) {X Y : A} (i : X ⟶ Y) (p : Y ⟶ X) (h : i ≫ p = 𝟙 X) :
    T.map i ≫ T.map p = 𝟙 (T.obj X) := by
  rw [← T.map_comp, h, T.map_id]

private theorem conjugate_retract
    {A : Type u} [Category.{v} A] {X Y Z : A}
    (e : X ≅ Y) (i : Y ⟶ Z) (p : Z ⟶ Y) (h : i ≫ p = 𝟙 Y) :
    (e.hom ≫ i) ≫ (p ≫ e.inv) = 𝟙 X := by
  rw [Category.assoc, ← Category.assoc i, h, Category.id_comp, e.hom_inv_id]

private theorem map_id_pair_retract
    {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B]
    {D : Type w} [Category D] (T : A × B ⥤ D) (X : A)
    {Y Z : B} (i : Y ⟶ Z) (p : Z ⟶ Y) (h : i ≫ p = 𝟙 Y) :
    T.map (CategoryTheory.Prod.mkHom (𝟙 X) i) ≫
      T.map (CategoryTheory.Prod.mkHom (𝟙 X) p) = 𝟙 _ := by
  rw [← T.map_comp, CategoryTheory.prod_comp, Category.id_comp, h,
    ← CategoryTheory.prod_id, T.map_id]

private theorem inverse_pair_of_retract
    {𝒞 : Type u} [Category.{v} 𝒞] {X Y X' Y' : 𝒞}
    (f : X ⟶ Y) (g : Y ⟶ X) (f' : X' ⟶ Y') (g' : Y' ⟶ X')
    (ai : X ⟶ X') (ap : X' ⟶ X) (bi : Y ⟶ Y') (bp : Y' ⟶ Y)
    (ha : ai ≫ ap = 𝟙 X) (hb : bi ≫ bp = 𝟙 Y)
    (hfi : ai ≫ f' = f ≫ bi) (hfp : ap ≫ f = f' ≫ bp)
    (hgi : bi ≫ g' = g ≫ ai) (hgp : bp ≫ g = g' ≫ ap)
    (hfg : f' ≫ g' = 𝟙 X') (hgf : g' ≫ f' = 𝟙 Y') :
    g ≫ f = 𝟙 Y ∧ f ≫ g = 𝟙 X := by
  constructor
  · calc
      g ≫ f = g ≫ (ai ≫ ap) ≫ f := by rw [ha, Category.id_comp]
      _ = bi ≫ g' ≫ ap ≫ f := by
        simp only [← Category.assoc]
        rw [← hgi]
      _ = bi ≫ g' ≫ f' ≫ bp := by rw [hfp]
      _ = 𝟙 Y := by rw [← Category.assoc g', hgf, Category.id_comp, hb]
  · calc
      f ≫ g = f ≫ (bi ≫ bp) ≫ g := by rw [hb, Category.id_comp]
      _ = ai ≫ f' ≫ bp ≫ g := by
        simp only [← Category.assoc]
        rw [← hfi]
      _ = ai ≫ f' ≫ g' ≫ ap := by rw [hgp]
      _ = 𝟙 X := by rw [← Category.assoc f', hfg, Category.id_comp, ha]

end CategoryTheory

namespace SheafOfModules

attribute [local irreducible] sheafCompose DerivedCategory



set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 2048


private noncomputable def singleFreePackage
    {C₀ : Type u} [Category.{u} C₀] {J₀ : GrothendieckTopology C₀}
    (R₀ : Sheaf J₀ RingCat.{u}) (N : ℕ) :
    StrictPerfectCoefficientPackage R₀
      ((HomologicalComplex.single (SheafOfModules.{u} R₀) (ComplexShape.up ℤ) 0).obj
        (∏ᶜ fun _ : Fin N ↦ SheafOfModules.unit R₀)) where
  N _ := N
  i r := if h : r = 0 then
    (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 _ r h).hom else 0
  p r := if h : r = 0 then
    (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 _ r h).inv else 0
  splitting r := by
    by_cases h : r = 0
    · simp only [dif_pos h, Iso.hom_inv_id]
    · simp only [dif_neg h, zero_comp]
      exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ r h).eq_of_src _ _

variable
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
    [V.Additive]
    (RF : DerivedCategory (SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S)) ⥤ DerivedCategory (SheafOfModules.{u} ((sheafCompose JC (forget₂
      CommRingCat.{u} RingCat.{u})).obj R)))
    (eta : V.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (hRF : ∀ G : DerivedCategory (SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S)) ⥤ DerivedCategory (SheafOfModules.{u} ((sheafCompose JC (forget₂
      CommRingCat.{u} RingCat.{u})).obj R)),
      Function.Bijective (fun b : RF ⟶ G ↦ eta ≫ Functor.whiskerLeft DerivedCategory.Qh b))
    (computeR : ∀ K : CochainComplex (SheafOfModules.{u} ((sheafCompose JD (forget₂
      CommRingCat.{u}
      RingCat.{u})).obj S)) ℤ, K.IsKInjective →
      IsIso (derivedPushforwardComplexComparison V RF eta K))
    (computeL : ∀ P : CochainComplex (SheafOfModules.{u} ((sheafCompose JC (forget₂
      CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ,
      P.IsAcyclicTensorKFlat → (∀ n : ℤ, (P.X n).IsFlat) →
        IsIso (derivedPullbackComplexComparison uStar LF epsilon P))
    (adjD : LF ⊣ RF)
    (canonicalAdj : ∀ K : CochainComplex (SheafOfModules.{u} ((sheafCompose JD (forget₂
      CommRingCat.{u} RingCat.{u})).obj S)) ℤ, K.IsKInjective →
      LF.map (derivedPushforwardComplexComparison V RF eta K) ≫
          adjD.counit.app (DerivedCategory.Q.obj K) =
        derivedPullbackComplexComparison uStar LF epsilon
          ((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
            DerivedCategory.Q.map ((am.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app K))
    (E : DerivedCategory (SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S))) (K : CochainComplex (SheafOfModules.{u} ((sheafCompose JD (forget₂
      CommRingCat.{u} RingCat.{u})).obj S)) ℤ) (hK : K.IsKInjective)
    (repE : E ≅ DerivedCategory.Q.obj K)

set_option hygiene false in
local notation "pairFamily" =>
  ringedProjectionFormulaArrows (C := C) (D := D) (JC := JC) (JD := JD)
    (R := R) (S := S) (RI := RI)
    uInv uPush adj I c uStar hobj hmap LF epsilon hLF
    PR PS hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj
    E K hK repE

set_option hygiene false in
local notation "Amap" f:arg => TR.map (CategoryTheory.Prod.mkHom (𝟙 (RF.obj E))
  ((DerivedCategory.Q (C := SheafOfModules.{u}
    ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))).map f))

set_option hygiene false in
local notation "Bmap" f:arg => RF.map (TS.map (CategoryTheory.Prod.mkHom (𝟙 E)
  (LF.map ((DerivedCategory.Q (C := SheafOfModules.{u}
    ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))).map f))))

attribute [local irreducible] ringedProjectionFormulaArrows

/-- The arrows of definition 1264 for one coefficient sheaf, placed in degree zero.
The package records the displayed finite-free splitting in degree zero; its other
terms are zero. This is a specialization of the existing arrows, with the canonical
bound [0,0], and introduces no new choice of a map or inverse.
Source: proper base change, lemma 1266 and definition 1264
(blueprint: lemma-weil-pbc-projection-formula-projective-summand). -/
noncomputable def ringedProjectionFormulaSummandArrows
    (M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (P : StrictPerfectCoefficientPackage ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R) ((HomologicalComplex.single (SheafOfModules.{u} ((sheafCompose JC
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (ComplexShape.up ℤ) 0).obj M)) :=
  ringedProjectionFormulaArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF PR PS hPR hPS TR
      TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj E K hK repE
    ((HomologicalComplex.single (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) (ComplexShape.up ℤ) 0).obj M) P
    ⟨0, 0, fun r h ↦ HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M r
      (h.elim ne_of_lt ne_of_gt)⟩

set_option maxHeartbeats 400000 in
-- Instantiate the ringed-site interface while keeping the arrow data opaque.
/-- The two summand arrows are inverse and independent of the finite-free presentation.
Source: proper base change, lemma 1266
(blueprint: lemma-weil-pbc-projection-formula-projective-summand).
Proof: place M and its displayed finite-free summand in degree zero. Transport
P.i 0 and P.p 0 through singleObjXSelf to obtain a genuine split pair of chain
maps i:F->G and p:G->F. The explicit finite-free coefficient package on G uses
the single-term isomorphism in degree zero and zero maps outside that degree.
The functors A(X)=Rh_*E tensor X and B(X)=Rh_*(E tensor Lh^*X) preserve this
splitting. Apply coefficient naturality to i and p, and apply the finite-free
inverse theorem to G with rank P.N 0 and shift zero. Inserting the splitting
identities between the two composites and using those naturality squares yields
both inverse identities; inverse_pair_of_retract gives the full calculation.
Finally apply coefficient naturality to the identity of F with packages P and P'.
Since A and B preserve identity, the two squares give componentwise equality of
the arrow pairs, and product extensionality proves presentation independence. -/
theorem ringedProjectionFormula_projective_summand
    (M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (P P' : StrictPerfectCoefficientPackage ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R) ((HomologicalComplex.single (SheafOfModules.{u} ((sheafCompose JC
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (ComplexShape.up ℤ) 0).obj M)) :
    (ringedProjectionFormulaSummandArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF PR PS
      hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj E K hK repE M P).2
      ≫
        (ringedProjectionFormulaSummandArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF PR
      PS hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj E K hK repE M
      P).1 = 𝟙 _ ∧
    (ringedProjectionFormulaSummandArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF PR PS
      hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj E K hK repE M P).1
      ≫
        (ringedProjectionFormulaSummandArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF PR
      PS hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj E K hK repE M
      P).2 = 𝟙 _ ∧
    ringedProjectionFormulaSummandArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF PR PS
      hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj E K hK repE M P =
      ringedProjectionFormulaSummandArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF PR PS
      hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj E K hK repE M P'
      := by
  let O := (sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  let single := HomologicalComplex.single (SheafOfModules.{u} O) (ComplexShape.up ℤ) 0
  let F := single.obj M
  let N := P.N 0
  let Free := ∏ᶜ fun _ : Fin N ↦ SheafOfModules.unit O
  let G := single.obj Free
  let Q := singleFreePackage O N
  have hb (X : SheafOfModules.{u} O) :
      ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero ((single.obj X).X r) :=
    ⟨0, 0, fun r h ↦ HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 X r
      (h.elim ne_of_lt ne_of_gt)⟩
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M
  let i : F ⟶ G := single.map (e.inv ≫ P.i 0)
  let p : G ⟶ F := single.map (P.p 0 ≫ e.hom)
  have hip : i ≫ p = 𝟙 F :=
    map_retract single _ _ (conjugate_retract e.symm (P.i 0) (P.p 0) (P.splitting 0))
  have hAi : Amap i ≫ Amap p = 𝟙 _ :=
    map_id_pair_retract TR (RF.obj E) _ _
      (map_retract (DerivedCategory.Q (C := SheafOfModules.{u} O)) i p hip)
  have hBi : Bmap i ≫ Bmap p = 𝟙 _ :=
    map_retract RF _ _ (map_id_pair_retract TS E _ _
      (map_retract LF _ _ (map_retract (DerivedCategory.Q (C := SheafOfModules.{u} O)) i p hip)))
  let naturality := ringedProjectionFormula_coefficient_naturality
    (C := C) (D := D) (JC := JC) (JD := JD) (R := R) (S := S) (RI := RI)
    uInv uPush adj I c uStar hobj hmap
    LF epsilon hLF PR PS hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL
    adjD canonicalAdj E K hK repE
  have hi := naturality F G P Q (hb M) (hb Free) i
  have hp := naturality G F Q P (hb Free) (hb M) p
  have hfree := ringedProjectionFormula_finiteFree
    (C := C) (D := D) (JC := JC) (JD := JD) (R := R) (S := S) (RI := RI)
    uInv uPush adj I c uStar hobj hmap
    LF epsilon hLF PR PS hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL
    adjD canonicalAdj E K hK repE G Q (hb Free) N 0 (by simp only [Int.neg_zero]; rfl)
  let pair := pairFamily
  let pF := pair F P (hb M)
  let pG := pair G Q (hb Free)
  have hinv := inverse_pair_of_retract pF.1 pF.2 pG.1 pG.2
    (Amap i) (Amap p) (Bmap i) (Bmap p) hAi hBi hi.1 hp.1 hi.2 hp.2
      hfree.1 hfree.2
  have hself := naturality F F P P' (hb M) (hb M) (𝟙 F)
  have hAid : Amap (𝟙 F) = 𝟙 _ := by
    rw [(DerivedCategory.Q (C := SheafOfModules.{u} O)).map_id,
      ← CategoryTheory.prod_id, TR.map_id]
  have hBid : Bmap (𝟙 F) = 𝟙 _ := by
    rw [(DerivedCategory.Q (C := SheafOfModules.{u} O)).map_id, LF.map_id,
      ← CategoryTheory.prod_id, TS.map_id, RF.map_id]
  simp only [hAid, hBid, Category.id_comp, Category.comp_id] at hself
  refine ⟨hinv.1, hinv.2, ?_⟩
  change pair F P (hb M) = pair F P' (hb M)
  exact Prod.ext hself.1.symm hself.2.symm

end SheafOfModules
