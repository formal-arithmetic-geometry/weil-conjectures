/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.Paper.ProjectionFormulaArrows
import Sheaf.Paper.ProjectionFormulaFiniteFree
import Sheaf.Paper.ProjectionFormulaInverseNaturality

/-!
# Finite-projective summand equations

Source: Weil conjectures blueprint, proper base change, lemma 1266
(blueprint: lemma-weil-pbc-projection-formula-projective-summand).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

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

private theorem projectionMate_naturality
    {A B : Type*} [Category A] [Category B]
    (L : A ⥤ B) (V : B ⥤ A) (a : L ⊣ V)
    (T : A × A ⥤ A) (U : B × B ⥤ B)
    (alpha : T ⋙ L ≅ (L.prod L) ⋙ U) (E : B)
    {X Y : A} (f : X ⟶ Y) :
    T.map (CategoryTheory.Prod.mkHom (𝟙 (V.obj E)) f) ≫
        derivedProjectionFormulaMate L V a T U alpha E Y =
      derivedProjectionFormulaMate L V a T U alpha E X ≫
        V.map (U.map (CategoryTheory.Prod.mkHom (𝟙 E) (L.map f))) := by
  exact ((a.rightAdjointProjectionMap (T_C := Functor.curry.obj U)
    (T_D := Functor.curry.obj T) (Functor.curry.map alpha.hom ≫ (Functor.curryObjProdComp L L
      U).hom)).app E).naturality f

private theorem inverseEquations_of_retract
    {A B : Type*} [Category A] [Category B] (T U : A ⥤ B)
    {X Y : A} (i : X ⟶ Y) (p : Y ⟶ X) (hi : i ≫ p = 𝟙 X)
    (f : T.obj X ⟶ U.obj X) (g : U.obj X ⟶ T.obj X)
    (f' : T.obj Y ⟶ U.obj Y) (g' : U.obj Y ⟶ T.obj Y)
    (hfi : T.map i ≫ f' = f ≫ U.map i)
    (hfp : T.map p ≫ f = f' ≫ U.map p)
    (hgi : U.map i ≫ g' = g ≫ T.map i)
    (hgp : U.map p ≫ g = g' ≫ T.map p)
    (hfg : f' ≫ g' = 𝟙 _) (hgf : g' ≫ f' = 𝟙 _) :
    g ≫ f = 𝟙 _ ∧ f ≫ g = 𝟙 _ := by
  have hT : T.map i ≫ T.map p = 𝟙 _ := by rw [← T.map_comp, hi, T.map_id]
  have hU : U.map i ≫ U.map p = 𝟙 _ := by rw [← U.map_comp, hi, U.map_id]
  constructor
  · calc
      g ≫ f = g ≫ T.map i ≫ T.map p ≫ f := by simp [← Category.assoc, hT]
      _ = U.map i ≫ g' ≫ f' ≫ U.map p := by
        rw [hfp, ← Category.assoc g (T.map i), ← hgi]
        simp [Category.assoc]
      _ = 𝟙 _ := by rw [← Category.assoc g' f', hgf]; simpa using hU
  · calc
      f ≫ g = f ≫ U.map i ≫ U.map p ≫ g := by simp [← Category.assoc, hU]
      _ = T.map i ≫ f' ≫ g' ≫ T.map p := by
        rw [hgp, ← Category.assoc f (U.map i), ← hfi]
        simp [Category.assoc]
      _ = 𝟙 _ := by rw [← Category.assoc f' g', hfg]; simpa using hT

private noncomputable def singleFreePackage
    (N : ℕ) : StrictPerfectCoefficientPackage
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (∏ᶜ fun _ : Fin N ↦ SheafOfModules.unit
          ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) where
  N _ := N
  i r := if h : r = 0 then
    (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 _ r h).hom else 0
  p r := if h : r = 0 then
    (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 _ r h).inv else 0
  splitting r := by
    split_ifs with h
    · simp
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ r h).eq_of_src
        _ _

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

/-- The two summand arrows are inverse and independent of the finite-free presentation.
Source: proper base change, lemma 1266
(blueprint: lemma-weil-pbc-projection-formula-projective-summand).
Proof: write A(X)=Rh_*E tensor X and B(X)=Rh_*(E tensor Lh^*X).
Naturality of the canonical tensor comparison gives naturality of its counit
composite. Transport through the derived adjunction to obtain
B(i) pi_M = pi_N A(i) and B(p) pi_N = pi_M A(p)
(def-weil-pbc-projection-formula-arrows;
lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
Insert these identities into rho_M=A(p) rho_N B(i). The finite-free inverse
identities (lemma-weil-pbc-projection-formula-finite-free), followed by i then p
being the identity, give both inverse equations. The forward arrow is intrinsic:
its defining adjunct uses no splitting. Repeat the inverse calculation for any
second package. Uniqueness of the inverse of the same forward arrow gives equality
of the inverse arrows, hence equality of the ordered pairs. In degree zero the
finite total is the single-term formula of definition 1264, including rank zero. -/
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
  classical
  let single := HomologicalComplex.single
    (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (ComplexShape.up ℤ) 0
  let q := single ⋙ DerivedCategory.Q
  let A := q ⋙ (Functor.curry.obj TR).obj (RF.obj E)
  let B := q ⋙ LF ⋙ (Functor.curry.obj TS).obj E ⋙ RF
  let Free := ∏ᶜ fun _ : Fin (P.N 0) ↦ SheafOfModules.unit
    ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
  let Pfree := singleFreePackage (R := R) (P.N 0)
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M
  let i : M ⟶ Free := e.inv ≫ P.i 0
  let p : Free ⟶ M := P.p 0 ≫ e.hom
  have hip : i ≫ p = 𝟙 M := by
    change (e.inv ≫ P.i 0) ≫ (P.p 0 ≫ e.hom) = _
    rw [Category.assoc, ← Category.assoc (P.i 0), P.splitting]
    simp
  let hb : ∀ X, ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r →
      IsZero ((single.obj X).X r) := fun X ↦
    ⟨0, 0, fun r h ↦ HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 X r
      (h.elim ne_of_lt ne_of_gt)⟩
  let arrows := ringedProjectionFormulaArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF PR
    PS hPR hPS TR TS rR rS k V am RF eta hRF
      computeR computeL adjD canonicalAdj E K hK repE
  let f := (arrows (single.obj M) P (hb M)).1
  let g := (arrows (single.obj M) P (hb M)).2
  let f' := (arrows (single.obj Free) Pfree (hb Free)).1
  let g' := (arrows (single.obj Free) Pfree (hb Free)).2
  have hn (X Y) (a : X ⟶ Y)
      (PX : StrictPerfectCoefficientPackage _ (single.obj X))
      (PY : StrictPerfectCoefficientPackage _ (single.obj Y)) :
      B.map a ≫ (arrows (single.obj Y) PY (hb Y)).2 =
        (arrows (single.obj X) PX (hb X)).2 ≫ A.map a := by
    exact ringedProjectionFormulaInverse_naturality uInv uPush adj I c uStar hobj hmap LF epsilon
      hLF PR PS hPR hPS TR TS rR rS k V am RF eta hRF
      computeR computeL adjD canonicalAdj E K hK repE
      (single.obj X) (single.obj Y) PX PY (hb X) (hb Y) (single.map a)
  have hfree : f' ≫ g' = 𝟙 _ ∧ g' ≫ f' = 𝟙 _ :=
    ringedProjectionFormula_finiteFree uInv uPush adj I c uStar hobj hmap LF epsilon hLF PR PS hPR
      hPS TR TS rR rS k V am RF eta hRF
      computeR computeL adjD canonicalAdj E K hK repE
      (single.obj Free) Pfree (hb Free) (P.N 0) 0 rfl
  have heqs : g ≫ f = 𝟙 _ ∧ f ≫ g = 𝟙 _ :=
    inverseEquations_of_retract A B i p hip f g f' g'
      (projectionMate_naturality LF RF adjD TR TS _ E (q.map i))
      (projectionMate_naturality LF RF adjD TR TS _ E (q.map p))
      (hn M Free i P Pfree) (hn Free M p Pfree P) hfree.1 hfree.2
  exact ⟨heqs.1, heqs.2, rfl⟩


end SheafOfModules
