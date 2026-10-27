/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.CategoryTheory.StrictRoosComparison
import Sheaf.CategoryTheory.StrictRoosShiftLocalization
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Integer shifts of the normalized strict Roos comparison

Source: Stacks Project, Tag 0941, lemma-derived-limit-is-ok; Tag 014E,
definition-cone; Tag 011G, definition-shift-cochain, with the signed refinement
(blueprint: lem-a1-normalized-roos-shift-comparison).

The cone, inclusion and descent unit are the existing `roosF`, `roosι` and
`roosDerivedUnit`. The unit equation specifies precisely the normalized comparison
of `strictRoosComparison`. Natural index `n` denotes positive tower index `n+1`.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe uC vC t w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

section

variable {A : Type*} [Category* A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]

private noncomputable def limitModelCone (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    Cone I.asFunctor where
  pt := (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) |>.obj I
  π :=
    { app := fun n ↦ (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).app I
      naturality := by
        intro n m f
        ext q
        change 𝟙 (limit (I.X q)) ≫ limit.π (I.X q) m =
          limit.π (I.X q) n ≫ (I.X q).map f
        rw [Category.id_comp, limit.w] }

private noncomputable def limitModelLimit (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    IsLimit (limitModelCone I) := by
  apply HomologicalComplex.isLimitOfEval
  intro q
  exact limit.isLimit (I.X q)

private noncomputable def limitModelPointIso (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj I ≅
      limit I.asFunctor :=
  (limitModelLimit I).conePointUniqueUpToIso (limit.isLimit I.asFunctor)

private noncomputable def limitModelIso :
    (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) ≅
      roosLimitFunctor :=
  NatIso.ofComponents limitModelPointIso (by
    intro X Y f
    change (lim.mapHomologicalComplex (.up ℤ)).map f ≫ (limitModelPointIso Y).hom =
      (limitModelPointIso X).hom ≫ lim.map
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f)
    apply limit.hom_ext
    intro n
    dsimp only [limitModelPointIso]
    erw [Category.assoc,
      IsLimit.conePointUniqueUpToIso_hom_comp (limitModelLimit Y)
        (limit.isLimit Y.asFunctor) n, lim_map, Category.assoc, limMap_π]
    erw [← Category.assoc,
      IsLimit.conePointUniqueUpToIso_hom_comp (limitModelLimit X)
        (limit.isLimit X.asFunctor) n]
    exact (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).naturality f)

end

private theorem derivedLimitUnitIso
    {A : Type uC} [Category.{vC} A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    (L RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (η₀ : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ L)
    (η : roosLimitFunctor (A := A) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ RF)
    (hL : L.IsRightDerivedFunctor η₀
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)))
    (_hRF : RF.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)))
    (hη₀ : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ), I.IsKInjective → IsIso (η₀.app I))
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] : IsIso (η.app I) := by
  classical
  let QT := DerivedCategory.Q.{w} (C := ℕᵒᵖ ⥤ A)
  let QA := DerivedCategory.Q.{w} (C := A)
  let := hL
  let := _hRF
  let e := Functor.isoWhiskerRight (limitModelIso (A := A)) QA
  let δ := L.rightDerivedNatIso RF (L := QT) η₀ η
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) e
  have he := L.rightDerivedNatTrans_app RF (L := QT) η₀ η
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) e.hom I
  have := hη₀ I inferInstance
  have heq : η.app I = e.inv.app I ≫ η₀.app I ≫ δ.hom.app (QT.obj I) := by
    have he' := congrArg (fun z ↦ e.inv.app I ≫ z) he
    simpa only [δ, Functor.rightDerivedNatIso_hom, Iso.inv_hom_id_app_assoc] using he'.symm
  exact heq.symm ▸ (inferInstance : IsIso
    (e.inv.app I ≫ η₀.app I ≫ δ.hom.app (QT.obj I)))

section FastAbelian

variable {A : Type uC} [Category.{vC} A] [Preadditive A]
  [IsNormalMonoCategory A] [IsNormalEpiCategory A]
  [HasFiniteProducts A] [HasKernels A] [HasCokernels A]

private local instance assembledAbelian : Abelian A where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := inferInstance
  toIsNormalEpiCategory := inferInstance
  has_finite_products := inferInstance
  has_kernels := inferInstance
  has_cokernels := inferInstance

private theorem normalizedRoosShiftAssembly
    [HasCountableProducts A] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    (RF CF : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤
      DerivedCategory.{w} (A))
    (η : roosLimitFunctor (A := A) ⋙
      DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ RF)
    (_hRF : RF.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)))
    (hηiso : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective], IsIso (η.app I))
    (κ : roosF (A := A) ⋙
      DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙ CF)
    (ρ : CF ≅ RF)
    (_hnorm : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      DerivedCategory.Q.{w}.map (roosι X) ≫ κ.hom.app X ≫
        ρ.hom.app (DerivedCategory.Q.{w}.obj X) = η.app X) :
    ∃ (cC : (roosF (A := A)).CommShift ℤ)
      (cD : CF.CommShift ℤ) (cR : RF.CommShift ℤ)
      (cL : (roosLimitFunctor (A := A)).CommShift ℤ),
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
        (r q : ℤ) (n : ℕ),
        (((Functor.commShiftIso roosF (self := cC) r).hom.app X).f q ≫
            (CochainComplex.shiftFunctorObjXIso (roosF.obj X) r q (q + r) rfl).hom ≫
            (roosProj X).f (q + r) ≫
            (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f (q + r) =
          (roosProj (X⟦r⟧)).f q ≫
            (Pi.π (fun k : ℕ ↦ (X⟦r⟧).asFunctor.obj (op k)) n).f q ≫
            ((CochainComplex.shiftFunctorObjXIso X r q (q + r) rfl).hom).app (op n)) ∧
        (((Functor.commShiftIso roosF (self := cC) r).hom.app X).f q ≫
            (CochainComplex.shiftFunctorObjXIso (roosF.obj X) r q (q + r) rfl).hom ≫
            (CochainComplex.mappingCocone.snd (roosU X)).v
              (q + r) ((q - 1) + r) (by omega) ≫
            (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f ((q - 1) + r) =
          r.negOnePow • ((CochainComplex.mappingCocone.snd (roosU (X⟦r⟧))).v
              q (q - 1) (by omega) ≫
            (Pi.π (fun k : ℕ ↦ (X⟦r⟧).asFunctor.obj (op k)) n).f (q - 1) ≫
            ((CochainComplex.shiftFunctorObjXIso X r (q - 1) ((q - 1) + r) rfl).hom).app
              (op n)))) ∧
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r : ℤ),
        DerivedCategory.Q.{w}.map ((Functor.commShiftIso roosF (self := cC) r).hom.app X) ≫
            (DerivedCategory.Q.{w}.commShiftIso r).hom.app (roosF.obj X) ≫
            (κ.hom.app X)⟦r⟧' =
          κ.hom.app (X⟦r⟧) ≫ CF.map ((DerivedCategory.Q.{w}.commShiftIso r).hom.app X) ≫
            (Functor.commShiftIso CF (self := cD) r).hom.app (DerivedCategory.Q.{w}.obj X)) ∧
      (∀ (N : DerivedCategory.{w} (ℕᵒᵖ ⥤ A)) (r : ℤ),
        ρ.hom.app (N⟦r⟧) ≫ (Functor.commShiftIso RF (self := cR) r).hom.app N =
          (Functor.commShiftIso CF (self := cD) r).hom.app N ≫ (ρ.hom.app N)⟦r⟧') ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
        (r q : ℤ) (n : ℕ),
        ((Functor.commShiftIso roosLimitFunctor (self := cL) r).hom.app I).f q ≫
            (CochainComplex.shiftFunctorObjXIso (limit I.asFunctor) r q (q + r) rfl).hom ≫
            (limit.π I.asFunctor (op n)).f (q + r) =
          (limit.π (I⟦r⟧).asFunctor (op n)).f q ≫
            ((CochainComplex.shiftFunctorObjXIso I r q (q + r) rfl).hom).app (op n)) ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
        [I.IsKInjective] (r : ℤ),
        roosι (I⟦r⟧) ≫ (Functor.commShiftIso roosF (self := cC) r).hom.app I =
          (Functor.commShiftIso roosLimitFunctor (self := cL) r).hom.app I ≫ (roosι I)⟦r⟧') ∧
      (∀ (X I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
        (q : X ⟶ I) [QuasiIso q] [I.IsKInjective] (r : ℤ),
        ∃ (d : DerivedCategory.Q.{w}.obj (limit I.asFunctor) ≅
            RF.obj (DerivedCategory.Q.{w}.obj X))
          (ds : DerivedCategory.Q.{w}.obj (limit (I⟦r⟧).asFunctor) ≅
            RF.obj (DerivedCategory.Q.{w}.obj (X⟦r⟧))),
          d.hom ≫ RF.map (DerivedCategory.Q.{w}.map q) = η.app I ∧
          ds.hom ≫ RF.map (DerivedCategory.Q.{w}.map (q⟦r⟧')) = η.app (I⟦r⟧) ∧
          ds.hom ≫ RF.map ((DerivedCategory.Q.{w}.commShiftIso r).hom.app X) ≫
              (Functor.commShiftIso RF (self := cR) r).hom.app (DerivedCategory.Q.{w}.obj X) =
            DerivedCategory.Q.{w}.map
                ((Functor.commShiftIso roosLimitFunctor (self := cL) r).hom.app I) ≫
              (DerivedCategory.Q.{w}.commShiftIso r).hom.app (limit I.asFunctor) ≫ d.hom⟦r⟧') := by
  classical
  let QT := DerivedCategory.Q.{w} (C := ℕᵒᵖ ⥤ A)
  let QA := DerivedCategory.Q.{w} (C := A)
  have h := strictRoosShiftLocalization (A := A) QT QA CF κ
  rcases h with ⟨cC, cL, hcoord, _, hlim, hinc, cD, ⟨hdesc, hloc⟩, _⟩
  let := cD
  let cR := Functor.CommShift.ofIso ρ ℤ
  have hsquare (N : DerivedCategory.{w} (ℕᵒᵖ ⥤ A)) (r : ℤ) :
      ρ.hom.app (N⟦r⟧) ≫ (Functor.commShiftIso RF (self := cR) r).hom.app N =
        (Functor.commShiftIso CF (self := cD) r).hom.app N ≫ (ρ.hom.app N)⟦r⟧' := by
    simp [cR, Functor.CommShift.ofIso_commShiftIso_hom_app]
  have hηshift (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r : ℤ) :
      η.app (I⟦r⟧) ≫ RF.map ((QT.commShiftIso r).hom.app I) ≫
          (Functor.commShiftIso RF (self := cR) r).hom.app (QT.obj I) =
        QA.map ((Functor.commShiftIso roosLimitFunctor (self := cL) r).hom.app I) ≫
          (QA.commShiftIso r).hom.app (limit I.asFunctor) ≫ (η.app I)⟦r⟧' := by
    let u := (QT.commShiftIso r).hom.app I
    let v := (Functor.commShiftIso RF (self := cR) r).hom.app (QT.obj I)
    have hn : ρ.hom.app (QT.obj (I⟦r⟧)) ≫ RF.map u =
        CF.map u ≫ ρ.hom.app ((QT.obj I)⟦r⟧) :=
      (ρ.hom.naturality u).symm
    have hn' := congrArg (fun z ↦ z ≫ v) hn
    have hs := congrArg (fun z ↦ CF.map u ≫ z) (hsquare (QT.obj I) r)
    have hc : ρ.hom.app (QT.obj (I⟦r⟧)) ≫ RF.map u ≫ v =
        CF.map u ≫ (Functor.commShiftIso CF (self := cD) r).hom.app (QT.obj I) ≫
          (ρ.hom.app (QT.obj I))⟦r⟧' := by
      exact (Category.assoc _ _ _).symm.trans
        (hn'.trans ((Category.assoc _ _ _).trans hs))
    have hh := congrArg (fun z ↦ QA.map (roosι (I⟦r⟧)) ≫ κ.hom.app (I⟦r⟧) ≫ z) hc
    have hl := congrArg (fun z ↦ z ≫ (ρ.hom.app (QT.obj I))⟦r⟧') (hloc I r)
    simp only [Functor.map_comp, Category.assoc] at hh hl
    have hleft := congrArg (fun z ↦ z ≫ RF.map u ≫ v) (_hnorm (I⟦r⟧))
    have hright := congrArg (fun z ↦
      QA.map ((Functor.commShiftIso roosLimitFunctor (self := cL) r).hom.app I) ≫
        (QA.commShiftIso r).hom.app (limit I.asFunctor) ≫ z⟦r⟧') (_hnorm I)
    simp only [Functor.map_comp, Category.assoc] at hleft hright
    dsimp only [QT, QA, roosLimitFunctor, Functor.comp_obj,
      HomologicalComplex.complexOfFunctorsToFunctorToComplex_obj] at hleft hh hl hright ⊢
    set_option backward.isDefEq.respectTransparency false in
      simp only [Category.assoc] at hl
    set_option backward.isDefEq.respectTransparency true in
      exact hleft.symm.trans (hh.trans (hl.trans hright))
  dsimp only [QT, QA] at hcoord hdesc hsquare hlim hinc hηshift hηiso
  refine ⟨cC, cD, cR, cL, ?_⟩
  refine And.intro ?_ ?_
  · intro X r q n
    with_reducible exact hcoord X r q n
  refine And.intro ?_ ?_
  · intro X r
    with_reducible exact hdesc X r
  refine And.intro ?_ ?_
  · intro N r
    with_reducible exact hsquare N r
  refine And.intro ?_ ?_
  · intro I r q n
    set_option backward.isDefEq.respectTransparency true in
      with_reducible exact hlim I r q n
  constructor
  · intro I _ r
    set_option backward.isDefEq.respectTransparency true in
      with_reducible exact hinc I r
  · intro X I q _ _ r
    have := hηiso I
    have := hηiso (I⟦r⟧)
    let d₀ := asIso (η.app I)
    let ds₀ := asIso (η.app (I⟦r⟧))
    dsimp only [roosLimitFunctor, Functor.comp_obj,
      HomologicalComplex.complexOfFunctorsToFunctorToComplex_obj] at d₀ ds₀
    let d := d₀ ≪≫ (RF.mapIso (asIso (QT.map q))).symm
    let ds := ds₀ ≪≫
      (RF.mapIso (asIso (QT.map (q⟦r⟧')))).symm
    have hd : d.hom ≫ RF.map (QT.map q) = η.app I := by simp [d, d₀]
    have hds : ds.hom ≫ RF.map (QT.map (q⟦r⟧')) = η.app (I⟦r⟧) := by simp [ds, ds₀]
    refine ⟨d, ds, hd, hds, ?_⟩
    apply (cancel_mono ((RF.map (QT.map q))⟦r⟧')).1
    have hn := (Functor.commShiftIso RF (self := cR) r).hom.naturality (QT.map q)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    have hq := (QT.commShiftIso r).hom.naturality q
    dsimp only [Functor.comp_map, Functor.comp_obj] at hq
    have ht := congrArg RF.map hq
    simp only [Functor.map_comp] at ht
    have e₁ := congrArg (fun z ↦ ds.hom ≫
      RF.map ((QT.commShiftIso r).hom.app X) ≫ z) hn.symm
    have e₂ := congrArg (fun z ↦ ds.hom ≫ z ≫
      (Functor.commShiftIso RF (self := cR) r).hom.app (QT.obj I)) ht.symm
    have e₃ := congrArg (fun z ↦ z ≫ RF.map ((QT.commShiftIso r).hom.app I) ≫
      (Functor.commShiftIso RF (self := cR) r).hom.app (QT.obj I)) hds
    dsimp only [QT, QA, roosLimitFunctor, Functor.comp_obj,
      HomologicalComplex.complexOfFunctorsToFunctorToComplex_obj] at hd hds hηshift ⊢
    have e₄ := congrArg (fun z ↦
      QA.map ((Functor.commShiftIso roosLimitFunctor (self := cL) r).hom.app I) ≫
        (QA.commShiftIso r).hom.app (limit I.asFunctor) ≫ z⟦r⟧') hd
    simp only [Functor.map_comp, Category.assoc] at e₁ e₂ e₃ e₄
    dsimp only [QT, QA, roosLimitFunctor, Functor.comp_obj,
      HomologicalComplex.complexOfFunctorsToFunctorToComplex_obj] at e₄ hηshift ⊢
    simp only [Category.assoc]
    exact e₁.trans (e₂.trans (e₃.trans ((hηshift I r).trans e₄.symm)))

end FastAbelian

set_option backward.isDefEq.respectTransparency.types true in
/-- The normalized Roos comparison respects the signed, coherent integer shifts.
The first two component equations say `(y,x) ↦ ((-1)^r y,x)` after the canonical
termwise identifications. The descent equation identifies that chain shift with
`cD`; the next equation is the requested square for every derived tower object.
The limit projection equation fixes `cL` to the termwise inverse-limit shift.
The inclusion equation preserves `(0,z)`. The final clause computes `cR` using
EVERY K-injective resolution, including those without injective terms: `d` and `ds`
are fixed by the derived unit and the resolution maps, so the formula is independent
of all resolution choices. Each `CommShift ℤ` includes naturality and the zero and
addition coherence laws. In particular natural strict comparisons commuting with
termwise shifts can be composed with this square.

Source: Stacks Project, Tag 0941, lemma-derived-limit-is-ok, shifted K-injective
proof; Tags 014E and 011G, signed cone and shift conventions
(blueprint: lem-a1-normalized-roos-shift-comparison).

Proof plan, following the seven steps of the node:
1. Write h=1-s and a=(-1)^r. The two differentials are (-a dy-hx,a dx)
   and (-a dy-a hx,a dx). The diagonal map (ay,x) intertwines them since a²=1;
   its inverse has the same coordinate formula (def-weil-strict-roos-model).
2. Strict maps act diagonally, hence commute with this sign. Signs multiply under
   addition of shifts and the zero sign is 1 (def-weil-abstract-derived-category).
3. Choose an injective-term K-injective tower resolution using
   lem-pur-injective-tower-roos-shifts. Shifting preserves K-injectivity by
   lem-weil-pbc-kinjective-shift; limit shift is identity on compatible tuples.
4. The normalized inclusion is (0,z), so the signed map preserves it. Apply the
   resolution formula of lem-weil-strict-roos-comparison to the same shifted resolution.
5. Invert that inclusion identity, and use strict naturality for the resolution map.
   Substitution yields sigmaLim rhoShift = rhoShifted sigmaCone, with these exact maps.
6. Localization extends strict naturality to every derived morphism. For another
   K-injective resolution, lem-weil-pbc-kinjective-hom-derived represents its comparison
   by a homotopy equivalence. Limit preserves its homotopies and its termwise shift
   square, proving the same computation for every resolution, without injective terms.
7. Conjugate the coherent cone shifts by rho. Cancellation gives zero and addition
   coherence on derived limits. Naturality composes the square with any natural strict
   tower comparison commuting with termwise shifts. -/
theorem normalizedRoosShiftComparison
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max uC vC t}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC t}]
    (R : Sheaf J RingCat.{max uC vC t})
    (_hcomm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    [HasDerivedCategory.{w} (ringedSiteModules.{max uC vC t} R)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC t} R)]
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{max uC vC t} R)]
    (RF CF : DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC t} R) ⥤
      DerivedCategory.{w} (ringedSiteModules.{max uC vC t} R))
    (η : roosLimitFunctor (A := ringedSiteModules.{max uC vC t} R) ⋙
      DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ RF)
    (_hRF : RF.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC t} R) (.up ℤ)))
    (κ : roosF (A := ringedSiteModules.{max uC vC t} R) ⋙
      DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙ CF)
    (ρ : CF ≅ RF)
    (_hnorm : ∀ X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC t} R) ℤ,
      DerivedCategory.Q.{w}.map (roosι X) ≫ κ.hom.app X ≫
        ρ.hom.app (DerivedCategory.Q.{w}.obj X) = η.app X) :
    ∃ (cC : (roosF (A := ringedSiteModules.{max uC vC t} R)).CommShift ℤ)
      (cD : CF.CommShift ℤ) (cR : RF.CommShift ℤ)
      (cL : (roosLimitFunctor (A := ringedSiteModules.{max uC vC t} R)).CommShift ℤ),
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC t} R) ℤ)
        (r q : ℤ) (n : ℕ),
        (((Functor.commShiftIso roosF (self := cC) r).hom.app X).f q ≫
            (CochainComplex.shiftFunctorObjXIso (roosF.obj X) r q (q + r) rfl).hom ≫
            (roosProj X).f (q + r) ≫
            (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f (q + r) =
          (roosProj (X⟦r⟧)).f q ≫
            (Pi.π (fun k : ℕ ↦ (X⟦r⟧).asFunctor.obj (op k)) n).f q ≫
            ((CochainComplex.shiftFunctorObjXIso X r q (q + r) rfl).hom).app (op n)) ∧
        (((Functor.commShiftIso roosF (self := cC) r).hom.app X).f q ≫
            (CochainComplex.shiftFunctorObjXIso (roosF.obj X) r q (q + r) rfl).hom ≫
            (CochainComplex.mappingCocone.snd (roosU X)).v
              (q + r) ((q - 1) + r) (by omega) ≫
            (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f ((q - 1) + r) =
          r.negOnePow • ((CochainComplex.mappingCocone.snd (roosU (X⟦r⟧))).v
              q (q - 1) (by omega) ≫
            (Pi.π (fun k : ℕ ↦ (X⟦r⟧).asFunctor.obj (op k)) n).f (q - 1) ≫
            ((CochainComplex.shiftFunctorObjXIso X r (q - 1) ((q - 1) + r) rfl).hom).app
              (op n)))) ∧
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC t} R) ℤ) (r : ℤ),
        DerivedCategory.Q.{w}.map ((Functor.commShiftIso roosF (self := cC) r).hom.app X) ≫
            (DerivedCategory.Q.{w}.commShiftIso r).hom.app (roosF.obj X) ≫
            (κ.hom.app X)⟦r⟧' =
          κ.hom.app (X⟦r⟧) ≫ CF.map ((DerivedCategory.Q.{w}.commShiftIso r).hom.app X) ≫
            (Functor.commShiftIso CF (self := cD) r).hom.app (DerivedCategory.Q.{w}.obj X)) ∧
      (∀ (N : DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC t} R)) (r : ℤ),
        ρ.hom.app (N⟦r⟧) ≫ (Functor.commShiftIso RF (self := cR) r).hom.app N =
          (Functor.commShiftIso CF (self := cD) r).hom.app N ≫ (ρ.hom.app N)⟦r⟧') ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC t} R) ℤ)
        (r q : ℤ) (n : ℕ),
        ((Functor.commShiftIso roosLimitFunctor (self := cL) r).hom.app I).f q ≫
            (CochainComplex.shiftFunctorObjXIso (limit I.asFunctor) r q (q + r) rfl).hom ≫
            (limit.π I.asFunctor (op n)).f (q + r) =
          (limit.π (I⟦r⟧).asFunctor (op n)).f q ≫
            ((CochainComplex.shiftFunctorObjXIso I r q (q + r) rfl).hom).app (op n)) ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC t} R) ℤ)
        [I.IsKInjective] (r : ℤ),
        roosι (I⟦r⟧) ≫ (Functor.commShiftIso roosF (self := cC) r).hom.app I =
          (Functor.commShiftIso roosLimitFunctor (self := cL) r).hom.app I ≫ (roosι I)⟦r⟧') ∧
      (∀ (X I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC t} R) ℤ)
        (q : X ⟶ I) [QuasiIso q] [I.IsKInjective] (r : ℤ),
        ∃ (d : DerivedCategory.Q.{w}.obj (limit I.asFunctor) ≅
            RF.obj (DerivedCategory.Q.{w}.obj X))
          (ds : DerivedCategory.Q.{w}.obj (limit (I⟦r⟧).asFunctor) ≅
            RF.obj (DerivedCategory.Q.{w}.obj (X⟦r⟧))),
          d.hom ≫ RF.map (DerivedCategory.Q.{w}.map q) = η.app I ∧
          ds.hom ≫ RF.map (DerivedCategory.Q.{w}.map (q⟦r⟧')) = η.app (I⟦r⟧) ∧
          ds.hom ≫ RF.map ((DerivedCategory.Q.{w}.commShiftIso r).hom.app X) ≫
              (Functor.commShiftIso RF (self := cR) r).hom.app (DerivedCategory.Q.{w}.obj X) =
            DerivedCategory.Q.{w}.map
                ((Functor.commShiftIso roosLimitFunctor (self := cL) r).hom.app I) ≫
              (DerivedCategory.Q.{w}.commShiftIso r).hom.app (limit I.asFunctor) ≫ d.hom⟦r⟧') := by
  classical
  let A := ringedSiteModules.{max uC vC t} R
  let QT := DerivedCategory.Q.{w} (C := ℕᵒᵖ ⥤ A)
  let QA := DerivedCategory.Q.{w} (C := A)
  have hηiso (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] :
      IsIso (η.app I) := by
    have hdata := ringedStrictTowerHomotopyLimitIndependentCoefficients.{w, uC, vC, max uC vC t}
        J R _hcomm
    rcases hdata with ⟨L, η₀, hL, hη₀, _⟩
    exact derivedLimitUnitIso L RF η₀ η hL _hRF hη₀ I
  have h := normalizedRoosShiftAssembly (A := A) RF CF η _hRF hηiso κ ρ _hnorm
  dsimp only [A] at h
  set_option backward.isDefEq.respectTransparency true in
    with_reducible exact h

end CategoryTheory
