/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.RingedTopoiDerivedPullbackIndependent
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Sheaf.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients

/-! # Exact pullback and its resolving normalization

Source: Stacks Project, derived.tex, Tag 015F (dual), and sites-cohomology.tex,
Tags 06YS, 06YY and 0G7E (blueprint: lem-pur-exact-derived-resolving-identification).

The comparison is the one on the homotopy category from the recorded derived-pullback
interface. Its values on complexes use the canonical quotient functor. The exact
localization comparison is Mathlib's `mapDerivedCategoryFactorsh`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe uC vC uD vD r w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open WeilConjectures.SemilinearSections (Mod)

namespace SheafOfModules

private def sheafUliftIso
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    (A : Type uD) [Category.{vD} A] (U : A ⥤ Type w)
    [J.HasSheafCompose U] [J.HasSheafCompose (U ⋙ uliftFunctor.{w, w})] :
    sheafCompose J (U ⋙ uliftFunctor.{w, w}) ≅ sheafCompose J U :=
  NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun X ↦ uliftTrivial (U.obj (M.obj.obj X)))
      (by intros; rfl))) (by intros; rfl)

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  {R : Sheaf JC CommRingCat.{w}} {RI : Sheaf JD CommRingCat.{w}}
  {L : Sheaf JC (Type w) ⥤ Sheaf JD (Type w)}

set_option backward.isDefEq.respectTransparency false in
private noncomputable def inverseImageOfUniverses (I : AlgebraicInverseImage L R RI) :
    AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} L R RI := by
  let eR := sheafUliftIso JC CommRingCat.{w} (CategoryTheory.forget CommRingCat.{w})
  let eS := sheafUliftIso JD CommRingCat.{w} (CategoryTheory.forget CommRingCat.{w})
  let eM := isoWhiskerLeft (toSheaf ((sheafCompose JC
    (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) <|
    sheafUliftIso JC AddCommGrpCat.{w} (CategoryTheory.forget AddCommGrpCat.{w})
  let eN := isoWhiskerLeft (toSheaf ((sheafCompose JD
    (forget₂ CommRingCat.{w} RingCat.{w})).obj RI)) <|
    sheafUliftIso JD AddCommGrpCat.{w} (CategoryTheory.forget AddCommGrpCat.{w})
  let er := L.mapIso (eR.app R) ≪≫ I.ringUnderlying ≪≫ (eS.app RI).symm
  let em := isoWhiskerLeft I.modules eN ≪≫ I.moduleUnderlying ≪≫
    isoWhiskerRight eM.symm L
  refine
    { ringUnderlying := er
      ringAdd := ?_
      ringMul := ?_
      ringZero := ?_
      ringOne := ?_
      modules := I.modules
      moduleUnderlying := em
      moduleAdd := ?_
      moduleZero := ?_
      moduleSMul := ?_ }
  · intro T a b t h V x
    have hr := I.ringAdd T (a ≫ (eR.app R).hom) (b ≫ (eR.app R).hom)
      (t ≫ (eR.app R).hom) h V x
    simpa [er, eS, sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro T a b t h V x
    have hr := I.ringMul T (a ≫ (eR.app R).hom) (b ≫ (eR.app R).hom)
      (t ≫ (eR.app R).hom) h V x
    simpa [er, eS, sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro T a h V x
    have hr := I.ringZero T (a ≫ (eR.app R).hom) h V x
    simpa [er, eS, sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro T a h V x
    have hr := I.ringOne T (a ≫ (eR.app R).hom) h V x
    simpa [er, eS, sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro M T a b t h V x
    have hr := I.moduleAdd M T (a ≫ (eM.app M).hom) (b ≫ (eM.app M).hom)
      (t ≫ (eM.app M).hom) h V x
    simpa [em, eN, sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro M T a h V x
    have hr := I.moduleZero M T (a ≫ (eM.app M).hom) h V x
    simpa [em, eN, sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro M T a b t h V x
    have hr := I.moduleSMul M T (a ≫ (eR.app R).hom) (b ≫ (eM.app M).hom)
      (t ≫ (eM.app M).hom) h V x
    simpa [er, em, eS, eN, sheafUliftIso, uliftTrivial, Functor.map_comp] using hr

set_option backward.isDefEq.respectTransparency false in
private theorem changeOfRings_eq_ofUniverses
    {S : Sheaf JD CommRingCat.{w}} (c : RI ⟶ S)
    (M : SheafOfModules.{w}
      ((sheafCompose JD (forget₂ CommRingCat.{w} RingCat.{w})).obj RI)) :
    changeOfRings c M = changeOfRingsOfUniverses c M := by
  rfl


private theorem preservesCoproducts_of_finite_and_filtered
    {A : Type uC} {B : Type uD} [Category.{vC} A] [Category.{vD} B]
    (F : A ⥤ B) [HasFiniteCoproducts A] [HasColimitsOfSize.{r, r} A]
    [PreservesFiniteColimits F] (ι : Type r)
    [PreservesColimitsOfShape (Finset (Discrete ι)) F] :
    PreservesColimitsOfShape (Discrete ι) F := by
  classical
  constructor
  intro G
  let f (i : ι) := G.obj ⟨i⟩
  let T := CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor f)
  let c := CoproductsFromFiniteFiltered.finiteSubcoproductsCocone f
  let hc := isColimitOfPreserves F
    (CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone f)
  let hfin (s : Finset (Discrete ι)) := isColimitOfPreserves F
    (colimit.isColimit (Discrete.functor (fun x : s ↦ f x.val.as)))
  let ds (d : Cocone (Discrete.functor f ⋙ F)) (s : Finset (Discrete ι)) :
      Cocone (Discrete.functor (fun x : s ↦ f x.val.as) ⋙ F) :=
    { pt := d.pt
      ι := Discrete.natTrans (fun x ↦ d.ι.app x.as.val) }
  let dt (d : Cocone (Discrete.functor f ⋙ F)) : Cocone (T ⋙ F) :=
    { pt := d.pt
      ι :=
        { app := fun s ↦ (hfin s).desc (ds d s)
          naturality := by
            intro s t i
            apply (hfin s).hom_ext
            rintro ⟨x⟩
            dsimp [hfin, T, CoproductsFromFiniteFiltered.liftToFinsetObj]
            simp only [Category.comp_id, ← F.map_comp_assoc, Sigma.ι_desc]
            have ht := (hfin t).fac (ds d t) ⟨⟨x.val, i.down.down x.property⟩⟩
            have hs := (hfin s).fac (ds d s) ⟨x⟩
            exact ht.trans hs.symm } }
  have hcop : IsColimit (F.mapCocone (colimit.cocone (Discrete.functor f))) := by
    refine
      { desc := fun d ↦ hc.desc (dt d)
        fac := ?_
        uniq := ?_ }
    · intro d i
      let s : Finset (Discrete ι) := {i}
      let x : s := ⟨i, by simp [s]⟩
      have hi : F.map (Sigma.ι f i.as) =
          F.map (Sigma.ι (fun x : s ↦ f x.val.as) x) ≫ F.map (c.ι.app s) := by
        simp [c, CoproductsFromFiniteFiltered.finiteSubcoproductsCocone,
          ← F.map_comp, x]
      change F.map (Sigma.ι f i.as) ≫ _ = _
      rw [hi, Category.assoc]
      have hcs := hc.fac (dt d) s
      change F.map (c.ι.app s) ≫ hc.desc (dt d) = (dt d).ι.app s at hcs
      rw [hcs]
      exact (hfin s).fac (ds d s) ⟨x⟩
    · intro d m hm
      apply hc.hom_ext
      intro s
      apply (hfin s).hom_ext
      rintro ⟨x⟩
      rw [hc.fac (dt d) s]
      change F.map (Sigma.ι (fun x : s ↦ f x.val.as) x) ≫
        F.map (c.ι.app s) ≫ m = _
      rw [← F.map_comp_assoc]
      have hs := (hfin s).fac (ds d s) ⟨x⟩
      change F.map (Sigma.ι (fun x : s ↦ f x.val.as) x) ≫
        (dt d).ι.app s = d.ι.app x.val at hs
      change F.map (Sigma.ι (fun x : s ↦ f x.val.as) x ≫ c.ι.app s) ≫ m =
        F.map (Sigma.ι (fun x : s ↦ f x.val.as) x) ≫ (dt d).ι.app s
      have hx := hm x.val
      change F.map (Sigma.ι f x.val.as) ≫ m = d.ι.app x.val at hx
      simpa only [c, CoproductsFromFiniteFiltered.finiteSubcoproductsCocone_ι_app,
        Sigma.ι_desc] using hx.trans hs.symm
  have := preservesColimit_of_preserves_colimit_cocone
    (colimit.isColimit (Discrete.functor f)) hcop
  exact preservesColimit_of_iso_diagram F
    (show Discrete.functor f ≅ G from Discrete.natIso (fun i ↦ Iso.refl (G.obj i)))

/-- Exact ringed pullback preserves resolving complexes, arbitrary small direct sums and
integer signs. Its derived comparison is invertible on every complex and determines a
unique natural isomorphism to exact localization, normalized already on resolving complexes.
The isomorphism respects all integer shifts and the degree-zero comparison, even for
nonflat modules.

Source: Stacks Project, derived.tex, Tag 015F (dual left-derived exactness), and
sites-cohomology.tex, Tags 06YS, 06YY and 0G7E
(blueprint: lem-pur-exact-derived-resolving-identification).

Proof:
1. The module adjunction (lem-weil-pbc-ringed-topoi-module-adjunction) and the
left-adjoint colimit theorem (lem-weil-pbc-left-adjoint-preserves-colimits) give preservation
of arbitrary small coproducts, including the diagonal sums in an unbounded total tensor.
Flat and resolving preservation are lem-weil-pbc-ringed-topos-flat-module-pullback and
lem-weil-pbc-ringed-topos-kflat-pullback.
2. Additivity gives preservation of integer multiples, hence differential, shift and
Koszul signs. The coproduct comparison preserves each summand inclusion, so these equations
also hold on the unbounded total differential (def-pc-tensor-complex-sheaves).
3. For any A choose a flat-term K-flat quasi-isomorphism p : P ⟶ A
(lem-pc-kflat-resolution). Naturality expresses epsilon_A as epsilon_P conjugated by
L(q_R p) and q_S(Fp). Both maps are invertible by exact factorization
(lem-weil-pbc-exact-functor-derived-factorization), so epsilon_A is invertible.
4. The natural isomorphism epsilon followed by kappa inverse descends uniquely through
localization (lem-weil-pbc-localization-universal-property); descend its inverse as well.
This gives the all-complex normalization.
5. Any other isomorphism normalized on resolving P agrees on A by naturality along p,
and then everywhere by localization faithfulness. Thus uniqueness uses only resolving
normalization.
6. Shifts preserve resolving complexes: reindex the flat terms, and use the total-tensor
isomorphism with factor (-1)^(np) on the (p,q) summand to check K-flatness. The stipulated
resolving shift normalization of epsilon and the unsigned termwise identity normalization
of kappa give shift compatibility on P. Naturality along q_R p extends this to all A;
localization faithfulness extends it to every derived object, for every integer shift.
7. Substitute the single complex M[0] in the all-complex equation. Termwise F(M[0]) is
(FM)[0], so the same equation identifies the degree-zero comparisons without flatness of M.
-/
theorem exactDerivedResolvingIdentification
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{r}} {S RI : Sheaf JD CommRingCat.{r}}
    (uInv : Sheaf JC (Type r) ⥤ Sheaf JD (Type r))
    (uPush : Sheaf JD (Type r) ⥤ Sheaf JC (Type r))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (F : Mod JC R ⥤ Mod JD S)
    (hobj : ∀ M : Mod JC R, F.obj M = changeOfRings c (I.modules.obj M))
    (hmap : ∀ {M N : Mod JC R} (v : M ⟶ N), F.map v =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map v) ≫
        eqToHom (hobj N).symm)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [HasDerivedCategory.{w} (Mod JC R)] [HasDerivedCategory.{w} (Mod JD S)]
    (L : DerivedCategory (Mod JC R) ⥤ DerivedCategory (Mod JD S))
    (epsilon : DerivedCategory.Qh ⋙ L ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hL : L.IsLeftDerivedFunctor epsilon
      (HomotopyCategory.quasiIso (Mod JC R) (.up ℤ)))
    (he : ∀ P : CochainComplex (Mod JC R) ℤ,
      P.IsKFlatIndependentCoefficients → (∀ i : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X i)) →
        IsIso (epsilon.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    [L.CommShift ℤ]
    (hshift : ∀ (P : CochainComplex (Mod JC R) ℤ),
      P.IsKFlatIndependentCoefficients → (∀ i : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X i)) →
      ∀ n : ℤ,
        ((DerivedCategory.Qh ⋙ L).commShiftIso n).hom.app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
          (shiftFunctor _ n).map
            (epsilon.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
        epsilon.app (((HomotopyCategory.quotient _ (.up ℤ)).obj P)⟦n⟧) ≫
          ((F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).commShiftIso n).hom.app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :
    (∀ M : Mod JC R, IsFlatOnSite (J := JC) (R := R) M →
        IsFlatOnSite (J := JD) (R := S) (F.obj M)) ∧
    (∀ P : CochainComplex (Mod JC R) ℤ,
      P.IsKFlatIndependentCoefficients → (∀ i : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X i)) →
      CochainComplex.IsKFlatIndependentCoefficients
        ((F.mapHomologicalComplex (.up ℤ)).obj P) ∧
        ∀ i : ℤ, IsFlatOnSite (J := JD) (R := S)
          (((F.mapHomologicalComplex (.up ℤ)).obj P).X i)) ∧
    (∀ ι : Type r, PreservesColimitsOfShape (Discrete ι) F) ∧
    (∀ (M N : Mod JC R) (v : M ⟶ N) (z : ℤ), F.map (z • v) = z • F.map v) ∧
    (∀ (A B : CochainComplex (Mod JC R) ℤ) (v : A ⟶ B) (z : ℤ),
      (F.mapHomologicalComplex (.up ℤ)).map (z • v) =
        z • (F.mapHomologicalComplex (.up ℤ)).map v) ∧
    (∀ A : CochainComplex (Mod JC R) ℤ,
      IsIso (epsilon.app ((HomotopyCategory.quotient _ (.up ℤ)).obj A))) ∧
    ∃ eta : L ≅ F.mapDerivedCategory,
      (∀ P : CochainComplex (Mod JC R) ℤ,
        P.IsKFlatIndependentCoefficients → (∀ i : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X i)) →
        eta.hom.app (DerivedCategory.Q.obj P) ≫
          F.mapDerivedCategoryFactorsh.hom.app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
          epsilon.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ∧
      (∀ eta' : L ≅ F.mapDerivedCategory,
        (∀ P : CochainComplex (Mod JC R) ℤ,
          P.IsKFlatIndependentCoefficients → (∀ i : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X i)) →
          eta'.hom.app (DerivedCategory.Q.obj P) ≫
            F.mapDerivedCategoryFactorsh.hom.app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
            epsilon.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) → eta' = eta) ∧
      (∀ A : CochainComplex (Mod JC R) ℤ,
        eta.hom.app (DerivedCategory.Q.obj A) ≫
          F.mapDerivedCategoryFactorsh.hom.app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj A) =
          epsilon.app ((HomotopyCategory.quotient _ (.up ℤ)).obj A)) ∧
      NatTrans.CommShift eta.hom ℤ ∧
      (∀ M : Mod JC R,
        eta.hom.app (DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj M)) ≫
          F.mapDerivedCategoryFactorsh.hom.app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj
              ((HomologicalComplex.single _ (.up ℤ) 0).obj M)) =
          epsilon.app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj
              ((HomologicalComplex.single _ (.up ℤ) 0).obj M))) := by
  classical
  have hflat (M : Mod JC R) (hM : IsFlatOnSite (J := JC) (R := R) M) :
      IsFlatOnSite (J := JD) (R := S) (F.obj M) := by
    rw [hobj M, changeOfRings_eq_ofUniverses]
    exact isFlat_ringedToposPullback.{uC, vC, uD, vD, r, r}
      uInv uPush adj (inverseImageOfUniverses I) c M hM
  have hdet (G H : DerivedCategory (Mod JC R) ⥤ DerivedCategory (Mod JD S))
      (a b : G ⟶ H)
      (h : ∀ P : CochainComplex (Mod JC R) ℤ,
        P.IsKFlatIndependentCoefficients →
        (∀ i : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X i)) →
        a.app (DerivedCategory.Q.obj P) = b.app (DerivedCategory.Q.obj P)) : a = b := by
    apply Localization.natTrans_ext DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Mod JC R) (.up ℤ))
    intro X
    obtain ⟨A, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨P, p, hp, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) A
    have hflatP (i : ℤ) : IsFlatOnSite (J := JC) (R := R) (P.X i) :=
      (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (P.X i)).symm (hf i)
    let := hq
    have : IsIso (G.map (DerivedCategory.Q.map p)) := inferInstance
    change a.app (DerivedCategory.Q.obj A) = b.app (DerivedCategory.Q.obj A)
    rw [← cancel_epi (G.map (DerivedCategory.Q.map p)),
      a.naturality, b.naturality, h P hp hflatP]
  refine ⟨hflat, isKFlat_ringedToposPullback uInv uPush adj I c F hobj hmap,
    ?_, fun M N v z ↦ F.map_zsmul (f := v) (r := z),
    fun A B v z ↦ (F.mapHomologicalComplex (.up ℤ)).map_zsmul (f := v) (r := z), ?_, ?_⟩
  · intro ι
    have := preservesFilteredColimits_ringedToposPullback uInv uPush adj I c F
      hobj hmap (Finset (Discrete ι))
    exact preservesCoproducts_of_finite_and_filtered F ι
  · intro A
    obtain ⟨P, p, hp, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) A
    have hflatP (i : ℤ) : IsFlatOnSite (J := JC) (R := R) (P.X i) :=
      (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (P.X i)).symm (hf i)
    let q := (HomotopyCategory.quotient (Mod JC R) (.up ℤ)).map p
    let W := HomotopyCategory.quasiIso (Mod JC R) (.up ℤ)
    have hq' : W q := (HomotopyCategory.quotient_map_mem_quasiIso_iff p).2 hq
    have := Localization.inverts DerivedCategory.Qh W q hq'
    have := he P hp hflatP
    have hi := (MorphismProperty.IsInvertedBy.iff_of_iso W
      F.mapDerivedCategoryFactorsh).mp
        (MorphismProperty.IsInvertedBy.of_comp W DerivedCategory.Qh
          (Localization.inverts DerivedCategory.Qh W) F.mapDerivedCategory)
    have := hi q hq'
    have : IsIso ((DerivedCategory.Qh ⋙ L).map q) := by
      change IsIso (L.map (DerivedCategory.Qh.map q))
      infer_instance
    have : IsIso (((DerivedCategory.Qh ⋙ L).map q) ≫
        epsilon.app ((HomotopyCategory.quotient _ (.up ℤ)).obj A)) := by
      rw [epsilon.naturality]
      infer_instance
    exact (isIso_comp_left_iff ((DerivedCategory.Qh ⋙ L).map q) _).1 this
  · let W := HomotopyCategory.quasiIso (Mod JC R) (.up ℤ)
    let := hL
    let := Functor.isLeftDerivedFunctor_of_inverts W F.mapDerivedCategory
      F.mapDerivedCategoryFactorsh
    let eta := Functor.leftDerivedUnique F.mapDerivedCategory L epsilon
      F.mapDerivedCategoryFactorsh.hom W
    have hnorm (A : CochainComplex (Mod JC R) ℤ) :
        eta.hom.app (DerivedCategory.Q.obj A) ≫
          F.mapDerivedCategoryFactorsh.hom.app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj A) =
          epsilon.app ((HomotopyCategory.quotient _ (.up ℤ)).obj A) := by
      change (Functor.leftDerivedNatTrans L F.mapDerivedCategory epsilon
        F.mapDerivedCategoryFactorsh.hom W (𝟙 _)).app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj A)) ≫ _ = _
      simpa only [NatTrans.id_app, Category.comp_id] using
        Functor.leftDerivedNatTrans_app L F.mapDerivedCategory epsilon
          F.mapDerivedCategoryFactorsh.hom W (𝟙 _) 
          ((HomotopyCategory.quotient _ (.up ℤ)).obj A)
    refine ⟨eta, fun P hp hf ↦ hnorm P, ?_, hnorm, ?_, fun M ↦ hnorm _⟩
    · intro eta' hn
      apply Iso.ext
      apply hdet L F.mapDerivedCategory
      intro P hp hf
      rw [← cancel_mono (F.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)), hn P hp hf, hnorm P]
    · have hnormK : Functor.whiskerLeft DerivedCategory.Qh eta.hom ≫
          F.mapDerivedCategoryFactorsh.hom = epsilon := by
        change Functor.whiskerLeft DerivedCategory.Qh
          (Functor.leftDerivedNatTrans L F.mapDerivedCategory epsilon
            F.mapDerivedCategoryFactorsh.hom W (𝟙 _)) ≫ _ = _
        simpa only [Category.comp_id] using
          Functor.leftDerivedNatTrans_fac L F.mapDerivedCategory epsilon
            F.mapDerivedCategoryFactorsh.hom W (𝟙 _)
      constructor
      intro n
      apply hdet (shiftFunctor _ n ⋙ L) (F.mapDerivedCategory ⋙ shiftFunctor _ n)
      intro P hp hf
      let X := (HomotopyCategory.quotient (Mod JC R) (.up ℤ)).obj P
      let b := Functor.whiskerLeft DerivedCategory.Qh eta.hom
      have hb : ((DerivedCategory.Qh ⋙ L).commShiftIso n).hom.app X ≫
          (shiftFunctor _ n).map (b.app X) =
          b.app (X⟦n⟧) ≫
            ((DerivedCategory.Qh ⋙ F.mapDerivedCategory).commShiftIso n).hom.app X := by
        apply (cancel_mono ((shiftFunctor _ n).map
          (F.mapDerivedCategoryFactorsh.hom.app X))).1
        have hh := hshift P hp hf n
        rw [← hnormK] at hh
        simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc] at hh
        rw [← NatTrans.shift_app_comm F.mapDerivedCategoryFactorsh.hom n] at hh
        simpa only [b, X, Category.assoc] using hh
      dsimp only [b, Functor.whiskerLeft_app] at hb
      simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at hb
      rw [← eta.hom.naturality_assoc] at hb
      exact (cancel_epi (L.map ((DerivedCategory.Qh.commShiftIso n).hom.app X))).1 hb

end SheafOfModules
