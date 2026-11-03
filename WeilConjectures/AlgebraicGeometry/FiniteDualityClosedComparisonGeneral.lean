/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDualityClosedComparison
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedSupportTriangle
import WeilConjectures.SixFunctors.OpenClosed.Supported
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # Closed exceptional comparison for arbitrary finite primary coefficients

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
lem-weil-finite-duality-site-comparison.proof.md, first paragraph;
Wei Yang #1441 item 28 and #1423 (geometric fields and arbitrary finite coefficients).
(blueprint: lem-weil-finite-duality-closed-comparison).

The existing delta and alpha constructions are reused without changing their maps.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option linter.unusedVariables false in
private theorem closedComparisonDelta_naturality
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [QuasiCompact i] [QuasiSeparated i]
    {X Y : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (L L' : DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (e : X ≅ DerivedCategory.Plus.ι.obj L)
    (e' : Y ≅ DerivedCategory.Plus.ι.obj L') (f : X ⟶ Y) :
    finiteDualityClosedComparisonDelta i X L e ≫
      (ProEtale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor.map
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.map f) =
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.map
      ((Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i).map f) ≫
      finiteDualityClosedComparisonDelta i Y L' e' := by
  let g : L ⟶ L' := DerivedCategory.Plus.ι.preimage (e.inv ≫ f ≫ e'.hom)
  have hg : DerivedCategory.Plus.ι.map g = e.inv ≫ f ≫ e'.hom :=
    DerivedCategory.Plus.ι.map_preimage _
  let RE := Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i
  let RP := (ProEtale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor
  let FT := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory
  let FZ := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory
  let b : DerivedCategory.Plus.ι ⋙ RE ⋙ FT ⟶ DerivedCategory.Plus.ι ⋙ FZ ⋙ RP :=
    Functor.whiskerRight
        (Etale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorPlusCompatibility.inv FT ≫
      Functor.whiskerLeft (Etale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorPlus
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T
          ).mapDerivedCategoryPlusCompatibility.inv ≫
      Functor.whiskerRight (ProEtale.fixedComparisonDirectImageMatePlus A i)
        DerivedCategory.Plus.ι ≫
      Functor.whiskerLeft
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlus
        (ProEtale.lowerStar (ModuleCat.{u + 1} A) i
          ).rightDerivedFunctorPlusCompatibility.hom ≫
      Functor.whiskerRight
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Z
        ).mapDerivedCategoryPlusCompatibility.hom RP
  have hf : f = e.hom ≫ DerivedCategory.Plus.ι.map g ≫ e'.inv := by
    rw [hg]
    simp
  rw [hf]
  simpa [finiteDualityClosedComparisonDelta, b, RE, RP, FT, FZ,
    Functor.map_comp, Category.assoc] using
    congrArg (fun k ↦ FT.map (RE.map e.hom) ≫ k ≫ RP.map (FZ.map e'.inv))
      (b.naturality g).symm

open Etale in
set_option linter.unusedVariables false in
set_option linter.unusedVariables false in
private theorem closedRightAdjoint_boundedBelow
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (M : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hM : DerivedCategory.TStructure.t.plus M) :
    letI : (Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i).IsLeftAdjoint :=
      Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion A i
    ∃ L : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)),
      Nonempty ((Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i).rightAdjoint.obj M ≅
        DerivedCategory.Plus.ι.obj L) := by
  let : (Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i).IsLeftAdjoint :=
      Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion A i
  let F := Etale.lowerStar (ModuleCat.{u + 1} A) i
  let : F.IsLeftAdjoint := closedLowerStar_isLeftAdjoint A i
  let adj := Adjunction.ofIsLeftAdjoint F
  let : F.rightAdjoint.Additive := adj.right_adjoint_additive
  let adjD := adj.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoLeft
    F.rightDerivedFunctorIsoMapDerivedCategory.symm
  let e := (Adjunction.ofIsLeftAdjoint F.rightDerivedFunctor).rightAdjointUniq adjD
  let Mplus : DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) := ⟨M, hM⟩
  exact ⟨F.rightAdjoint.rightDerivedFunctorPlus.obj Mplus,
    ⟨e.app M ≪≫ (F.rightAdjoint.rightDerivedFunctorPlusCompatibility.app Mplus).symm⟩⟩

set_option linter.unusedVariables false in
private theorem closedComparisonAlpha_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    [hRE : (Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i).IsLeftAdjoint]
    [QuasiCompact i] [QuasiSeparated i]
    (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (M : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hM : DerivedCategory.TStructure.t.plus M)
    (L : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (e : (Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i).rightAdjoint.obj M ≅
      DerivedCategory.Plus.ι.obj L)
    [hδ : IsIso (finiteDualityClosedComparisonDelta i _ L e)] :
    IsIso (finiteDualityClosedComparisonAlpha i j
      (Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i)
      (Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i).rightAdjoint
      (ProEtale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor
      (ProEtale.closedUpperShriek (ModuleCat.{u + 1} A) i j).rightDerivedFunctor
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory
      (Adjunction.ofIsLeftAdjoint (Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i))
      (ProEtale.derivedLowerStarClosedUpperShriekAdjunction i j hij) M
      (asIso (finiteDualityClosedComparisonDelta i _ L e))) := by
  let C := ModuleCat.{u + 1} A
  let RE := Etale.rightDerivedLowerStar C i
  let RP := (ProEtale.lowerStar C i).rightDerivedFunctor
  let IP := (ProEtale.closedUpperShriek C i j).rightDerivedFunctor
  let FT := (ProEtale.comparisonUpperStar C T).mapDerivedCategory
  let adjE := Adjunction.ofIsLeftAdjoint RE
  let adjP := ProEtale.derivedLowerStarClosedUpperShriekAdjunction (R := A) i j hij
  let JP := (ProEtale.upperStar C j).mapDerivedCategory
  let GP := (ProEtale.lowerStar C j).rightDerivedFunctor
  let adjj := (ProEtale.upperStarLowerStarAdjunction C j
    ).mapDerivedCategoryRightDerivedAdjunction
  let := ProEtale.preservesFiniteColimits_lowerStar_of_isCompl (R := A) i j hij
  have hz (P : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) C)) :
      IsZero (JP.obj (RP.obj P)) := by
    have hz' : IsZero (JP.obj ((ProEtale.lowerStar C i).mapDerivedCategory.obj P)) :=
      (Functor.isZero_mapDerivedCategory_obj (ProEtale.lowerStar C i ⋙
        ProEtale.upperStar C j) P
        (fun n ↦ ProEtale.isZero_upperStar_lowerStar_of_disjoint C i j hij.disjoint
          ((DerivedCategory.homologyFunctor _ n).obj P))).of_iso
          (((ProEtale.lowerStar C i).mapDerivedCategoryCompIso
            (ProEtale.upperStar C j)).symm.app P)
    exact hz'.of_iso (JP.mapIso
      ((ProEtale.lowerStar C i).rightDerivedFunctorIsoMapDerivedCategory.app P))
  have hkill (N : DerivedCategory (Sheaf (Scheme.ProEt.topology U) C)) :
      IsZero (IP.obj (GP.obj N)) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply (adjP.homEquiv _ _).symm.injective
    let : Subsingleton (JP.obj (RP.obj (IP.obj (GP.obj N))) ⟶ N) :=
      ⟨fun f g ↦ (hz _).eq_of_src f g⟩
    have : Subsingleton (RP.obj (IP.obj (GP.obj N)) ⟶ GP.obj N) :=
      (adjj.homEquiv (RP.obj (IP.obj (GP.obj N))) N).symm.subsingleton
    exact Subsingleton.elim _ _
  let JE := (Etale.upperStar C j).mapDerivedCategory
  let GE := Etale.rightDerivedLowerStar C j
  let Mplus : DerivedCategory.Plus (Sheaf T.smallEtaleTopology C) := ⟨M, hM⟩
  let Lopen := (Etale.upperStar C j).mapDerivedCategoryPlus.obj Mplus
  let eopen : JE.obj M ≅ DerivedCategory.Plus.ι.obj Lopen :=
    ((Etale.upperStar C j).mapDerivedCategoryPlusCompatibility.app Mplus).symm
  have hopen : IsZero (IP.obj (FT.obj (GE.obj (JE.obj M)))) :=
    (hkill _).of_iso (IP.mapIso
      (asIso (finiteDualityClosedComparisonDelta j (JE.obj M) Lopen eopen)))
  obtain ⟨w, hw⟩ := Etale.exists_etale_closedSupportTriangle A i j hij.eq_compl
  have hdist := IP.map_distinguished _ (FT.map_distinguished _ (hw M))
  have hc : IsIso (IP.map (FT.map (adjE.counit.app M))) :=
    (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hdist).1 hopen
  unfold finiteDualityClosedComparisonAlpha
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  infer_instance


/-- Closed exceptional restriction commutes with etale/pro-etale comparison through the
specified direct-image counit mate, for every bounded-below lift of its etale value.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
lem-weil-finite-duality-site-comparison.proof.md, first paragraph; Wei Yang #1441 item 28
and #1423 (blueprint: lem-weil-finite-duality-closed-comparison).

Proof plan:
1. Finite type over a field makes T Noetherian. Closed direct image is exact; its
ambient right adjoint sends bounded objects to bounded-below objects by the exact
adjunction bounds (lem-pur-exact-derived-adjunction-bounds).
2. Both immersions are qcqs. Transport fixedComparisonDirectImageMatePlus through the
named Plus/full compatibilities and e to obtain delta. Fullness of D+ and naturality
of the Plus mate show naturality for arbitrary lifts, and independence of the lift.
3. The exact fully faithful closed pro-etale direct image and its open complement
satisfy j* i* = 0. Adjunction gives I_pro Rj* = 0, since every Hom into it vanishes.
4. Apply I_pro nu* to the etale closed-support counit triangle. The open direct-image
comparison and pullback comparison identify the third term with a term killed in
Step 3. Hence I_pro nu* of the etale counit is invertible. This uses localization,
not biduality or any identification of ordinary closed restriction with internal Hom.
5. Alpha is the pro-etale adjunction transpose of delta inverse followed by the
pulled-back etale counit. Its formula is the composite of the fully faithful closed
unit, I_pro(delta inverse), and the isomorphism in Step 4, hence is invertible.
6. Inverse transposition and cancellation of delta give the displayed counit equation.
Transpose both candidate naturality composites; naturality of delta and the etale
counit make their transposes equal, and injectivity of homEquiv proves naturality.
The zero ring, empty schemes, identity closed immersion and arbitrary lifts are retained. -/
theorem finiteDualityClosedComparisonGeneral
    (l : ℕ) [Fact l.Prime]
    (k : Type u) [Field k] (_hk : Finite k ∨ IsAlgClosed k) (_hchar : ringChar k ≠ l)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (_hA : ∃ N : ℕ, (l ^ N : ℕ) • (1 : A) = 0)
    (T Z U : Scheme.{u})
    (aT : T ⟶ Spec (.of k)) (aZ : Z ⟶ Spec (.of k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    [LocallyOfFiniteType aZ] [QuasiCompact aZ] [IsSeparated aZ]
    (i : Z ⟶ T) [IsClosedImmersion i]
    (j : U ⟶ T) [IsOpenImmersion j]
    (_hi : i ≫ aT = aZ)
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    letI : IsNoetherian T := {
      __ := LocallyOfFiniteType.isLocallyNoetherian aT
      __ := QuasiCompact.compactSpace_of_compactSpace aT }
    let Rₑ := Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i
    letI : Rₑ.IsLeftAdjoint :=
      Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion A i
    let Iₑ := Rₑ.rightAdjoint
    let Rₚ := (ProEtale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor
    let Iₚ := (ProEtale.closedUpperShriek (ModuleCat.{u + 1} A) i j).rightDerivedFunctor
    let F_T := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory
    let F_Z := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory
    let adjₑ : Rₑ ⊣ Iₑ := Adjunction.ofIsLeftAdjoint Rₑ
    let adjₚ : Rₚ ⊣ Iₚ :=
      ProEtale.derivedLowerStarClosedUpperShriekAdjunction i j hij
    ∀ (M : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (_hM : Etale.DerivedCategory.isBoundedConstructible A T M),
      (∃ L : DerivedCategory.Plus
          (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)),
        Nonempty (Iₑ.obj M ≅ DerivedCategory.Plus.ι.obj L)) ∧
      (∀ (L : DerivedCategory.Plus
          (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
        (e : Iₑ.obj M ≅ DerivedCategory.Plus.ι.obj L),
        let δ := finiteDualityClosedComparisonDelta i (Iₑ.obj M) L e
        let δIso : F_T.obj (Rₑ.obj (Iₑ.obj M)) ≅
            Rₚ.obj (F_Z.obj (Iₑ.obj M)) := asIso δ
        let α := finiteDualityClosedComparisonAlpha i j Rₑ Iₑ Rₚ Iₚ F_T F_Z
          adjₑ adjₚ M δIso
        IsIso α ∧
        (δ ≫ Rₚ.map α ≫ adjₚ.counit.app (F_T.obj M) =
          F_T.map (adjₑ.counit.app M)) ∧
        (∀ (N : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
          (h : M ⟶ N) (_hN : Etale.DerivedCategory.isBoundedConstructible A T N)
          (L' : DerivedCategory.Plus
            (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
          (e' : Iₑ.obj N ≅ DerivedCategory.Plus.ι.obj L'),
          let δ' := finiteDualityClosedComparisonDelta i (Iₑ.obj N) L' e'
          let δIso' : F_T.obj (Rₑ.obj (Iₑ.obj N)) ≅
              Rₚ.obj (F_Z.obj (Iₑ.obj N)) := asIso δ'
          F_Z.map (Iₑ.map h) ≫
              finiteDualityClosedComparisonAlpha i j Rₑ Iₑ Rₚ Iₚ F_T F_Z
                adjₑ adjₚ N δIso' =
            finiteDualityClosedComparisonAlpha i j Rₑ Iₑ Rₚ Iₚ F_T F_Z
              adjₑ adjₚ M δIso ≫ Iₚ.map (F_T.map h))) := by
  let : IsNoetherian T := {
    __ := LocallyOfFiniteType.isLocallyNoetherian aT
    __ := QuasiCompact.compactSpace_of_compactSpace aT }
  let RE := Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i
  let : RE.IsLeftAdjoint :=
    Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion A i
  let IE := RE.rightAdjoint
  let RP := (ProEtale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor
  let IP := (ProEtale.closedUpperShriek (ModuleCat.{u + 1} A) i j).rightDerivedFunctor
  let FT := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory
  let FZ := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory
  let adjE : RE ⊣ IE := Adjunction.ofIsLeftAdjoint RE
  let adjP : RP ⊣ IP := ProEtale.derivedLowerStarClosedUpperShriekAdjunction i j hij
  dsimp only
  intro M hM
  have hMplus : DerivedCategory.TStructure.t.plus M := by
    obtain ⟨a, b, _, hv⟩ := hM.2
    exact ⟨a, (DerivedCategory.isGE_iff M a).2 (fun q hq ↦ hv q (Or.inl hq))⟩
  refine ⟨closedRightAdjoint_boundedBelow A i M hMplus, ?_⟩
  intro L e
  let d := finiteDualityClosedComparisonDelta i (IE.obj M) L e
  let : IsIso d := isIso_finiteDualityClosedComparisonDelta_proof i (IE.obj M) L e
  let a := finiteDualityClosedComparisonAlpha i j RE IE RP IP FT FZ adjE adjP M (asIso d)
  change IsIso a ∧
    (d ≫ RP.map a ≫ adjP.counit.app (FT.obj M) = FT.map (adjE.counit.app M)) ∧ _
  refine ⟨closedComparisonAlpha_isIso A i j hij M hMplus L e, ?_, ?_⟩
  · have hc : RP.map a ≫ adjP.counit.app (FT.obj M) =
        (asIso d).inv ≫ FT.map (adjE.counit.app M) := by
      exact (adjP.homEquiv_counit (FZ.obj (IE.obj M)) (FT.obj M) a).symm.trans
        ((adjP.homEquiv _ _).symm_apply_apply _)
    simpa [Category.assoc] using congrArg (fun k ↦ d ≫ k) hc
  · intro N h hN L' e'
    let d' := finiteDualityClosedComparisonDelta i (IE.obj N) L' e'
    change FZ.map (IE.map h) ≫
        (adjP.homEquiv _ _) ((asIso d').inv ≫ FT.map (adjE.counit.app N)) =
      (adjP.homEquiv _ _) ((asIso d).inv ≫ FT.map (adjE.counit.app M)) ≫ IP.map (FT.map h)
    apply (adjP.homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_naturality_left_symm,
      Adjunction.homEquiv_naturality_right_symm,
      Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    have hd := closedComparisonDelta_naturality i L L' e e' (IE.map h)
    have hi : RP.map (FZ.map (IE.map h)) ≫ (asIso d').inv =
        (asIso d).inv ≫ FT.map (RE.map (IE.map h)) := by
      apply (cancel_epi d).1
      apply (cancel_mono d').1
      simpa [Category.assoc] using hd
    rw [reassoc_of% hi, ← FT.map_comp]
    rw [adjE.counit_naturality h]
    simp only [Functor.map_comp, Category.assoc]


end AlgebraicGeometry
