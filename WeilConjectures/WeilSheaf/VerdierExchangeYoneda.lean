/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.VerdierExchange
public import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
public import WeilConjectures.Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# The Verdier exchange for Weil complexes (re-export)

This module re-exports `WeilConjectures.WeilSheaf.VerdierExchange`, which contains the statements
formerly duplicated here (`WeilConjectures.CoefficientClosedStructure.curryYonedaIso`,
`AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedTensorCurryYonedaIso`,
`AlgebraicGeometry.WeilComplex.nativeConstructibleTensorCurryYonedaIso`,
`AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriek_op_comp_iso_of_adjunction`); the copies
were removed because a module importing both saw every declaration twice (lean-eval bump dedup, 2026-11-07).
-/

/-- **Verdier exchange, natural form** (blueprint: `fix-cor-verdier-exchange`, with
`fix-lem-tensor-adjunction`): let `a_X = f ≫ a_Y` be morphisms to a base `S`, `G_X`, `G_Y` right
adjoints of `Ra_{X,0}!` and `Ra_{Y,0}!`, and `Q` a Weil complex on `S`. If `RHom(-, G_X Q)` and
`RHom(-, G_Y Q)` send Weil complexes to Weil complexes, then
`RHom(Rf₀! M, G_Y Q) ≅ Rf_* RHom(M, G_X Q)`, naturally in the Weil complex `M`. -/
theorem nonempty_derivedLowerShriek_op_comp_iso_of_adjunction {S : Scheme.{u}}
    [S.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (S ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (S ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (S ↘ Spec (CommRingCat.of k₀))]
    (aX : X ⟶ S) (aY : Y ⟶ S) [aX.IsOver (Spec (CommRingCat.of k₀))]
    [aY.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated aX] [LocallyOfFiniteType aX]
    [QuasiCompact aX] [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (h : f ≫ aY = aX) {GX : WeilComplex k₀ l S ⥤ WeilComplex k₀ l X}
    {GY : WeilComplex k₀ l S ⥤ WeilComplex k₀ l Y}
    (adjX : derivedLowerShriek k₀ l aX ⊣ GX) (adjY : derivedLowerShriek k₀ l aY ⊣ GY)
    (Q : WeilComplex k₀ l S)
    (hX : ∀ K : WeilComplex k₀ l X, objectProperty k₀ l X
      ((ProEtaleWeilSheaf.derivedHom k₀ l X (GX.obj Q).obj).obj (op K.obj)))
    (hY : ∀ K : WeilComplex k₀ l Y, objectProperty k₀ l Y
      ((ProEtaleWeilSheaf.derivedHom k₀ l Y (GY.obj Q).obj).obj (op K.obj))) :
    Nonempty ((derivedLowerShriek k₀ l f).op ⋙
        (objectProperty k₀ l Y).lift ((objectProperty k₀ l Y).ι.op ⋙
          ProEtaleWeilSheaf.derivedHom k₀ l Y (GY.obj Q).obj) (fun K ↦ hY K.unop) ≅
      (objectProperty k₀ l X).lift ((objectProperty k₀ l X).ι.op ⋙
          ProEtaleWeilSheaf.derivedHom k₀ l X (GX.obj Q).obj) (fun K ↦ hX K.unop) ⋙
        derivedLowerStar f) := by
  subst h
  obtain ⟨π⟩ := nonempty_nativeCompactProjectionLeft_iso (k₀ := k₀) (l := l) f
  obtain ⟨c⟩ := nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) f aY
  let DX := (objectProperty k₀ l X).lift ((objectProperty k₀ l X).ι.op ⋙
    ProEtaleWeilSheaf.derivedHom k₀ l X (GX.obj Q).obj) (fun K ↦ hX K.unop)
  let DY := (objectProperty k₀ l Y).lift ((objectProperty k₀ l Y).ι.op ⋙
    ProEtaleWeilSheaf.derivedHom k₀ l Y (GY.obj Q).obj) (fun K ↦ hY K.unop)
  -- `P ↦ Hom(Rf₀! P, G_Y Q)` is `P ↦ Hom(P, G_X Q)`.
  let q : (derivedLowerShriek k₀ l f).op ⋙ yoneda.obj (GY.obj Q) ≅ yoneda.obj (GX.obj Q) :=
    Functor.isoWhiskerLeft (derivedLowerShriek k₀ l f).op (adjY.compYonedaIso.app Q) ≪≫
      Functor.isoWhiskerRight (NatIso.op c) (yoneda.obj Q) ≪≫ (adjX.compYonedaIso.app Q).symm
  -- `Hom(T, D_Y Rf₀! M) = Hom(Rf₀! M ⊗ T, ω_Y) = Hom(Rf₀!(M ⊗ f^* T), ω_Y)`
  -- `= Hom(M ⊗ f^* T, ω_X) = Hom(f^* T, D_X M) = Hom(T, Rf_* D_X M)`.
  let e : ((derivedLowerShriek k₀ l f).op ⋙ DY) ⋙ yoneda ≅ (DX ⋙ derivedLowerStar f) ⋙ yoneda :=
    Functor.isoWhiskerLeft (derivedLowerShriek k₀ l f).op
        (nativeConstructibleTensorCurryYonedaIso (GY.obj Q) hY).symm ≪≫
      (Functor.curryObjProdComp (derivedLowerShriek k₀ l f).op (𝟭 (WeilComplex k₀ l Y)).op
        ((prodOpEquiv _).inverse ⋙ (nativeConstructibleTensor k₀ l Y).op ⋙
          yoneda.obj (GY.obj Q))).symm ≪≫
      Functor.curry.mapIso (Functor.isoWhiskerLeft (prodOpEquiv _).inverse
        (Functor.isoWhiskerRight (NatIso.op π) (yoneda.obj (GY.obj Q)))).symm ≪≫
      Functor.curry.mapIso (Functor.isoWhiskerLeft ((prodOpEquiv _).inverse ⋙
        ((𝟭 (WeilComplex k₀ l X)).prod (upperStar f) ⋙ nativeConstructibleTensor k₀ l X).op) q) ≪≫
      Functor.curryObjProdComp (𝟭 (WeilComplex k₀ l X)).op (upperStar f).op
        ((prodOpEquiv _).inverse ⋙ (nativeConstructibleTensor k₀ l X).op ⋙
          yoneda.obj (GX.obj Q)) ≪≫
      Functor.isoWhiskerLeft (𝟭 (WeilComplex k₀ l X)).op
        (Functor.isoWhiskerRight (nativeConstructibleTensorCurryYonedaIso (GX.obj Q) hX)
          ((Functor.whiskeringLeft _ _ _).obj (upperStar f).op)) ≪≫
      Functor.isoWhiskerLeft DX (upperStarDerivedLowerStarAdjunction f).compYonedaIso.symm
  exact ⟨(Yoneda.fullyFaithful.whiskeringRight _).preimageIso e⟩

