/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefDualFormulaScalarTranspose.CoefRelativeTraceRestriction
import WeilConjectures.SixFunctors.CoefDualFormulaScalarTranspose.CoefEtaleRelativeTraceRestrictionMate
import WeilConjectures.SixFunctors.CoefDualFormulaScalarTranspose.CoefEtaleRelativeTraceRestrictionCompositor
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import WeilConjectures.AlgebraicGeometry.Proper.ProperFiniteCoefficientExtension

/-! # Quotient compatibility of the etale relative structural trace -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefDualFormulaScalarTranspose

private theorem trace_coefficient_assembly
    {XA YA SA XB YB SB : Type*}
    [Category XA] [Category YA] [Category SA]
    [Category XB] [Category YB] [Category SB]
    (F : XA ⥤ YA) (G : YA ⥤ SA) (H : XA ⥤ SA)
    (F' : XB ⥤ YB) (G' : YB ⥤ SB) (H' : XB ⥤ SB)
    (TX : XA ⥤ XB) (TY : YA ⥤ YB) (TS : SA ⥤ SB)
    (a : F ⋙ G ≅ H) (b : F' ⋙ G' ≅ H')
    (cx : H ⋙ TS ⟶ TX ⋙ H') (cy : G ⋙ TS ⟶ TY ⋙ G')
    {R : SB ⥤ YB} (adj : G' ⊣ R)
    (W : XA) (V : YA) (W' : XB) (N : SA) (N' : SB)
    (ex : H.obj W ⟶ N) (ey : G.obj V ⟶ N)
    (ex' : H'.obj W' ⟶ N') (q : TS.obj N ⟶ N')
    (ux : TX.obj W ⟶ W') (uy : TY.obj V ⟶ R.obj N')
    (t : F.obj W ⟶ V) (t' : F'.obj W' ⟶ R.obj N')
    (cf : TY.obj (F.obj W) ⟶ F'.obj (TX.obj W))
    (ht : G.map t ≫ ey = a.hom.app W ≫ ex)
    (ht' : G'.map t' ≫ adj.counit.app N' = b.hom.app W' ≫ ex')
    (hx : cx.app W ≫ H'.map ux ≫ ex' = TS.map ex ≫ q)
    (hy : cy.app V ≫ G'.map uy ≫ adj.counit.app N' = TS.map ey ≫ q)
    (hc : cy.app (F.obj W) ≫ G'.map cf ≫ b.hom.app (TX.obj W) =
      TS.map (a.hom.app W) ≫ cx.app W)
    [Epi (cy.app (F.obj W))] :
    TY.map t ≫ uy = cf ≫ F'.map ux ≫ t' := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  apply (cancel_epi (cy.app (F.obj W))).1
  have hn := cy.naturality t
  dsimp only [Functor.comp_map] at hn
  have hb := b.hom.naturality ux
  dsimp only [Functor.comp_map] at hb
  calc
    cy.app (F.obj W) ≫ G'.map (TY.map t) ≫ G'.map uy ≫ adj.counit.app N' =
        TS.map (G.map t) ≫ TS.map ey ≫ q := by
          rw [← reassoc_of% hn]
          rw [hy]
    _ = TS.map (a.hom.app W) ≫ TS.map ex ≫ q := by
      rw [← TS.map_comp_assoc, ht, TS.map_comp]
      simp only [Category.assoc]
    _ = cy.app (F.obj W) ≫ G'.map cf ≫ G'.map (F'.map ux) ≫
        G'.map t' ≫ adj.counit.app N' := by
      rw [ht', reassoc_of% hb, reassoc_of% hc]
      rw [hx]

private theorem compact_comparison_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (q : A →+* B) {X Y : Scheme.{u}} [IsNoetherian Y]
    {f : X ⟶ Y} (c : Compactification f) (K : Etale.DerivedCategoryModule A X) :
    IsIso (Etale.ExceptionalCoefficients.compactSupportMap q c K) := by
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  have := (Etale.properFiniteCoefficientExtension q c.g).1
    ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj K)
  unfold Etale.ExceptionalCoefficients.compactSupportMap
  infer_instance

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)

/-- The etale relative structural trace commutes with adjacent quotient restriction.
Source: blueprint Step 2, absolute counit transposition, and Stacks 0F7J, 0GL6
(blueprint: lem-coef-etale-relative-trace-restriction).
Proof: compare both sides through the scalar Hom bijection at Y. The left side has
adjunct T(trace_{n+1}) followed by the dualizing comparison at Y; the right side has
adjunct c_f, compact support of the comparison at X and trace_n
(lem-coef-etale-relative-trace-restriction-mate). Their equality follows from the
defining counit identities of the traces and dualizing comparisons, naturality, the
coefficient compositor square (lem-coef-etale-relative-trace-restriction-compositor)
and cancellation of the compact-support coefficient map at Y, which is invertible by
proper finite coefficient extension (lem-asd-proper-finite-coefficient-extension).
No flatness of the quotient and no faithfulness of derived restriction is used. -/
theorem finiteEtaleTrace_restriction (n : ℕ) :
    finiteEtaleTrace D l E f c (n + 1) ≫
        finiteDualizingEtaleTransition l E D Y n.le_succ =
      (Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (finiteDualizingCoeff l E (n + 1))) c).map
          (finiteDualizingEtaleTransition l E D X n.le_succ) ≫
        finiteEtaleSupportRestriction (finiteDualizingQuotient l E n.le_succ) c
          ⟨finiteDualizingEtaleTerm l E D X n, finiteEtaleDualizing_plus D l E X n⟩ ≫
        (Sheaf.derivedRestrictScalars Y.smallEtaleTopology
          (finiteDualizingQuotient l E n.le_succ)).map (finiteEtaleTrace D l E f c n) := by
  let := c.hasCompactification
  let := (finiteDualizingCompactification D X).hasCompactification
  let := (finiteDualizingCompactification D Y).hasCompactification
  let q := finiteDualizingQuotient l E n.le_succ
  let F := Etale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (finiteDualizingCoeff l E (n + 1))) c
  let F' := Etale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) c
  let G := finiteDualizingEtaleSupport l E D Y (n + 1)
  let G' := finiteDualizingEtaleSupport l E D Y n
  let H := finiteDualizingEtaleSupport l E D X (n + 1)
  let H' := finiteDualizingEtaleSupport l E D X n
  let TX := Etale.scalarExtension q X
  let TY := Etale.scalarExtension q Y
  let TS := Etale.scalarExtension q (Spec (.of D.k))
  let W := finiteDualizingEtaleTerm l E D X (n + 1)
  let V := finiteDualizingEtaleTerm l E D Y (n + 1)
  let W' := finiteDualizingEtaleTerm l E D X n
  let N := Etale.constantComplex (finiteDualizingCoeff l E (n + 1)) (Spec (.of D.k))
  let N' := Etale.constantComplex (finiteDualizingCoeff l E n) (Spec (.of D.k))
  let ex := finiteDualizingEtaleCounit l E D X (n + 1)
  let ey := finiteDualizingEtaleCounit l E D Y (n + 1)
  let ex' := finiteDualizingEtaleCounit l E D X n
  let u := (Etale.ExceptionalCoefficients.unitIso q (Spec (.of D.k))).hom
  let ux := finiteDualizingEtaleComparison l E D X n.le_succ
  let uy := finiteDualizingEtaleComparison l E D Y n.le_succ
  let t := finiteEtaleTrace D l E f c (n + 1)
  let t' := finiteEtaleTrace D l E f c n
  let a := finiteSupportComposition (finiteDualizingCoeff l E (n + 1)) f
    (Y ↘ Spec (.of D.k)) (X ↘ Spec (.of D.k))
    (CategoryTheory.comp_over f (Spec (.of D.k))) c
    (finiteDualizingCompactification D Y) (finiteDualizingCompactification D X)
  let b := finiteSupportComposition (finiteDualizingCoeff l E n) f
    (Y ↘ Spec (.of D.k)) (X ↘ Spec (.of D.k))
    (CategoryTheory.comp_over f (Spec (.of D.k))) c
    (finiteDualizingCompactification D Y) (finiteDualizingCompactification D X)
  let cx := Etale.compactScalarMap q (finiteDualizingCompactification D X)
  let cy := Etale.compactScalarMap q (finiteDualizingCompactification D Y)
  let cf := Etale.ExceptionalCoefficients.compactSupportMap q c W
  have ht : G.map t ≫ ey = a.hom.app W ≫ ex :=
    ((finiteDualizingEtaleAdjunction l E D Y (n + 1)).homEquiv _ _).symm_apply_apply _
  have ht' : G'.map t' ≫ (finiteDualizingEtaleAdjunction l E D Y n).counit.app N' =
      b.hom.app W' ≫ ex' :=
    ((finiteDualizingEtaleAdjunction l E D Y n).homEquiv _ _).symm_apply_apply _
  have hix := compact_comparison_isIso q (finiteDualizingCompactification D X) W
  have hiy := compact_comparison_isIso q (finiteDualizingCompactification D Y) V
  have him := compact_comparison_isIso q (finiteDualizingCompactification D Y) (F.obj W)
  have : IsIso (cy.app (F.obj W)) := him
  have hx : cx.app W ≫ H'.map ux ≫ ex' = TS.map ex ≫ u := by
    have he := ((finiteDualizingEtaleAdjunction l E D X n).homEquiv _ _).symm_apply_apply
      (Etale.ExceptionalCoefficients.comparisonInverse q
        (finiteDualizingCompactification D X) W ≫ TS.map ex ≫ u)
    change H'.map ux ≫ ex' = _ at he
    rw [he]
    simp only [cx, Etale.compactScalarMap, Etale.ExceptionalCoefficients.comparisonInverse,
      dif_pos hix]
    exact IsIso.hom_inv_id_assoc _ _
  have hy : cy.app V ≫ G'.map uy ≫
      (finiteDualizingEtaleAdjunction l E D Y n).counit.app N' = TS.map ey ≫ u := by
    have he := ((finiteDualizingEtaleAdjunction l E D Y n).homEquiv _ _).symm_apply_apply
      (Etale.ExceptionalCoefficients.comparisonInverse q
        (finiteDualizingCompactification D Y) V ≫ TS.map ey ≫ u)
    change G'.map uy ≫ (finiteDualizingEtaleAdjunction l E D Y n).counit.app N' = _ at he
    rw [he]
    simp only [cy, Etale.compactScalarMap, Etale.ExceptionalCoefficients.comparisonInverse,
      dif_pos hiy]
    exact IsIso.hom_inv_id_assoc _ _
  have hc : cy.app (F.obj W) ≫ G'.map cf ≫ b.hom.app (TX.obj W) =
      TS.map (a.hom.app W) ≫ cx.app W :=
    finiteEtaleTrace_restriction_compositor D l E f c n
  have htrace : TY.map t ≫ uy = cf ≫ F'.map ux ≫ t' :=
    trace_coefficient_assembly F G H F' G' H' TX TY TS a b cx cy
      (finiteDualizingEtaleAdjunction l E D Y n) W V W' N N' ex ey ex' u ux uy t t' cf
      ht ht' hx hy hc
  let adj := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars Y.smallEtaleTopology q)
  apply (adj.homEquiv (F.obj W) (finiteDualizingEtaleTerm l E D Y n)).symm.injective
  rw [finiteEtaleTrace_restriction_mate D l E f c n]
  change (adj.homEquiv _ _).symm
    (t ≫ adj.homEquiv _ _ uy) = cf ≫ F'.map ux ≫ t'
  erw [adj.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
  exact htrace

end WeilConjectures.CoefDualFormulaScalarTranspose
