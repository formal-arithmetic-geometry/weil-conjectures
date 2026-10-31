/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BrownTowerBoundedTransport

import WeilConjectures.AlgebraicGeometry.BrownTowerGeometricTransport
import WeilConjectures.CategoryTheory.ExactDerivedAdjunctionBounds
import Mathlib.CategoryTheory.HomCongr
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Finite evaluation and bounded site transport

Source: integral-adjunction proof, first Hom display; Zheng Lemmas 4.10, 5.16, 5.22
(blueprint: lem-pur-brown-tower-finite-site-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genCtorIdx false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u a av b bv x xv y yv
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
namespace BrownTowerComparison

section CategoricalTransport
variable {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
  {X : Type x} [Category.{xv} X] {Y : Type y} [Category.{yv} Y]
  {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
  {U : A ⥤ X} {V : X ⥤ A} (ax : U ⊣ V)
  {W : B ⥤ Y} {Z : Y ⥤ B} (ay : W ⊣ Z)
  (P : X ⥤ Y) (d : F ⋙ W ⟶ U ⋙ P)

private theorem transport_bijective (C : Y) (K : X)
    [IsIso (ax.counit.app K)] [IsIso (d.app (V.obj K))]
    [IsIso (d.app (G.obj (Z.obj C)))]
    (hfull : Function.Bijective
      (U.map : (V.obj K ⟶ G.obj (Z.obj C)) → _)) :
    Function.Bijective (fun a : K ⟶ U.obj (G.obj (Z.obj C)) ↦
      P.map a ≫ inv (d.app (G.obj (Z.obj C))) ≫
        W.map (adj.counit.app (Z.obj C)) ≫ ay.counit.app C) := by
  let e₁ := Iso.homCongr (asIso (ax.counit.app K)).symm
    (Iso.refl (U.obj (G.obj (Z.obj C))))
  let e₂ := (Equiv.ofBijective
    (U.map : (V.obj K ⟶ G.obj (Z.obj C)) → _) hfull).symm
  let e₃ := (adj.homEquiv (V.obj K) (Z.obj C)).symm
  let e₄ := (ay.homEquiv (F.obj (V.obj K)) C).symm
  let i : W.obj (F.obj (V.obj K)) ≅ P.obj K :=
    asIso (d.app (V.obj K)) ≪≫ P.mapIso (asIso (ax.counit.app K))
  let e₅ := Iso.homCongr i (Iso.refl C)
  let e := e₁.trans (e₂.trans (e₃.trans (e₄.trans e₅)))
  have he (a : K ⟶ U.obj (G.obj (Z.obj C))) :
      e a = P.map a ≫ inv (d.app (G.obj (Z.obj C))) ≫
        W.map (adj.counit.app (Z.obj C)) ≫ ay.counit.app C := by
    let b := e₂ (e₁ a)
    have hb : U.map b = ax.counit.app K ≫ a := by
      exact (Equiv.ofBijective U.map hfull).apply_symm_apply (e₁ a) |>.trans
        (by simp [e₁, Iso.homCongr])
    have hd := d.naturality b
    dsimp only [Functor.comp_obj, Functor.comp_map] at hd
    apply (cancel_epi (P.map (ax.counit.app K))).mp
    apply (cancel_epi (d.app (V.obj K))).mp
    dsimp [e, e₅, e₄, e₃, i, Iso.homCongr]
    simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.comp_id,
      Category.assoc]
    rw [← Category.assoc (P.map (ax.counit.app K)), ← P.map_comp,
      IsIso.hom_inv_id, P.map_id, Category.id_comp]
    rw [IsIso.hom_inv_id_assoc]
    rw [← Category.assoc (P.map (ax.counit.app K)), ← P.map_comp, ← hb]
    rw [← Category.assoc (d.app (V.obj K)) (P.map (U.map b)), ← hd]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rfl
  simpa only [← he] using e.bijective

private theorem transport_counit_naturality
    {C C' : Y} (b : C ⟶ C')
    [IsIso (d.app (G.obj (Z.obj C)))]
    [IsIso (d.app (G.obj (Z.obj C')))] :
    P.map (U.map (G.map (Z.map b))) ≫ inv (d.app (G.obj (Z.obj C'))) ≫
        W.map (adj.counit.app (Z.obj C')) ≫ ay.counit.app C' =
      inv (d.app (G.obj (Z.obj C))) ≫ W.map (adj.counit.app (Z.obj C)) ≫
        ay.counit.app C ≫ b := by
  apply (cancel_epi (d.app (G.obj (Z.obj C)))).mp
  simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  have hd := d.naturality (G.map (Z.map b))
  dsimp only [Functor.comp_obj, Functor.comp_map] at hd
  rw [← hd]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  have hn := adj.counit.naturality (Z.map b)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [← Category.assoc (W.map _), ← W.map_comp, hn]
  simp only [Functor.map_comp, Category.assoc]
  exact congrArg (fun f ↦ W.map (adj.counit.app (Z.obj C)) ≫ f)
    (ay.counit.naturality b)

private theorem transport_brown_formula
    (C : Y) (K : X)
    [IsIso (d.app (G.obj (Z.obj C)))]
    (a : K ⟶ U.obj (G.obj (Z.obj C)))
    (b : V.obj K ⟶ G.obj (Z.obj C))
    (hb : ax.counit.app K ≫ a = U.map b) :
    d.app (V.obj K) ≫ P.map (ax.counit.app K) ≫ P.map a ≫
        inv (d.app (G.obj (Z.obj C))) ≫ W.map (adj.counit.app (Z.obj C)) ≫
          ay.counit.app C =
      W.map ((adj.homEquiv _ _).symm b) ≫ ay.counit.app C := by
  rw [← Category.assoc (P.map (ax.counit.app K)), ← Functor.map_comp, hb]
  have hd := d.naturality b
  dsimp only [Functor.comp_obj, Functor.comp_map] at hd
  rw [← Category.assoc (d.app _) (P.map _) _, ← hd]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc, Adjunction.homEquiv_counit,
    Functor.map_comp]

private theorem transport_counit_formula (C : Y)
    [IsIso (d.app (G.obj (Z.obj C)))] :
    d.app (G.obj (Z.obj C)) ≫
        (inv (d.app (G.obj (Z.obj C))) ≫ W.map (adj.counit.app (Z.obj C)) ≫
          ay.counit.app C) =
      W.map (adj.counit.app (Z.obj C)) ≫ ay.counit.app C := by
  simp only [IsIso.hom_inv_id_assoc]

private theorem transport_scalar (C : Y)
    [IsIso (d.app (G.obj (Z.obj C)))]
    (s : Z.obj C ⟶ Z.obj C) (ar : C ⟶ C)
    (h : ay.counit.app C ≫ ar = W.map s ≫ ay.counit.app C) :
    P.map (U.map (G.map s)) ≫ inv (d.app (G.obj (Z.obj C))) ≫
        W.map (adj.counit.app (Z.obj C)) ≫ ay.counit.app C =
      inv (d.app (G.obj (Z.obj C))) ≫ W.map (adj.counit.app (Z.obj C)) ≫
        ay.counit.app C ≫ ar := by
  apply (cancel_epi (d.app (G.obj (Z.obj C)))).mp
  simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  have hd := d.naturality (G.map s)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hd
  rw [← hd]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  have hn := adj.counit.naturality s
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [← Category.assoc (W.map _), ← W.map_comp, hn]
  simp only [Functor.map_comp, Category.assoc]
  rw [← h]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem map_bijective_of_unit (K L : A) [IsIso (ax.unit.app L)] :
    Function.Bijective (U.map : (K ⟶ L) → _) := by
  let e := (Iso.homCongr (Iso.refl K) (asIso (ax.unit.app L))).trans
    (ax.homEquiv K (U.obj L)).symm
  have he (f : K ⟶ L) : e f = U.map f := by
    apply (ax.homEquiv K (U.obj L)).injective
    dsimp only [e, Equiv.trans_apply]
    erw [(ax.homEquiv K (U.obj L)).apply_symm_apply]
    rw [Iso.homCongr_apply]
    simp only [Iso.refl_inv, Category.id_comp, asIso_hom]
    simpa only [Adjunction.homEquiv_unit, Functor.id_map, Functor.comp_map]
      using ax.unit.naturality f
  have hf : (U.map : (K ⟶ L) → _) = fun f ↦ e f :=
    funext (fun f ↦ (he f).symm)
  rw [hf]
  exact e.bijective

private theorem exactImageBound
    {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{x} A]
    {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{y} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (FD : DerivedCategory A ⥤ DerivedCategory B)
    (fac : DerivedCategory.Q ⋙ FD ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (K : DerivedCategory A) (n : ℤ) [K.IsGE n] : (FD.obj K).IsGE n := by
  let e : FD ≅ F.mapDerivedCategory := Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ))
    (DerivedCategory.Q ⋙ FD) (DerivedCategory.Q ⋙ F.mapDerivedCategory)
    FD F.mapDerivedCategory (fac ≪≫ F.mapDerivedCategoryFactors.symm)
  have := F.isGE_mapDerivedCategory_obj K n
  exact DerivedCategory.TStructure.t.isGE_of_iso (e.app K).symm n

private theorem exactImageAdditive
    {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{x} A]
    {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{y} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (FD : DerivedCategory A ⥤ DerivedCategory B)
    (fac : DerivedCategory.Q ⋙ FD ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) : FD.Additive := by
  let e : FD ≅ F.mapDerivedCategory := Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ))
    (DerivedCategory.Q ⋙ FD) (DerivedCategory.Q ⋙ F.mapDerivedCategory)
    FD F.mapDerivedCategory (fac ≪≫ F.mapDerivedCategoryFactors.symm)
  exact Functor.additive_of_iso e.symm

end CategoricalTransport

section BuildTransport
attribute [local instance 5000] proSystemDerived proLevelDerived
  strictEtaleSystemDerived strictEtaleLevelDerived
variable {O : Type (u + 1)} [CommRing O] {t : O}
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  {S : StrictEtaleCompactSupport.{u} O t c} {G : EtaleTowerBrownAdjunction.{u} S}
  {H : FiniteEvaluation.{u} S G}

private theorem geometricCompactIso (D : GeometricTransport.{u} S G H)
    (C : DerivedCategory.{u + 2} (ProSystem Y O t)) (hC : D.siteY.Origin C)
    (hn : IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2}
      (J := Scheme.ProEt.topology Y) O t D.siteY.proEvaluation C)
    (hc : ∀ n, FiniteCoefficientAdjoints.ctf (Ring O t n) Y
      ((D.siteY.realization n).derived.obj ((D.siteY.proEvaluation.evaluation n).obj C)))
    (hb : ∃ a : ℤ, ∀ n, ((finiteExceptional.{u} S G H D.siteX D.siteY n).obj
      ((D.siteY.proEvaluation.evaluation n).obj C)).IsGE a) :
    IsIso (D.compactComparison.app (G.right.obj (D.siteY.direct.obj C))) := by
  obtain ⟨a, ha⟩ := hb
  exact D.compact_iso _ ⟨a, (D.bound C hC hn hc a ha).1⟩

private def geometricCounit (D : GeometricTransport.{u} S G H)
    (C : DerivedCategory.{u + 2} (ProSystem Y O t)) (hC : D.siteY.Origin C)
    (hn : IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2}
      (J := Scheme.ProEt.topology Y) O t D.siteY.proEvaluation C)
    (hc : ∀ n, FiniteCoefficientAdjoints.ctf (Ring O t n) Y
      ((D.siteY.realization n).derived.obj ((D.siteY.proEvaluation.evaluation n).obj C)))
    (hb : ∃ a : ℤ, ∀ n, ((finiteExceptional.{u} S G H D.siteX D.siteY n).obj
      ((D.siteY.proEvaluation.evaluation n).obj C)).IsGE a) :
    D.compact.functor.obj (D.siteX.inverse.obj
      (G.right.obj (D.siteY.direct.obj C))) ⟶ C :=
  have := geometricCompactIso D C hC hn hc hb
  inv (D.compactComparison.app (G.right.obj (D.siteY.direct.obj C))) ≫
    D.siteY.inverse.map (G.adjunction.counit.app (D.siteY.direct.obj C)) ≫
      D.siteY.adjunction.counit.app C

private theorem geometricFullyFaithfulX (D : GeometricTransport.{u} S G H) (K L :
    DerivedCategory.{u + 2} (strictEtaleCoefficientSystem X O t))
    (_hK : ∃ a : ℤ, K.IsGE a) (hL : ∃ a : ℤ, L.IsGE a) :
    Function.Bijective (D.siteX.inverse.map : (K ⟶ L) → _) := by
  have := D.unit_iso_X L hL
  exact map_bijective_of_unit D.siteX.adjunction K L

private theorem geometricFullyFaithfulY (D : GeometricTransport.{u} S G H) (K L :
    DerivedCategory.{u + 2} (strictEtaleCoefficientSystem Y O t))
    (_hK : ∃ a : ℤ, K.IsGE a) (hL : ∃ a : ℤ, L.IsGE a) :
    Function.Bijective (D.siteY.inverse.map : (K ⟶ L) → _) := by
  have := D.unit_iso_Y L hL
  exact map_bijective_of_unit D.siteY.adjunction K L

private theorem geometricCompactBound
    (D : GeometricTransport.{u} S G H) (K : DerivedCategory.{u + 2} (ProSystem X O t))
    (a : ℤ) (hK : K.IsGE a) : (D.compact.functor.obj K).IsGE a := by
  have := hK
  have := D.compact.openAdditive
  have := D.compact.openExact.1
  have := D.compact.openExact.2
  have := D.compact.properImage.systemExact.1
  have := D.compact.properImage.systemExact.2
  have : (D.compact.derivedOpen.obj K).IsGE a :=
    exactImageBound D.compact.openExtension D.compact.derivedOpen
      D.compact.openFactors K a
  exact exactDerivedAdjunction_isGE D.compact.properImage.inverse
    D.compact.properDerived.inverse D.compact.properDerived.inverseFactors
    D.compact.properDerived.adjunction (D.compact.derivedOpen.obj K) a

private theorem geometricHom_bijective (D : GeometricTransport.{u} S G H)
    (C : DerivedCategory.{u + 2} (ProSystem Y O t)) (hC : D.siteY.Origin C)
    (hn : IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2}
      (J := Scheme.ProEt.topology Y) O t D.siteY.proEvaluation C)
    (hc : ∀ n, FiniteCoefficientAdjoints.ctf (Ring O t n) Y
      ((D.siteY.realization n).derived.obj ((D.siteY.proEvaluation.evaluation n).obj C)))
    (hb : ∃ a : ℤ, ∀ n, ((finiteExceptional.{u} S G H D.siteX D.siteY n).obj
      ((D.siteY.proEvaluation.evaluation n).obj C)).IsGE a)
    (B : DerivedCategory.{u + 2} (ProSystem X O t)) (hB : D.siteX.Origin B) :
    Function.Bijective (fun a : B ⟶ D.siteX.inverse.obj
      (G.right.obj (D.siteY.direct.obj C)) ↦
        D.compact.functor.map a ≫ geometricCounit D C hC hn hc hb) := by
  have := D.counit_iso_X B hB
  have hVB : ∃ a : ℤ, (D.siteX.direct.obj B).IsGE a := by
    obtain ⟨a, ha⟩ := hB.1
    exact ⟨a, D.siteX.direct_bound B a ha⟩
  have := D.compact_iso _ hVB
  have := geometricCompactIso D C hC hn hc hb
  have hGC : ∃ a : ℤ, (G.right.obj (D.siteY.direct.obj C)).IsGE a := by
    obtain ⟨a, ha⟩ := hb
    exact ⟨a, (D.bound C hC hn hc a ha).1⟩
  exact transport_bijective G.adjunction D.siteX.adjunction D.siteY.adjunction
    D.compact.functor D.compactComparison C B (geometricFullyFaithfulX D _ _ hVB hGC)

private def geometricEvaluation (D : GeometricTransport.{u} S G H) (n : ℕ) :
    D.siteY.direct ⋙ G.right ⋙ D.siteX.inverse ⋙ D.siteX.proEvaluation.evaluation n ≅
      D.siteY.proEvaluation.evaluation n ⋙
        finiteExceptional.{u} S G H D.siteX D.siteY n :=
  isoWhiskerLeft D.siteY.direct
    (isoWhiskerLeft G.right (D.siteX.comparison.evaluation.inverseEvaluation n) ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (H.evaluation n) _ ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (D.siteY.comparison.evaluation.directEvaluation n) _ ≪≫
    Functor.associator _ _ _

private def geometricTransportData
    (D : GeometricTransport.{u} S G H) : TransportData.{u} S G H where
  finite := D.finite
  siteX := D.siteX
  siteY := D.siteY
  compact := D.compact
  compactComparison := D.compactComparison
  compactEvaluation := D.compactEvaluation
  evaluation := geometricEvaluation D
  counit := geometricCounit D
  hom C hC hn hc hb B hB := Equiv.ofBijective
    (fun a ↦ D.compact.functor.map a ≫ geometricCounit D C hC hn hc hb)
    (geometricHom_bijective D C hC hn hc hb B hB)

private theorem geometricTransport (D : GeometricTransport.{u} S G H) :
    Transport.{u} S G H (geometricTransportData D) (finite := D.finite) := by
  have : ∀ n : ℕ, Finite (Ring O t n) := D.finite
  refine {
    realizationX := D.realizationX
    realizationY := D.realizationY
    compactComparison_evaluation := D.compactComparison_evaluation
    compact_iso := D.compact_iso
    unit_iso_X := D.unit_iso_X
    unit_iso_Y := D.unit_iso_Y
    counit_iso_X := D.counit_iso_X
    counit_iso_Y := D.counit_iso_Y
    fullyFaithful_X := geometricFullyFaithfulX D
    fullyFaithful_Y := geometricFullyFaithfulY D
    compact_bound := geometricCompactBound D
    bound := D.bound
    evaluation_def := by
      intro n C
      simp only [geometricTransportData, geometricEvaluation, Iso.trans_hom,
        isoWhiskerLeft_hom, isoWhiskerRight_hom, Iso.symm_hom, NatTrans.comp_app,
        whiskerLeft_app, whiskerRight_app, associator_hom_app, associator_inv_app,
        Category.id_comp, Category.comp_id, Functor.comp_obj, Functor.comp_map, Category.assoc]
    counit_formula := ?_
    hom_formula := ?_
    hom_brown := ?_
    hom_natural_left := ?_
    hom_natural_right := ?_
    hom_additive := ?_
    hom_linear := ?_ }
  · intro C hC hn hc hb
    have := geometricCompactIso D C hC hn hc hb
    exact transport_counit_formula G.adjunction D.siteY.adjunction
      D.compact.functor D.compactComparison C
  · intros
    rfl
  · intro C hC hn hc hb B hB a b hab
    have := geometricCompactIso D C hC hn hc hb
    exact transport_brown_formula G.adjunction D.siteX.adjunction D.siteY.adjunction
      D.compact.functor D.compactComparison C B a b hab
  · intro C hC hn hc hb B hB B' hB' b a
    change D.compact.functor.map (b ≫ a) ≫ _ = _
    rw [Functor.map_comp, Category.assoc]
    rfl
  · intro C hC hn hc hb C' hC' hn' hc' hb' b B hB a
    have := geometricCompactIso D C hC hn hc hb
    have := geometricCompactIso D C' hC' hn' hc' hb'
    change D.compact.functor.map (a ≫ _) ≫ _ = _
    rw [Functor.map_comp, Category.assoc]
    simpa only [geometricTransportData, Equiv.ofBijective_apply, geometricCounit,
      Category.assoc] using congrArg (fun f ↦ D.compact.functor.map a ≫ f)
      (transport_counit_naturality G.adjunction D.siteY.adjunction
        D.compact.functor D.compactComparison b)
  · intro C hC hn hc hb B hB a b
    let openImage := D.compact.openImage
    let properImage := D.compact.properImage
    have := openImage.systemExact.1
    have := openImage.systemExact.2
    have := properImage.systemExact.1
    have := properImage.systemExact.2
    have : D.compact.openDerived.inverse.Additive :=
      exactImageAdditive openImage.inverse _ D.compact.openDerived.inverseFactors
    have : D.compact.derivedOpen.Additive :=
      D.compact.derivedOpenAdjunction.left_adjoint_additive
    have : D.compact.properDerived.inverse.Additive :=
      exactImageAdditive properImage.inverse _ D.compact.properDerived.inverseFactors
    have : D.compact.properDerived.direct.Additive :=
      D.compact.properDerived.adjunction.right_adjoint_additive
    have : D.compact.functor.Additive := by
      change (D.compact.derivedOpen ⋙ D.compact.properDerived.direct).Additive
      infer_instance
    change D.compact.functor.map (a + b) ≫ _ = _
    rw [Functor.map_add, Preadditive.add_comp]
    rfl
  · intro C hC hn hc hb B hB a r ar har
    have := geometricCompactIso D C hC hn hc hb
    change D.compact.functor.map (a ≫ _) ≫ _ = _
    rw [Functor.map_comp, Category.assoc, ← G.rightLinear]
    simpa only [geometricTransportData, Equiv.ofBijective_apply, geometricCounit,
      Category.assoc] using congrArg (fun f ↦ D.compact.functor.map a ≫ f)
      (transport_scalar G.adjunction D.siteY.adjunction D.compact.functor
        D.compactComparison C ((G.scalarY.derived r).app (D.siteY.direct.obj C)) ar har)

end BuildTransport

/-- The finite evaluation and bounded site transport of the chosen Brown adjunction.
Source: Zheng Construction 4.1, Lemma 4.10, Construction 5.15, Lemmas 5.16 and 5.22;
proof Steps 1--12 (blueprint: lem-pur-brown-tower-finite-site-comparison).

Proof plan (the complete DAG argument):
1. All schemes in the chosen compactification are Noetherian: a field is Noetherian since its
only ideals are zero and the whole field, finite-type schemes over it are Noetherian, and the
proper finite-type factor $g$ makes $\overline X$ Noetherian too. Thus the ordinary etale
compact-support and scalar comparison hypotheses apply. Write $L_n^T=LE_n^T$,
$G=G^{\mathrm{et}}$ and $F=F^{\mathrm{et}}$ until Step 10. Let $a_n:e_nF\cong F_ne_n$ be the
canonical evaluated proper/open comparison. The Brown-adjunction node supplies this comparison,
compatible with transitions, on all unbounded objects. Define $\chi_{n,P}:L_n^YF_nP\to FL_n^XP$
by the $L_n^Y\dashv e_n$ transpose of $F_nP\cong F_ne_nL_n^XP\xrightarrow{a_n^{-1}}e_nFL_n^XP$.
The first isomorphism uses $e_nL_n^X\cong1$ from the evaluation-extension formula. This defines
a natural transformation in the derived category of whole systems; it is the meaning of the
identity transpose in the statement.
2. For $q\le n$ let $T_{nq}=-\otimes^L_{A_n}A_q$. Under the evaluation formulas, $e_q\chi_n$ is
the canonical compact-support coefficient map $q_{nq}:T_{nq}F_n\to F_qT_{nq}$. To check the
named arrow, the $L_n$-transpose at $q$ first tensors the level-$n$ identity and then follows
the transition of $FL_nP$. The transition formula for derived direct image is its coefficient
counit mate, and extension by zero acts termwise. Thus this is exactly the proper coefficient
counit mate followed by the open balancing map defining $q_{nq}$. This calculation uses the
actual transition/Hom formulas, not faithfulness of evaluations. The unbounded scalar-coherence
node says every $q_{nq}$ is invertible, without quotient flatness. For $q>n$ both sides evaluate
to zero. Joint conservativity therefore makes $\chi_n$ invertible on all $P$.
3. For $P\in D(X_{\mathrm{et}},A_n)$ and arbitrary $Q$, compose the natural bijections
$$\operatorname{Hom}(P,e_nGQ)\cong\operatorname{Hom}(L_n^XP,GQ)\cong\operatorname{Hom}(FL_n^XP,Q
)\cong\operatorname{Hom}(L_n^YF_nP,Q)\cong\operatorname{Hom}(F_nP,e_nQ)\cong\operatorname{Hom}(P
,f_n^\times
e_nQ).$$ The middle map precomposes with $\chi_{n,P}$. Yoneda gives a unique natural isomorphism
$\theta_{n,Q}:e_nGQ\cong f_n^\times e_nQ$. Here Yoneda is used only between the two represented
Hom functors, precisely the fully faithful representable statement. Every operation is natural
on derived morphisms. There is no constructibility restriction in this calculation.
4. Let $\epsilon:FG\to1$ and $\epsilon_n:F_nf_n^\times\to1$ be the chosen counits. Apply the Hom
chain to the identity of $e_nGQ$. Its finite transpose is $$\epsilon_{n,e_nQ}\circ
F_n(\theta_{n,Q})=e_n(\epsilon_Q)\circ a_{n,GQ}^{-1}.$$ Indeed the first evaluation transpose is
the extension counit $L_n e_nGQ\to GQ$; naturality of $a_n$ and the defining transpose of
$\chi_n$ cancel the extension unit/counit by a triangle identity. This proves compatibility with
the evaluated counit for the specified, rather than an arbitrary, isomorphism. Equivalently, the
mate of $\chi_n^{-1}:FL_n^X\to L_n^YF_n$ under $F\dashv G$, $F_n\dashv f_n^\times$ is
$L_n^Xf_n^\times\to GL_n^Y$, and the same Hom chain gives its evaluation mate $\theta_n$.
5. For $m\ge n$ put $T_X=-\otimes^L_{A_m}A_n$, $T_Y=-\otimes^L_{A_m}A_n$ and use $q:T_YF_m\cong
F_nT_X$ from Step 2. Transpose the level-$m$ counit identity of Step 4 along the actual
transition of $Q$. The extension-adjunction formula for $\sigma_{mn}$ identifies precomposition
with that map with $t^{GQ}_{mn}\circ T_X(-)$. Naturality of the whole-system counit $\epsilon$
then gives $$\epsilon_{n,Q_n}\circ F_n(\theta_{n,Q}\,t^{GQ}_{mn}) =t^Q_{mn}\circ
T_Y(\epsilon_{m,Q_m})\circ q^{-1}_{f_m^\times Q_m}\circ F_n(T_X\theta_{m,Q}).$$ Both sides are
maps $F_nT_X e_mGQ\to Q_n$. By injectivity of the finite adjunction transpose, the actual
transition, in $\theta$ coordinates, is $$T_X f_m^\times Q_m\xrightarrow{b_{mn}}f_n^\times
T_YQ_m\xrightarrow{f_n^\times(t^Q_{mn})}f_n^\times Q_n,$$ where $b_{mn}$ is the transpose of
$T_Y\epsilon_m\circ q^{-1}$. This argument works for arbitrary $Q$; it does not claim the
ordinary unbounded $b_{mn}$ is invertible.
6. These identifications respect $m\to n\to r$: use the actual composition law for $\sigma$ and
the tensor associators, then apply the same successive adjunction transposes to $\epsilon$. Mate
pasting says the successive transposes equal the transpose of the pasted map; identities give
identities. In particular the transition equations of Step 5 are equalities of natural
transformations obtained from the whole-system counit and extension adjunctions. Their cocycle
is the cocycle of those actual transitions (with the scalar restriction compositors inserted),
not an inference from equality of evaluations of two unrelated system morphisms.
7. Put $U_T=\nu_{T,\bullet}^*$ and $V_T=R\nu_{T,\bullet,*}$. The system comparison gives
$U_T\dashv V_T$, evaluation compatibility and the counit isomorphism $U_TV_TM\cong M$ for
bounded-below etale-origin $M$. For any bounded-below etale system $H$, the evaluated unit $H\to
V_TU_TH$ is the finite site unit, hence invertible by the finite site-comparison theorem. Joint
conservativity makes the system unit invertible. Thus $U_T$ is fully faithful on all such
bounded-below objects and morphisms, with inverse $V_T$ on the bounded-below origin subcategory.
The exact pullback $U_T$ preserves bounds; $V_T$ preserves lower bounds by the system
comparison. For the stated $C$, $Q=V_YC$ is consequently bounded below and normalized, and
$U_YQ\cong C$.
8. By Step 3 and the evaluation formula for $V_Y$, $\nu_X^*e_nGQ\cong\nu_X^* f_n^\times
R\nu_{Y,*}C_n=Rf_n^!C_n$. The finite-adjoint-comparison node defines exactly this transported
exceptional functor and gives its counit normalization and invertible quotient mates on the
finite constructible finite-Tor inputs. Exact inverse image reflects every cohomological lower
bound: $H^i(\nu_X^*Z)=\nu_X^*H^i(Z)$, and full faithfulness on degree-zero objects implies
$\nu_X^*H=0$ only if $H=0$ (the identity of $H$ must vanish). This applies even when $Z$ is
unbounded. The assumed common lower bound on the displayed exceptional images is therefore a
common lower bound on every $e_nGQ$. The system-evaluation bound criterion implies $GQ$ has that
lower bound. Hence $N=U_XGQ$ is bounded below, with the asserted finite evaluations.
9. Transport Step 5 through $\nu^*$ and $U_YQ\cong C$. The specified finite compact-support
scalar/site square identifies $q$ with the finite pro-etale projection, and the finite-adjoint-
comparison node identifies the counits. Taking the same finite adjunction transpose therefore
identifies the transported transition with $Rf_n^!(t^C_{mn})\circ b_{mn,C_m}$. The etale
witnesses $Q_m=R\nu_{Y,*}C_m$ are bounded constructible finite-Tor: the finite-ring
constructible-origin theorem and the Noetherian Tor-comparison equivalence identify this class
on the two sites. The same applies to $e_mGQ$ using its exceptional-image identification and
finite-adjoint preservation. Hence the coefficient-compatibility theorem applies to these etale
inputs and their pro-etale images: all schemes are separated finite type over the given
characteristic-$p$ field, and $\ell\ne p$. It allows nonflat quotients. Both $b_{mn,C_m}$ and
$t^C_{mn}$ are invertible. Thus each adjoint transition of $N$ is invertible: $N$ is normalized.
Counits and quotient cocycles have the specified normalization because the finite comparison
fixes the counit equation and the mate composition law.
10. Now write $F^p=Rg_{*,\bullet}^{\mathrm{proet}}j_{!,\bullet}^{\mathrm{proet}}$. There is an
actual natural comparison $d:U_YF\to F^pU_X$: paste the system direct-image mate for the square
$\nu_{\bar X}^*g_{\mathrm{et}}^*\cong g_{\mathrm{proet}}^*\nu_Y^*$ with the open comparison.
These are whole-system transformations furnished by semilinear derived sections and mate
pasting. The open comparison is formed termwise, from the sheaf comparison and exact extension
by zero. At each $n$, $d_H$ is the named bounded-below compact-support site isomorphism for
$H_n$. Thus for bounded-below $H$, conservativity makes $d_H$ invertible. All its objects are
bounded below: open extension and inverse image are exact, while right-derived direct images
preserve lower bounds. This constructs $d$, including its action on morphisms, before checking
its invertibility.
11. Define the actual transported counit by
$$F^pN=F^pU_XGQ\xrightarrow{d_{GQ}^{-1}}U_YFGQ\xrightarrow{U_Y\epsilon_Q}U_YQ\xrightarrow{\epsil
on^{\nu}_C}C.$$
Every arrow is a map of derived systems. The evaluation/counit compatibilities already proved
identify its evaluations with the finite counits. For any bounded-below origin system $B$, put
$H=V_XB$, so $B\cong U_XH$. Full faithfulness from Step 7 and Step 10 give
$$\operatorname{Hom}(B,N)\cong\operatorname{Hom}(H,GQ)\cong\operatorname{Hom}(FH,Q)\cong\operato
rname{Hom}(U_YFH,C)\cong\operatorname{Hom}(F^pB,C).$$
The middle bijection is the chosen Brown adjunction. The others are induced by the system unit,
counit and $d$; consequently they are natural on morphisms and their inverse sends the identity
of $N$ to the displayed counit. All inverse images, coefficient evaluations and comparison maps
commute with multiplication by $r\in R$ componentwise, and their derived maps retain that
equality. The Brown Hom bijection is $R$-linear by its scalar-transpose normalization. Hence
this transported bijection is $R$-linear. Only bounded-below origin inputs were used for site
transport. -/
theorem brownTowerFiniteSiteComparison
    (p l : ℕ) [Fact p.Prime] [Fact l.Prime] (_hpl : p ≠ l)
    (k : Type u) [Field k] [CharP k p]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (t : Padic.coefficientExtensionIntegers l E)
    (_ht : Ideal.span ({t} : Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (c : Compactification f)
    (S : StrictEtaleCompactSupport (Padic.coefficientExtensionIntegers l E) t c)
    (G : EtaleTowerBrownAdjunction S) :
    ∃ H : FiniteEvaluation S G, ∃ D : TransportData S G H,
      Transport S G H D (finite := D.finite) := by
  -- Choose finite and geometric comparisons together to retain their normalization.
  obtain ⟨H, ⟨D⟩⟩ := brownTowerGeometricTransport_exists p l _hpl k E t _ht f c S G
  exact ⟨H, geometricTransportData D, geometricTransport D⟩

end BrownTowerComparison
end AlgebraicGeometry
