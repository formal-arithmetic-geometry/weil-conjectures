/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalIntegralBoundaryPullback
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence

/-! # The ordinary integral supported-source exchange -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
namespace IntegralSourceExchange

/-- The integral constant sheaf used in the ordinary exchange.
Source: blueprint diagonal coefficient changes (3).
(blueprint: lem-diagonal-integral-source-exchange). -/
abbrev integralConstant (X : Scheme.{u}) :=
  (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

private def integralConstantComparison (X : Scheme.{u}) :=
  ((((constantSheafAdj X.smallEtaleTopology Ab.{u + 1}
    (Scheme.Etale.isTerminalMkId X)).comp (comparisonAdjunction Ab.{u + 1} X)).ofNatIsoRight
      ((Scheme.toProEt X).sheafPushforwardContinuousCompSheafSectionsObjIso
        Ab.{u + 1} X.smallEtaleTopology (Scheme.ProEt.topology X)
        (op (Scheme.Etale.mk (𝟙 X))))).leftAdjointUniq
    (constantSheafAdj (Scheme.ProEt.topology X) Ab.{u + 1}
      (Scheme.ProEt.isTerminalMkId X)))

/-- The canonical inverse-image comparison of a commutative scheme square.
Source: blueprint diagonal coefficient changes (3).
(blueprint: lem-diagonal-integral-source-exchange). -/
def integralSquare {D D' Z Z' : Scheme.{u}}
    (i : D ⟶ Z) (i' : D' ⟶ Z') (g : Z' ⟶ Z) (w : D' ⟶ D)
    (sq : CommSq w i' i g) :
    upperStar Ab.{u + 1} g ⋙ upperStar Ab.{u + 1} i' ≅
      upperStar Ab.{u + 1} i ⋙ upperStar Ab.{u + 1} w :=
  (upperStarComp Ab.{u + 1} i' g).symm ≪≫
    eqToIso (congrArg (upperStar Ab.{u + 1}) sq.w.symm) ≪≫
    upperStarComp Ab.{u + 1} w i

/-- The abelian closed exchange on integral constants, using the canonical inverse-image square.
Source: blueprint diagonal coefficient changes (3).
(blueprint: lem-diagonal-integral-source-exchange). -/
def integralExchange {D D' Z Z' : Scheme.{u}}
    (i : D ⟶ Z) (i' : D' ⟶ Z') (g : Z' ⟶ Z) (w : D' ⟶ D)
    (sq : CommSq w i' i g) :=
  (upperStarLowerStarAdjunction Ab.{u + 1} i').homEquiv _ _
    ((integralSquare i i' g w sq).hom.app
        ((lowerStar Ab.{u + 1} i).obj (integralConstant D)) ≫
      (upperStar Ab.{u + 1} w).map
        ((upperStarLowerStarAdjunction Ab.{u + 1} i).counit.app (integralConstant D)) ≫
      Scheme.proEtaleConstantInverseImageMap w Ab.{u + 1}
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))

namespace ConstantProof
universe u₁ u₂ u₃ v₁ v₂ v₃ w
variable {C₁ : Type u₁} [Category.{v₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] {C₃ : Type u₃} [Category.{v₃} C₃]
  {D : Type w} [Category D]
  (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂)
  (J₃ : GrothendieckTopology C₃)
  [HasWeakSheafify J₁ D] [HasWeakSheafify J₂ D] [HasWeakSheafify J₃ D]

end ConstantProof


private theorem comparison_counit {D Z : Scheme.{u}} (i : D ⟶ Z)
    (F : Sheaf D.smallEtaleTopology Ab.{u + 1}) :
    (upperStar Ab.{u + 1} i).map
        ((lowerStarComparisonUpperStarBaseChange i Ab.{u + 1}).app F) ≫
      (upperStarLowerStarAdjunction Ab.{u + 1} i).counit.app
        ((comparisonUpperStar Ab.{u + 1} D).obj F) =
    (comparisonUpperStarCompUpperStarIso Ab.{u + 1} i).hom.app _ ≫
      (comparisonUpperStar Ab.{u + 1} D).map
        ((Etale.upperStarLowerStarAdjunction Ab.{u + 1} i).counit.app F) := by
  have h := mateEquiv_counit_symm
    (Etale.upperStarLowerStarAdjunction Ab.{u + 1} i)
    (upperStarLowerStarAdjunction Ab.{u + 1} i)
    (lowerStarComparisonUpperStarBaseChange i Ab.{u + 1}) F
  have hi := iterated_mateEquiv_conjugateEquiv_symm
    (Etale.upperStarLowerStarAdjunction Ab.{u + 1} i)
    (upperStarLowerStarAdjunction Ab.{u + 1} i)
    (comparisonAdjunction Ab.{u + 1} Z)
    (comparisonAdjunction Ab.{u + 1} D)
    (lowerStarCompComparisonLowerStarIso i Ab.{u + 1}).inv
  unfold lowerStarComparisonUpperStarBaseChange at h
  rw [hi] at h
  exact h

private theorem comparison_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Sheaf Z.smallEtaleTopology Ab.{u + 1}) :
    (comparisonUpperStarCompUpperStarIso Ab.{u + 1} (f ≫ g)).hom.app F ≫
        (comparisonUpperStar Ab.{u + 1} X).map
          ((Etale.upperStarComp Ab.{u + 1} f g).hom.app F) =
      (upperStarComp Ab.{u + 1} f g).hom.app _ ≫
        (upperStar Ab.{u + 1} f).map
          ((comparisonUpperStarCompUpperStarIso Ab.{u + 1} g).hom.app F) ≫
        (comparisonUpperStarCompUpperStarIso Ab.{u + 1} f).hom.app
          ((Etale.upperStar Ab.{u + 1} g).obj F) := by
  have h := (comparison_pullback_coherent.2.1).2.1 X Y Z f g F
  change (comparisonUpperStar Ab.{u + 1} X).map
      ((Etale.upperStarComp Ab.{u + 1} f g).hom.app F) ≫
    (comparisonUpperStarCompUpperStarIso Ab.{u + 1} f).inv.app
      ((Etale.upperStar Ab.{u + 1} g).obj F) ≫
    (upperStar Ab.{u + 1} f).map
      ((comparisonUpperStarCompUpperStarIso Ab.{u + 1} g).inv.app F) =
    (comparisonUpperStarCompUpperStarIso Ab.{u + 1} (f ≫ g)).inv.app F ≫
      (upperStarComp Ab.{u + 1} f g).hom.app _ at h
  apply (cancel_epi
    ((comparisonUpperStarCompUpperStarIso Ab.{u + 1} (f ≫ g)).inv.app F)).mp
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← reassoc_of% h]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]

section SquareProof
attribute [local irreducible] upperStar Etale.upperStar comparisonUpperStar
  upperStarComp Etale.upperStarComp comparisonUpperStarCompUpperStarIso

private theorem comp_transport {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (w : h = f ≫ g) :
    Etale.upperStarComp Ab.{u + 1} f g h w =
      eqToIso (congrArg (Etale.upperStar Ab.{u + 1}) w) ≪≫
        Etale.upperStarComp Ab.{u + 1} f g := by
  subst h
  simp

private theorem pro_square_iso {D D' Z Z' : Scheme.{u}}
    (i : D ⟶ Z) (i' : D' ⟶ Z') (g : Z' ⟶ Z) (gD : D' ⟶ D)
    (sq : CommSq gD i' i g) :
    integralSquare i i' g gD sq =
      (upperStarComp Ab.{u + 1} i' g).symm ≪≫
        eqToIso (congrArg (upperStar Ab.{u + 1}) sq.w.symm) ≪≫
        upperStarComp Ab.{u + 1} gD i := by
  unfold integralSquare
  rfl

private theorem comparison_comp_forward {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Sheaf Z.smallEtaleTopology Ab.{u + 1}) :
    (upperStar Ab.{u + 1} f).map
        ((comparisonUpperStarCompUpperStarIso Ab.{u + 1} g).hom.app F) ≫
      (comparisonUpperStarCompUpperStarIso Ab.{u + 1} f).hom.app
        ((Etale.upperStar Ab.{u + 1} g).obj F) =
    (upperStarComp Ab.{u + 1} f g).inv.app
        ((comparisonUpperStar Ab.{u + 1} Z).obj F) ≫
      (comparisonUpperStarCompUpperStarIso Ab.{u + 1} (f ≫ g)).hom.app F ≫
      (comparisonUpperStar Ab.{u + 1} X).map
        ((Etale.upperStarComp Ab.{u + 1} f g).hom.app F) := by
  let C := Ab.{u + 1}
  exact iso_factor ((upperStarComp C f g).hom.app ((comparisonUpperStar C Z).obj F))
    ((upperStarComp C f g).inv.app ((comparisonUpperStar C Z).obj F))
    (Iso.inv_hom_id_app (upperStarComp C f g) ((comparisonUpperStar C Z).obj F))
    ((comparisonUpperStarCompUpperStarIso C (f ≫ g)).hom.app F)
    ((comparisonUpperStar C X).map ((Etale.upperStarComp C f g).hom.app F))
    ((upperStar C f).map ((comparisonUpperStarCompUpperStarIso C g).hom.app F) ≫
      (comparisonUpperStarCompUpperStarIso C f).hom.app ((Etale.upperStar C g).obj F))
    (comparison_comp f g F)


-- Keep the diagram calculation abstract: reducing components of the concrete
-- sheaf-pullback functors during equality transport unfolds large Kan extensions.
-- L₁, L₂ are the etale path g then i'; L₁', L₂' are i then gD.
-- R denotes the corresponding pro-etale paths, and K the site comparisons.
private theorem etale_square_iso {D D' Z Z' : Scheme.{u}}
    (i : D ⟶ Z) (i' : D' ⟶ Z') (g : Z' ⟶ Z) (gD : D' ⟶ D)
    (sq : CommSq gD i' i g) :
    Etale.squareUpperStarIso Ab.{u + 1} sq =
      (Etale.upperStarComp Ab.{u + 1} i' g).symm ≪≫
        (eqToIso (congrArg (Etale.upperStar Ab.{u + 1}) sq.w)).symm ≪≫
        Etale.upperStarComp Ab.{u + 1} gD i := by
  rw [Etale.squareUpperStarIso, comp_transport i' g (gD ≫ i) sq.w]
  simp only [Iso.trans_symm, Iso.trans_assoc]

private abbrev cartierSquareData {D D' Z Z' : Scheme.{u}}
    (i : D ⟶ Z) (i' : D' ⟶ Z') (g : Z' ⟶ Z) (gD : D' ⟶ D)
    (sq : CommSq gD i' i g) :
    ClosedSquareData
      (Sheaf Z.smallEtaleTopology Ab.{u + 1})
      (Sheaf Z'.smallEtaleTopology Ab.{u + 1})
      (Sheaf D.smallEtaleTopology Ab.{u + 1})
      (Sheaf D'.smallEtaleTopology Ab.{u + 1})
      (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (Sheaf (Scheme.ProEt.topology Z') Ab.{u + 1})
      (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1})
      (Sheaf (Scheme.ProEt.topology D') Ab.{u + 1}) where
  L₁ := Etale.upperStar Ab.{u + 1} g
  L₂ := Etale.upperStar Ab.{u + 1} i'
  L₁' := Etale.upperStar Ab.{u + 1} i
  L₂' := Etale.upperStar Ab.{u + 1} gD
  K₀ := comparisonUpperStar Ab.{u + 1} Z
  K₁ := comparisonUpperStar Ab.{u + 1} Z'
  K₁' := comparisonUpperStar Ab.{u + 1} D
  K₂ := comparisonUpperStar Ab.{u + 1} D'
  R₁ := upperStar Ab.{u + 1} g
  R₂ := upperStar Ab.{u + 1} i'
  R₁' := upperStar Ab.{u + 1} i
  R₂' := upperStar Ab.{u + 1} gD
  c₁ := comparisonUpperStarCompUpperStarIso Ab.{u + 1} g
  c₂ := comparisonUpperStarCompUpperStarIso Ab.{u + 1} i'
  c₁' := comparisonUpperStarCompUpperStarIso Ab.{u + 1} i
  c₂' := comparisonUpperStarCompUpperStarIso Ab.{u + 1} gD
  L := Etale.upperStar Ab.{u + 1} (i' ≫ g)
  L' := Etale.upperStar Ab.{u + 1} (gD ≫ i)
  T := upperStar Ab.{u + 1} (i' ≫ g)
  T' := upperStar Ab.{u + 1} (gD ≫ i)
  c := comparisonUpperStarCompUpperStarIso Ab.{u + 1} (i' ≫ g)
  c' := comparisonUpperStarCompUpperStarIso Ab.{u + 1} (gD ≫ i)
  a := Etale.upperStarComp Ab.{u + 1} i' g
  a' := Etale.upperStarComp Ab.{u + 1} gD i
  p := upperStarComp Ab.{u + 1} i' g
  p' := upperStarComp Ab.{u + 1} gD i
  e := (eqToIso (congrArg (Etale.upperStar Ab.{u + 1}) sq.w)).symm
  d := eqToIso (congrArg (upperStar Ab.{u + 1}) sq.w.symm)
  se := Etale.squareUpperStarIso Ab.{u + 1} sq
  sp := integralSquare i i' g gD sq


private theorem cartier_law_ha {D D' Z Z' : Scheme.{u}}
    (i : D ⟶ Z) (i' : D' ⟶ Z') (g : Z' ⟶ Z) (gD : D' ⟶ D)
    (sq : CommSq gD i' i g) :
    let s := cartierSquareData i i' g gD sq;
    ∀ F, s.R₂.map (s.c₁.hom.app F) ≫ s.c₂.hom.app (s.L₁.obj F) =
    s.p.inv.app (s.K₀.obj F) ≫ s.c.hom.app F ≫ s.K₂.map (s.a.hom.app F) := by
  exact comparison_comp_forward i' g

private theorem cartier_law_hb {D D' Z Z' : Scheme.{u}}
    (i : D ⟶ Z) (i' : D' ⟶ Z') (g : Z' ⟶ Z) (gD : D' ⟶ D)
    (sq : CommSq gD i' i g) :
    let s := cartierSquareData i i' g gD sq;
    ∀ F, s.c'.hom.app F ≫ s.K₂.map (s.a'.hom.app F) =
    s.p'.hom.app (s.K₀.obj F) ≫ s.R₂'.map (s.c₁'.hom.app F) ≫ s.c₂'.hom.app (s.L₁'.obj F) := by
  exact comparison_comp gD i

private theorem cartier_law_ht {D D' Z Z' : Scheme.{u}}
    (i : D ⟶ Z) (i' : D' ⟶ Z') (g : Z' ⟶ Z) (gD : D' ⟶ D)
    (sq : CommSq gD i' i g) :
    let s := cartierSquareData i i' g gD sq;
    s.c.hom ≫ Functor.whiskerRight s.e.hom s.K₂ =
      Functor.whiskerLeft s.K₀ s.d.hom ≫ s.c'.hom := by
  exact comparison_transport_nat
    (Etale.upperStar Ab.{u + 1}) (upperStar Ab.{u + 1})
    (comparisonUpperStar Ab.{u + 1} Z)
    (comparisonUpperStar Ab.{u + 1} D')
    (fun t ↦ comparisonUpperStarCompUpperStarIso Ab.{u + 1} t) sq.w

private theorem cartier_law_he {D D' Z Z' : Scheme.{u}}
    (i : D ⟶ Z) (i' : D' ⟶ Z') (g : Z' ⟶ Z) (gD : D' ⟶ D)
    (sq : CommSq gD i' i g) :
    let s := cartierSquareData i i' g gD sq;
    s.se = s.a.symm ≪≫ s.e ≪≫ s.a' := by
  exact etale_square_iso i i' g gD sq

private theorem cartier_law_hp {D D' Z Z' : Scheme.{u}}
    (i : D ⟶ Z) (i' : D' ⟶ Z') (g : Z' ⟶ Z) (gD : D' ⟶ D)
    (sq : CommSq gD i' i g) :
    let s := cartierSquareData i i' g gD sq;
    s.sp = s.p.symm ≪≫ s.d ≪≫ s.p' := by
  exact pro_square_iso i i' g gD sq

private theorem cartierSquareLaws {D D' Z Z' : Scheme.{u}}
    (i : D ⟶ Z) (i' : D' ⟶ Z') (g : Z' ⟶ Z) (gD : D' ⟶ D)
    (sq : CommSq gD i' i g) : ClosedSquareLaws (cartierSquareData i i' g gD sq) where
  ha := cartier_law_ha i i' g gD sq
  hb := cartier_law_hb i i' g gD sq
  ht := cartier_law_ht i i' g gD sq
  he := cartier_law_he i i' g gD sq
  hp := cartier_law_hp i i' g gD sq


end SquareProof

private lemma comparison_constant_inverse
    (T : Scheme.{u}) (M : Ab.{u + 1}) :
  let D := Ab.{u + 1};
    (integralConstantComparison T).hom.app M =
      ConstantProof.constantInverse T.smallEtaleTopology (Scheme.ProEt.topology T)
        (Scheme.toProEt T)
        (comparisonAdjunction D T) M := by
  let D := Ab.{u + 1}
  let ae := constantSheafAdj T.smallEtaleTopology D (Scheme.Etale.isTerminalMkId T)
  let ap := constantSheafAdj (Scheme.ProEt.topology T) D (Scheme.ProEt.isTerminalMkId T)
  let p := comparisonAdjunction D T
  let e := (Scheme.toProEt T).sheafPushforwardContinuousCompSheafSectionsObjIso D
    T.smallEtaleTopology (Scheme.ProEt.topology T) (op (Scheme.Etale.mk (𝟙 T)))
  let ac := (ae.comp p).ofNatIsoRight e
  apply (ac.homEquiv _ _).injective
  have hc := Adjunction.homEquiv_leftAdjointUniq_hom_app ac ap M
  change ac.homEquiv _ _ ((integralConstantComparison T).hom.app M) =
    ap.unit.app M at hc
  rw [hc]
  unfold ConstantProof.constantInverse
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  change _ = ae.homEquiv _ _ (p.homEquiv _ _ ((p.homEquiv _ _).symm _)) ≫ _
  rw [Equiv.apply_symm_apply]
  simp only [Adjunction.homEquiv_apply, ae, ap, constantSheafAdj,
    Adjunction.comp_unit_app, constantPresheafAdj_unit_app,
    sheafificationAdjunction_unit_app, Category.id_comp]
  change (toSheafify (Scheme.ProEt.topology T)
      ((Functor.const (Scheme.ProEt T)ᵒᵖ).obj M)).app
        (op ((Scheme.toProEt T).obj (Scheme.Etale.mk (𝟙 T)))) =
    (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj M)).app
      (op (Scheme.Etale.mk (𝟙 T))) ≫
        (ConstantProof.constantDirect T.smallEtaleTopology (Scheme.ProEt.topology T)
          (Scheme.toProEt T) M).hom.app (op (Scheme.Etale.mk (𝟙 T)))
  exact (ConstantProof.constantDirect_unit T.smallEtaleTopology (Scheme.ProEt.topology T)
    (Scheme.toProEt T) M (op (Scheme.Etale.mk (𝟙 T)))).symm

private lemma etale_constant_inverse
    {X Y : Scheme.{u}} (h : X ⟶ Y) (M : Ab.{u + 1}) :
  let D := Ab.{u + 1};
    (Scheme.upperStarConstantSheafIso D h).hom.app M =
      ConstantProof.constantInverse Y.smallEtaleTopology X.smallEtaleTopology
        h.Etale (Etale.upperStarLowerStarAdjunction D h) M := by
  let D := Ab.{u + 1}
  let ay := constantSheafAdj Y.smallEtaleTopology D terminalIsTerminal
  let ax := constantSheafAdj X.smallEtaleTopology D terminalIsTerminal
  let p := Etale.upperStarLowerStarAdjunction D h
  let d := Etale.lowerStarCompSheafSectionsTerminalIso D h
  let ac := (ay.comp p).ofNatIsoRight d
  apply (ac.homEquiv _ _).injective
  have hn := Adjunction.homEquiv_leftAdjointUniq_hom_app ac ax M
  change ac.homEquiv _ _ ((Scheme.upperStarConstantSheafIso D h).hom.app M) =
    ax.unit.app M at hn
  rw [hn]
  unfold ConstantProof.constantInverse
  conv_rhs => erw [transportedHom ay p d]
  simp only [Adjunction.homEquiv_apply, ax, ay, constantSheafAdj, Adjunction.comp_unit_app,
    constantPresheafAdj_unit_app, sheafificationAdjunction_unit_app,
    Category.id_comp, Category.assoc]
  change (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).app
      (op (⊤_ X.Etale)) =
    (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)).app
      (op (⊤_ Y.Etale)) ≫
      (ConstantProof.constantDirect Y.smallEtaleTopology X.smallEtaleTopology h.Etale M).hom.app
        (op (⊤_ Y.Etale)) ≫
      ((constantSheaf X.smallEtaleTopology D).obj M).obj.map
        (PreservesTerminal.iso h.Etale).inv.op
  rw [← Category.assoc, ConstantProof.constantDirect_unit]
  have hn := (toSheafify X.smallEtaleTopology
    ((Functor.const X.Etaleᵒᵖ).obj M)).naturality (PreservesTerminal.iso h.Etale).inv.op
  simpa only [constantSheaf, Functor.comp_obj, Functor.const_obj_map,
    Functor.const_obj_obj, Functor.op_obj, Category.id_comp] using hn

private theorem comparison_constants_general
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Ab.{u + 1}) :
  let D := Ab.{u + 1};
    (ProEtale.upperStar D f).map ((integralConstantComparison Y).hom.app M) ≫
        Scheme.proEtaleConstantInverseImageMap f D M =
      (comparisonUpperStarCompUpperStarIso D f).hom.app
          ((constantSheaf Y.smallEtaleTopology D).obj M) ≫
        (ProEtale.comparisonUpperStar D X).map
          ((Scheme.upperStarConstantSheafIso D f).hom.app
            M) ≫ (integralConstantComparison X).hom.app M := by
  let D := Ab.{u + 1}
  let ap := (ProEtale.comparisonAdjunction D Y).comp
    (Scheme.proEtaleSheafAdjunction f D)
  let ae := (Etale.upperStarLowerStarAdjunction D f).comp
    (ProEtale.comparisonAdjunction D X)
  let d := lowerStarCompComparisonLowerStarIso f D
  have hd (S : Sheaf (Scheme.ProEt.topology X) D) (W : Y.Etaleᵒᵖ) :
      ((d.inv.app S).hom.app W) = 𝟙 _ := by
    dsimp only [d, lowerStarCompComparisonLowerStarIso]
    change ((𝟙 _ ≫ S.obj.map (𝟙 _)) ≫ 𝟙 _) = 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
    exact S.obj.map_id _
  simp only [comparison_constant_inverse, etale_constant_inverse]
  change (ProEtale.upperStar D f).map _ ≫
      ConstantProof.constantInverse (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
        (Scheme.proEtaleBaseChange f) (upperStarLowerStarAdjunction D f) M = _
  apply (ap.homEquiv _ _).injective
  change _ = ap.homEquiv _ _
    (((conjugateIsoEquiv ap ae).symm d).inv.app _ ≫ _)
  have hm := ConstantProof.homEquiv_mate ap ae d.symm
    ((ProEtale.comparisonUpperStar D X).map
      (ConstantProof.constantInverse Y.smallEtaleTopology X.smallEtaleTopology f.Etale
        (Etale.upperStarLowerStarAdjunction D f) M) ≫
      ConstantProof.constantInverse X.smallEtaleTopology (Scheme.ProEt.topology X)
        (Scheme.toProEt X)
        (ProEtale.comparisonAdjunction D X) M)
  simp only [Iso.symm_symm_eq] at hm
  erw [hm]
  have hp := ConstantProof.constantInverse_composite_adjunct Y.smallEtaleTopology
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) (Scheme.toProEt Y)
    (Scheme.proEtaleBaseChange f)
    (ProEtale.comparisonAdjunction D Y) (Scheme.proEtaleSheafAdjunction f D)
    M
  have he := ConstantProof.constantInverse_composite_adjunct Y.smallEtaleTopology
    X.smallEtaleTopology (Scheme.ProEt.topology X) f.Etale (Scheme.toProEt X)
    (Etale.upperStarLowerStarAdjunction D f)
    (ProEtale.comparisonAdjunction D X) M
  erw [hp, he]
  apply ((sheafificationAdjunction Y.smallEtaleTopology D).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  apply NatTrans.ext
  funext W
  simp only [sheafificationAdjunction_unit_app, NatTrans.comp_app, Category.assoc]
  change (toSheafify Y.smallEtaleTopology
      ((Functor.const Y.Etaleᵒᵖ).obj M)).app W ≫
      (ConstantProof.constantDirect Y.smallEtaleTopology (Scheme.ProEt.topology Y)
        (Scheme.toProEt Y)
        M).hom.app W ≫
      (ConstantProof.constantDirect (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
        (Scheme.proEtaleBaseChange f)
        M).hom.app ((Scheme.toProEt Y).op.obj W) =
    (toSheafify Y.smallEtaleTopology
      ((Functor.const Y.Etaleᵒᵖ).obj M)).app W ≫
      (ConstantProof.constantDirect Y.smallEtaleTopology X.smallEtaleTopology f.Etale
        M).hom.app W ≫
      (ConstantProof.constantDirect X.smallEtaleTopology (Scheme.ProEt.topology X)
        (Scheme.toProEt X)
        M).hom.app (f.Etale.op.obj W) ≫
      ((d.inv.app ((constantSheaf (Scheme.ProEt.topology X) D).obj
        M)).hom.app W)
  rw [hd]
  rw [← Category.assoc, ConstantProof.constantDirect_unit, ConstantProof.constantDirect_unit,
    ← Category.assoc, ← Category.assoc, ConstantProof.constantDirect_unit,
    ConstantProof.constantDirect_unit]
  erw [Category.comp_id]
  rfl


private theorem comparison_constants {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar Ab.{u + 1} f).map
        (((integralConstantComparison Y).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom) ≫
      Scheme.proEtaleConstantInverseImageMap f Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} ℤ)) =
    (comparisonUpperStarCompUpperStarIso Ab.{u + 1} f).hom.app
        (Etale.supportedIntegralConstant Y) ≫
      (comparisonUpperStar Ab.{u + 1} X).map
        (((Scheme.upperStarConstantSheafIso Ab.{u + 1} f).app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom) ≫
      (((integralConstantComparison X).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom) := by
  exact comparison_constants_general f (AddCommGrpCat.of (ULift.{u + 1} ℤ))

private theorem integralConstantComparison_app (X : Scheme.{u}) :
    (integralConstantComparison X).app (AddCommGrpCat.of (ULift.{u + 1} ℤ)) =
      cartierIntegralConstantComparisonIso X := by
  rfl

private theorem integralSourceIso_hom {D Z : Scheme.{u}} (i : D ⟶ Z)
    [IsClosedImmersion i] :
    (cartierIntegralSourceIso i).hom = cartierIntegralSourceComparison i := by
  rfl

private theorem integralSource_cancel {D Z : Scheme.{u}} (i : D ⟶ Z)
    [IsClosedImmersion i] :
    (cartierIntegralSourceIso i).inv ≫ cartierIntegralSourceComparison i = 𝟙 _ := by
  exact (cartierIntegralSourceIso i).inv_hom_id

attribute [local irreducible] lowerStar Etale.upperStar Etale.lowerStar
  comparisonUpperStar integralConstantComparison cartierIntegralConstantComparisonIso
  cartierIntegralSourceComparison cartierIntegralSourceIso
  upperStarLowerStarAdjunction Etale.upperStarLowerStarAdjunction
  Functor.sheafPullbackConstruction.sheafPullback


private theorem source_counit {D Z : Scheme.{u}} (i : D ⟶ Z) :
    (upperStar Ab.{u + 1} i).map (cartierIntegralSourceComparison i) ≫
        (upperStarLowerStarAdjunction Ab.{u + 1} i).counit.app
          (integralConstant D) =
      (comparisonUpperStarCompUpperStarIso Ab.{u + 1} i).hom.app
          ((Etale.lowerStar Ab.{u + 1} i).obj
            (Etale.supportedIntegralConstant D)) ≫
        (comparisonUpperStar Ab.{u + 1} D).map
          ((Etale.upperStarLowerStarAdjunction Ab.{u + 1} i).counit.app
            (Etale.supportedIntegralConstant D)) ≫
        ((integralConstantComparison D).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom := by
  unfold cartierIntegralSourceComparison integralConstant
  rw [← integralConstantComparison_app, Functor.map_comp, Category.assoc]
  have hn := (upperStarLowerStarAdjunction Ab.{u + 1} i).counit.naturality
    (((integralConstantComparison D).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom)
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [hn, ← Category.assoc]
  simp only [Etale.supportedIntegralConstant, Functor.comp_obj]
  rw [comparison_counit, Category.assoc]


private theorem etale_exchange_counit {D D' Z Z' : Scheme.{u}}
    (i : D ⟶ Z) (i' : D' ⟶ Z') (g : Z' ⟶ Z) (gD : D' ⟶ D)
    (sq : CommSq gD i' i g) :
    (Etale.upperStar Ab.{u + 1} i').map
        (Etale.relativeExtensionExchange i i' g gD sq) ≫
      (Etale.upperStarLowerStarAdjunction Ab.{u + 1} i').counit.app
        (Etale.supportedIntegralConstant D') =
    (Etale.squareUpperStarIso Ab.{u + 1} sq).hom.app _ ≫
      (Etale.upperStar Ab.{u + 1} gD).map
        ((Etale.upperStarLowerStarAdjunction Ab.{u + 1} i).counit.app
          (Etale.supportedIntegralConstant D)) ≫
      ((Scheme.upperStarConstantSheafIso Ab.{u + 1} gD).app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom := by
  unfold Etale.relativeExtensionExchange
  rw [Functor.map_comp, Category.assoc]
  have hn := (Etale.upperStarLowerStarAdjunction Ab.{u + 1} i').counit.naturality
    (((Scheme.upperStarConstantSheafIso Ab.{u + 1} gD).app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom)
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [hn]
  have hb := Etale.upperStar_map_baseChangeMap_app_counit Ab.{u + 1} sq
    (Etale.supportedIntegralConstant D)
  simpa only [Category.assoc, Functor.comp_obj, Functor.id_obj,
    Etale.supportedIntegralConstant] using congrArg (fun t ↦ t ≫
    ((Scheme.upperStarConstantSheafIso Ab.{u + 1} gD).app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom) hb


-- The mate argument uses only square coherence, the two source-counit equations,
-- and compatibility of the constant maps. Work in abstract categories so that
-- associativity and naturality never unfold a concrete sheaf construction.
/-- Site comparison intertwines the two closed exchanges on constant modules.
Source: blueprint sk-lem-geo-cartier.proof.md, opening and final paragraphs
(blueprint: lem-diagonal-integral-source-exchange).

Proof: transpose both composites under the inverse-image/direct-image adjunction for i'.
Expand the source comparison as the mate of restriction commuting with direct image,
followed by the constant comparison. The defining counit-mate identity moves this
comparison across the counit. The inverse-image comparison is conjugate to the same
restriction square, so its composition law identifies the two inverse-image paths
around the commutative scheme square. Naturality moves the remaining constant map
past the comparison. Both transposes are consequently inverse-image commutation,
followed by the pullback of the counit for i and the constant map for gD. Injectivity
of the adjunction equivalence gives the equality. This argument does not use
Cartier ideals or Kummer classes; it applies also to empty schemes and identity maps.
-/
private theorem sourceComparison_closed_exchange
    {D D' Z Z' : Scheme.{u}} (i : D ⟶ Z) (i' : D' ⟶ Z')
    (g : Z' ⟶ Z) (gD : D' ⟶ D) (sq : CommSq gD i' i g) :
    (upperStar Ab.{u + 1} g).map (cartierIntegralSourceComparison i) ≫
        integralExchange i i' g gD sq =
      (comparisonUpperStarCompUpperStarIso Ab.{u + 1} g).hom.app
          ((Etale.lowerStar Ab.{u + 1} i).obj (Etale.supportedIntegralConstant D)) ≫
        (comparisonUpperStar Ab.{u + 1} Z').map
          (Etale.relativeExtensionExchange i i' g gD sq) ≫
        cartierIntegralSourceComparison i' := by
  unfold integralExchange
  exact closedExchange_mates (cartierSquareData i i' g gD sq)
    (Etale.lowerStar Ab.{u + 1} i)
    (Etale.lowerStar Ab.{u + 1} i')
    (lowerStar Ab.{u + 1} i)
    (lowerStar Ab.{u + 1} i')
    (upperStarLowerStarAdjunction Ab.{u + 1} i')
    (Etale.supportedIntegralConstant D) (Etale.supportedIntegralConstant D')
    (integralConstant D) (integralConstant D')
    ((Etale.upperStarLowerStarAdjunction Ab.{u + 1} i).counit.app _)
    ((Etale.upperStarLowerStarAdjunction Ab.{u + 1} i').counit.app _)
    ((upperStarLowerStarAdjunction Ab.{u + 1} i).counit.app _)
    (((integralConstantComparison D).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom)
    (((integralConstantComparison D').app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom)
    (((Scheme.upperStarConstantSheafIso Ab.{u + 1} gD).app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom)
    (Scheme.proEtaleConstantInverseImageMap gD Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (cartierIntegralSourceComparison i) (cartierIntegralSourceComparison i')
    (Etale.relativeExtensionExchange i i' g gD sq)
    (cartierSquareLaws i i' g gD sq)
    (source_counit i) (source_counit i')
    (comparison_constants gD) (etale_exchange_counit i i' g gD sq)


section InverseExchange
attribute [local irreducible] upperStar

private theorem sourceComparison_inverse_exchange
    {D D' Z Z' : Scheme.{u}} (i : D ⟶ Z) (i' : D' ⟶ Z')
    [IsClosedImmersion i] [IsClosedImmersion i']
    (g : Z' ⟶ Z) (gD : D' ⟶ D) (sq : CommSq gD i' i g) :
    (upperStar Ab.{u + 1} g).map (cartierIntegralSourceIso i).inv ≫
        (comparisonUpperStarCompUpperStarIso Ab.{u + 1} g).hom.app
          ((Etale.lowerStar Ab.{u + 1} i).obj (Etale.supportedIntegralConstant D)) ≫
        (comparisonUpperStar Ab.{u + 1} Z').map
          (Etale.relativeExtensionExchange i i' g gD sq) ≫
        (cartierIntegralSourceIso i').hom = integralExchange i i' g gD sq := by
  rw [integralSourceIso_hom, ← sourceComparison_closed_exchange i i' g gD sq,
    ← Functor.map_comp_assoc, integralSource_cancel,
    CategoryTheory.Functor.map_id, Category.id_comp]

end InverseExchange

/-- The transported integral boundary source is the canonical ordinary closed exchange.

Source: blueprint latest, diagonal coefficient changes (3), integral source pullback;
the site-comparison mate calculation for the closed exchange.
(blueprint: lem-diagonal-integral-source-exchange).

Proof: compare the two closed exchanges by transposing under the primed closed
adjunction. Coherence of comparison inverse image with scheme-map composition
identifies the square comparison. The comparison-counit equations and the
constant-sheaf comparison then identify the transposes. The comparison on
integral closed sources is invertible; cancel it and substitute the definition
of diagonalBoundarySource. This is an equality of ordinary abelian sheaf maps
and requires neither a reduction, a derived limit, nor invertibility of a prime. -/
theorem diagonalBoundarySource_exchange {Y Y' : Scheme.{u}}
    (v : diagonalSurface Y' ⟶ diagonalSurface Y)
    (w : ProjectiveLine Y' ⟶ ProjectiveLine Y)
    (sq : CommSq w (diagonalImmersion Y') (diagonalImmersion Y) v) :
    DiagonalCoefficients.diagonalBoundarySource v w sq =
      integralExchange (diagonalImmersion Y) (diagonalImmersion Y') v w sq := by
  exact sourceComparison_inverse_exchange
    (diagonalImmersion Y) (diagonalImmersion Y') v w sq

end IntegralSourceExchange
end AlgebraicGeometry.ProEtale
