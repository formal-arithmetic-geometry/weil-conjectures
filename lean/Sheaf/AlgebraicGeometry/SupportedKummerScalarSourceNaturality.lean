/-
Copyright (c) 2026 Bin Wu and The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary
public import WeilConjectures.SixFunctors.BaseChange.RestrictScalars

/-! # Naturality of normalized constant coefficient maps

Source: Stacks Project, sites-cohomology.tex, Tag 06YY, and etale-cohomology.tex,
Tag 03QP (blueprint: lem-asd-supported-constant-scalar-naturality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- The adjoint of the constant-sheaf pullback comparison. -/
private noncomputable def supportedTransition
    (Λ : Type (u + 1)) [CommRing Λ] (M : ModuleCat.{u + 1} Λ)
    {Y Z : Scheme.{u}} (g : Z ⟶ Y) :
    (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M ⟶
      (lowerStar (ModuleCat.{u + 1} Λ) g).obj
        ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
  (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app _ ≫
    (lowerStar (ModuleCat.{u + 1} Λ) g).map
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).hom.app M)

set_option backward.isDefEq.respectTransparency false in
/-- The transition preserves the sheafification generator at the terminal object.
This is the unit equation for uniqueness of left adjoints, followed by naturality. -/
private lemma supportedTransition_terminal
    (Λ : Type (u + 1)) [CommRing Λ] (M : ModuleCat.{u + 1} Λ)
    {Y Z : Scheme.{u}} (g : Z ⟶ Y) :
    (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)).app
        (Opposite.op (⊤_ Y.Etale)) ≫
      (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app _ ≫
        (lowerStar (ModuleCat.{u + 1} Λ) g).map
          ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).hom.app M)).hom).app
            (Opposite.op (⊤_ Y.Etale)) ≫
      ((lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} Λ) g).hom.app _) =
    (toSheafify Z.smallEtaleTopology ((Functor.const Z.Etaleᵒᵖ).obj M)).app
        (Opposite.op (⊤_ Z.Etale)) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (((constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
        terminalIsTerminal).comp
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g)).ofNatIsoRight
      (lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} Λ) g))
    (constantSheafAdj Z.smallEtaleTopology (ModuleCat.{u + 1} Λ) terminalIsTerminal) M
  change
    ((toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)).app
        (Opposite.op (⊤_ Y.Etale)) ≫
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app _).hom.app
        (Opposite.op (⊤_ Y.Etale))) ≫
      (lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} Λ) g).hom.app _ ≫
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).hom.app M).hom.app
        (Opposite.op (⊤_ Z.Etale)) = _ at h
  have hn := (lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} Λ) g).hom.naturality
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).hom.app M)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, Category.assoc]
  change
    ((lowerStar (ModuleCat.{u + 1} Λ) g).map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).hom.app M)).hom.app
          (Opposite.op (⊤_ Y.Etale)) ≫
      (lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} Λ) g).hom.app _ =
    (lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} Λ) g).hom.app _ ≫
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).hom.app M).hom.app
        (Opposite.op (⊤_ Z.Etale)) at hn
  exact (congrArg (fun k ↦
    (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)).app
      (Opposite.op (⊤_ Y.Etale)) ≫
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app _).hom.app
      (Opposite.op (⊤_ Y.Etale)) ≫ k) hn).trans (by
      simpa only [Category.assoc, constantSheafAdj, Adjunction.comp_unit_app,
        constantPresheafAdj_unit_app, Functor.constCompEvaluationObj_hom_app,
        Category.id_comp, sheafificationAdjunction_unit_app, Functor.comp_obj,
        evaluation, constantSheaf, sheafSections, Functor.flip, sheafToPresheaf] using h)

set_option backward.isDefEq.respectTransparency false in
/-- The transition preserves all constant-presheaf generators.
Transport the terminal-object equation along the unique map to the terminal object. -/
private lemma supportedTransition_generators
    (Λ : Type (u + 1)) [CommRing Λ] (M : ModuleCat.{u + 1} Λ)
    {Y Z : Scheme.{u}} (g : Z ⟶ Y) (U : Y.Etaleᵒᵖ) :
    (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)).app U ≫
      (supportedTransition Λ M g).hom.app U =
    (toSheafify Z.smallEtaleTopology ((Functor.const Z.Etaleᵒᵖ).obj M)).app
        (g.Etale.op.obj U) := by
  let CY := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  let CZ := (constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  let t : CY ⟶ (lowerStar (ModuleCat.{u + 1} Λ) g).obj CZ :=
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app _ ≫
      (lowerStar (ModuleCat.{u + 1} Λ) g).map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).hom.app M)
  let eY := toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)
  let eZ := toSheafify Z.smallEtaleTopology ((Functor.const Z.Etaleᵒᵖ).obj M)
  let a := (terminalIsTerminal.from U.unop).op
  let i := PreservesTerminal.iso g.Etale
  have ht := supportedTransition_terminal Λ M g
  change eY.app (Opposite.op (⊤_ Y.Etale)) ≫ t.hom.app _ ≫
    CZ.obj.map i.inv.op = eZ.app (Opposite.op (⊤_ Z.Etale)) at ht
  have ht' := congrArg (fun k ↦ k ≫ CZ.obj.map i.hom.op) ht
  simp only [Category.assoc, ← Functor.map_comp, ← op_comp,
    Iso.hom_inv_id, op_id] at ht'
  change eY.app (Opposite.op (⊤_ Y.Etale)) ≫
    t.hom.app (Opposite.op (⊤_ Y.Etale)) ≫ CZ.obj.map (𝟙 _) = _ at ht'
  rw [CZ.obj.map_id] at ht'
  have ht'' : eY.app (Opposite.op (⊤_ Y.Etale)) ≫ t.hom.app _ =
      eZ.app (Opposite.op (⊤_ Z.Etale)) ≫ CZ.obj.map i.hom.op := by
    exact (Category.comp_id _).symm.trans ((Category.assoc _ _ _).trans ht')
  have hY := eY.naturality a
  have hZ := eZ.naturality ((terminalIsTerminal.from (g.Etale.obj U.unop)).op)
  dsimp only [Functor.const_obj_map, Functor.const_obj_obj] at hY hZ
  simp only [Category.id_comp] at hY hZ
  have hn := t.hom.naturality a
  dsimp only [CY, CZ, constantSheaf, Functor.comp_obj] at hn ⊢
  change eY.app U ≫ t.hom.app U = eZ.app (g.Etale.op.obj U)
  rw [hY, Category.assoc, hn, ← Category.assoc, ht'']
  change eZ.app (Opposite.op (⊤_ Z.Etale)) ≫
    CZ.obj.map i.hom.op ≫ CZ.obj.map (g.Etale.map a.unop).op = _
  dsimp only [CZ, constantSheaf, Functor.comp_obj] at *
  rw [← Functor.map_comp, ← op_comp]
  have he : g.Etale.map a.unop ≫ i.hom =
      terminalIsTerminal.from (g.Etale.obj U.unop) := terminalIsTerminal.hom_ext _ _
  rw [he]
  exact hZ.symm

set_option backward.isDefEq.respectTransparency false in
/-- Normalized coefficient maps commute with the adjunction unit on constants.
Source: Stacks Project, sites-cohomology.tex, Tag 06YY, and etale-cohomology.tex,
Tag 03QP (blueprint: lem-asd-supported-constant-scalar-naturality).
Proof: the constant-sheaf transition sends each constant generator to the same
generator on the base change. Both composites therefore send r to the constant
section with value φ(r). The universal property of sheafification proves equality.
No flatness or finiteness hypothesis is needed. -/
theorem supported_kummer_scalar_source_naturality
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) {D T : Scheme.{u}} (i : D ⟶ T)
    (ηD : ordinaryFiniteConstant R D ⟶
      (Sheaf.restrictScalars D.smallEtaleTopology φ).obj (ordinaryFiniteConstant S D))
    (ηT : ordinaryFiniteConstant R T ⟶
      (Sheaf.restrictScalars T.smallEtaleTopology φ).obj (ordinaryFiniteConstant S T))
    (hD : ∀ (U : D.Etaleᵒᵖ) (r : R), ηD.hom.app U
      ((toSheafify D.smallEtaleTopology
        ((Functor.const D.Etaleᵒᵖ).obj (ModuleCat.of R R))).app U r) =
      (toSheafify D.smallEtaleTopology
        ((Functor.const D.Etaleᵒᵖ).obj (ModuleCat.of S S))).app U (φ r))
    (hT : ∀ (U : T.Etaleᵒᵖ) (r : R), ηT.hom.app U
      ((toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of R R))).app U r) =
      (toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of S S))).app U (φ r)) :
    ηT ≫ (Sheaf.restrictScalars T.smallEtaleTopology φ).map (supportedConstantUnit S i) =
      supportedConstantUnit R i ≫ (lowerStar (ModuleCat.{u + 1} R) i).map ηD ≫
        (lowerStarCompRestrictScalarsIso φ i).inv.app (ordinaryFiniteConstant S D) := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _
    ((Sheaf.restrictScalars T.smallEtaleTopology φ).obj
      ((lowerStar (ModuleCat.{u + 1} S) i).obj (ordinaryFiniteConstant S D))).property
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  have hR := ConcreteCategory.congr_hom
    (supportedTransition_generators R (ModuleCat.of R R) i U) r
  have hS := ConcreteCategory.congr_hom
    (supportedTransition_generators S (ModuleCat.of S S) i U) (φ r)
  change (supportedConstantUnit S i).hom.app U
      (ηT.hom.app U ((toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of R R))).app U r)) =
    ηD.hom.app (i.Etale.op.obj U)
      ((supportedConstantUnit R i).hom.app U
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of R R))).app U r))
  rw [hT]
  change (supportedTransition S (ModuleCat.of S S) i).hom.app U _ =
    ηD.hom.app (i.Etale.op.obj U)
      ((supportedTransition R (ModuleCat.of R R) i).hom.app U _)
  simp only [ModuleCat.comp_apply] at hR hS
  exact hS.trans ((congrArg (fun x ↦ ηD.hom.app (i.Etale.op.obj U) x) hR).trans
    (hD (i.Etale.op.obj U) r)).symm

end AlgebraicGeometry.Etale
