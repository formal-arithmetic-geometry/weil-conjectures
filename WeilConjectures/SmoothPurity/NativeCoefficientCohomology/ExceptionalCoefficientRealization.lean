/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CoefficientRealization.CoefficientRealizationData
public import WeilConjectures.SmoothPurity.NativeCoefficientCohomology.CoefficientEndpointObjects
public import WeilConjectures.WeilSheaf.LowerShriek

import WeilConjectures.SmoothPurity.NativeCoefficientCohomology.ExceptionalRealizationRightMate

/-! # Ordinary equivariant realization at the exceptional constant pair

This is an ordinary derived comparison, prior to choosing any cohomological degree.
The Tate endpoint is not part of this statement.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
attribute [local instance 1100] CategoryTheory.instOverClass
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.ConstantPurityFrobenius
namespace WeilConjectures.NativeCoefficientCohomology

variable (P : PurityFiniteSetting.{u})
  (X₀ : Over (Spec (.of P.field.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  [Fact (ringChar P.field.k₀ ≠ P.coefficients.l)]
  (c₀ : Compactification X₀.hom)
  (S : systems P.field P.coefficients.l P.coefficients.different P.coefficients.Qbar X₀)

attribute [local instance] nativeStructureOver pointFiniteType pointQuasiCompact
  pointSeparated pointMapSeparated pointMapFiniteType pointMapQuasiCompact
  sourceFiniteType sourceQuasiCompact targetFiniteType targetQuasiCompact
  geometricMapOver geometricMapSeparated geometricMapFiniteType geometricMapQuasiCompact
  sourceUnits targetUnits

/-- Transposing the normalized counit square forces the right comparison to
intertwine the actual inverse-exchange mate. -/
private theorem right_mate_intertwines
    {WX WY CX CY : Type*} [Category WX] [Category WY] [Category CX] [Category CY]
    (FW : WX ⥤ WY) (GW : WY ⥤ WX) (adjW : FW ⊣ GW)
    (F : CX ⥤ CY) (G : CY ⥤ CX) (adj : F ⊣ G)
    (Q : CX ⥤ CX) (T : CY ⥤ CY)
    (VX : WX ⥤ Endofunctor.IsoAlgebra Q)
    (VY : WY ⥤ Endofunctor.IsoAlgebra T)
    (a : FW ⋙ VY ⋙ Endofunctor.IsoAlgebra.forget T ≅
      (VX ⋙ Endofunctor.IsoAlgebra.forget Q) ⋙ F)
    (β : F ⋙ T ≅ Q ⋙ F)
    (ha : ∀ K : WX,
      F.map (VX.obj K).str.hom ≫ a.inv.app K =
        β.inv.app (VX.obj K).carrier ≫ T.map (a.inv.app K) ≫
          (VY.obj (FW.obj K)).str.hom)
    (γ : GW ⋙ VX ⋙ Endofunctor.IsoAlgebra.forget Q ⟶
      (VY ⋙ Endofunctor.IsoAlgebra.forget T) ⋙ G)
    (hc : ∀ M : WY,
      F.map (γ.app M) ≫ adj.counit.app (VY.obj M).carrier =
        a.inv.app (GW.obj M) ≫ (VY.map (adjW.counit.app M)).hom.f)
    (L : WY) :
    Q.map (γ.app L) ≫
        (mateEquiv adj adj (TwoSquare.mk _ _ _ _ β.inv)).natTrans.app
          (VY.obj L).carrier ≫ G.map (VY.obj L).str.hom =
      (VX.obj (GW.obj L)).str.hom ≫
        γ.app L := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  calc
    F.map (Q.map (γ.app L)) ≫
        F.map ((mateEquiv adj adj (TwoSquare.mk _ _ _ _ β.inv)).natTrans.app
          (VY.obj L).carrier) ≫ F.map (G.map (VY.obj L).str.hom) ≫
          adj.counit.app (VY.obj L).carrier =
      F.map (Q.map (γ.app L)) ≫
        F.map ((mateEquiv adj adj (TwoSquare.mk _ _ _ _ β.inv)).natTrans.app
          (VY.obj L).carrier) ≫ adj.counit.app (T.obj (VY.obj L).carrier) ≫
          (VY.obj L).str.hom := by
      have hn : F.map (G.map (VY.obj L).str.hom) ≫
          adj.counit.app (VY.obj L).carrier =
        adj.counit.app (T.obj (VY.obj L).carrier) ≫ (VY.obj L).str.hom :=
          adj.counit.naturality (VY.obj L).str.hom
      rw [hn]
    _ = F.map (Q.map (γ.app L)) ≫ β.inv.app (G.obj (VY.obj L).carrier) ≫
        T.map (adj.counit.app (VY.obj L).carrier) ≫ (VY.obj L).str.hom := by
      simpa only [Category.assoc] using congrArg
        (fun z ↦ F.map (Q.map (γ.app L)) ≫ z ≫ (VY.obj L).str.hom)
        (mateEquiv_counit adj adj (TwoSquare.mk _ _ _ _ β.inv) (VY.obj L).carrier)
    _ = β.inv.app (VX.obj (GW.obj L)).carrier ≫ T.map (F.map (γ.app L)) ≫
        T.map (adj.counit.app (VY.obj L).carrier) ≫ (VY.obj L).str.hom := by
      have hn := β.inv.naturality (γ.app L)
      simpa only [Functor.comp_obj, Functor.comp_map,
        Endofunctor.IsoAlgebra.forget_obj, Category.assoc] using
        congrArg (fun z ↦ z ≫ T.map (adj.counit.app (VY.obj L).carrier) ≫
          (VY.obj L).str.hom) hn
    _ = β.inv.app (VX.obj (GW.obj L)).carrier ≫
        T.map (a.inv.app (GW.obj L)) ≫
          T.map (VY.map (adjW.counit.app L)).hom.f ≫ (VY.obj L).str.hom := by
      simpa only [Functor.map_comp, Category.assoc] using congrArg
        (fun z ↦ β.inv.app (VX.obj (GW.obj L)).carrier ≫ T.map z ≫
          (VY.obj L).str.hom) (hc L)
    _ = β.inv.app (VX.obj (GW.obj L)).carrier ≫
        T.map (a.inv.app (GW.obj L)) ≫ (VY.obj (FW.obj (GW.obj L))).str.hom ≫
          (VY.map (adjW.counit.app L)).hom.f := by
      have hn : T.map (VY.map (adjW.counit.app L)).hom.f ≫ (VY.obj L).str.hom =
          (VY.obj (FW.obj (GW.obj L))).str.hom ≫
            (VY.map (adjW.counit.app L)).hom.f := by
        simpa only [Functor.comp_obj, Functor.id_obj,
          Endofunctor.IsoAlgebra.str_hom] using
          (VY.map (adjW.counit.app L)).hom.h
      rw [hn]
    _ = F.map (VX.obj (GW.obj L)).str.hom ≫
        a.inv.app (GW.obj L) ≫ (VY.map (adjW.counit.app L)).hom.f := by
      simpa only [Category.assoc] using congrArg
        (fun z ↦ z ≫ (VY.map (adjW.counit.app L)).hom.f) (ha (GW.obj L)).symm
    _ = F.map (VX.obj (GW.obj L)).str.hom ≫
        F.map (γ.app L) ≫ adj.counit.app (VY.obj L).carrier := by rw [hc]

/-- Lift the invertible ordinary mate to Frobenius pairs before specializing
any coefficient category. -/
private theorem right_mate_pair_iso
    {WX WY CX CY : Type*} [Category WX] [Category WY] [Category CX] [Category CY]
    (FW : WX ⥤ WY) (GW : WY ⥤ WX) (adjW : FW ⊣ GW)
    (F : CX ⥤ CY) (G : CY ⥤ CX) (adj : F ⊣ G)
    (Q : CX ⥤ CX) (T : CY ⥤ CY)
    (VX : WX ⥤ Endofunctor.IsoAlgebra Q)
    (VY : WY ⥤ Endofunctor.IsoAlgebra T)
    (a : FW ⋙ VY ⋙ Endofunctor.IsoAlgebra.forget T ≅
      (VX ⋙ Endofunctor.IsoAlgebra.forget Q) ⋙ F)
    (β : F ⋙ T ≅ Q ⋙ F)
    (ha : ∀ K : WX,
      F.map (VX.obj K).str.hom ≫ a.inv.app K =
        β.inv.app (VX.obj K).carrier ≫ T.map (a.inv.app K) ≫
          (VY.obj (FW.obj K)).str.hom)
    (γ : GW ⋙ VX ⋙ Endofunctor.IsoAlgebra.forget Q ⟶
      (VY ⋙ Endofunctor.IsoAlgebra.forget T) ⋙ G)
    (hc : ∀ M : WY,
      F.map (γ.app M) ≫ adj.counit.app (VY.obj M).carrier =
        a.inv.app (GW.obj M) ≫ (VY.map (adjW.counit.app M)).hom.f)
    (e : G ⋙ Q ≅ T ⋙ G)
    (he : e.hom = (mateEquiv adj adj (TwoSquare.mk _ _ _ _ β.inv)).natTrans)
    [IsIso γ] (L : WY) :
    Nonempty (VX.obj (GW.obj L) ≅
      (Endofunctor.IsoAlgebra.mapOfNatIso e).obj (VY.obj L)) := by
  have h := right_mate_intertwines FW GW adjW F G adj Q T VX VY a β ha γ hc L
  have hm : Q.map (γ.app L) ≫
        ((Endofunctor.IsoAlgebra.mapOfNatIso e).obj (VY.obj L)).str.hom =
      (VX.obj (GW.obj L)).str.hom ≫ γ.app L := by
    simpa only [Endofunctor.IsoAlgebra.mapOfNatIso_obj_str, Iso.trans_hom,
      Functor.mapIso_hom, Iso.app_hom, he] using h
  let f : VX.obj (GW.obj L) ⟶
      (Endofunctor.IsoAlgebra.mapOfNatIso e).obj (VY.obj L) :=
    ⟨{ f := γ.app L, h := hm }⟩
  have : IsIso ((Endofunctor.IsoAlgebra.forget Q).map f) := by
    change IsIso (γ.app L)
    infer_instance
  have : IsIso f := isIso_of_reflects_iso f (Endofunctor.IsoAlgebra.forget Q)
  exact ⟨asIso f⟩

/-- Compose a comparison with the image of a unit comparison generically. -/
private theorem iso_comp_map
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A : D} {B B' : C} (i : A ≅ F.obj B) (j : B ≅ B') :
    Nonempty (A ≅ F.obj B') := ⟨i ≪≫ F.mapIso j⟩

omit [Fact (ringChar P.field.k₀ ≠ P.coefficients.l)] in
/-- The transported point constant is the defined exceptional constant. -/
private theorem exceptionalConstant_eq_map :
    (Endofunctor.IsoAlgebra.mapOfNatIso
      (exceptionalIso P.field P.coefficients.l P.coefficients.different
        P.coefficients.Qbar X₀ (point P.field) (pointMap P.field X₀) c₀ S)).obj
      (constantWeilAlgebraicallyClosedComplex P.coefficients.l P.field
        P.coefficients.different (point P.field) P.coefficients.Qbar) =
      exceptionalConstant P X₀ c₀ S := by
  rfl

attribute [local irreducible] Endofunctor.IsoAlgebra.mapOfNatIso

-- The quantified adjunction proof does not occur in the conclusion; keep its existing binder.
set_option linter.unusedVariables false in
/-- The normalized ordinary realization may be chosen so that it realizes the
exceptional constant pair with its actual inverse-exchange mate action.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction
paragraph; the first two steps of lem-sf-native-coefficient-cohomology-comparison.
(blueprint: lem-sf-exceptional-coefficient-realization)

Proof: restrict the fixed algebraic-closure isomorphism from P.coefficients.Qbar
to PadicAlgCl to every finite coefficient field. Scalar extension along these
restrictions, followed by the normalized ordinary realization, gives a coherent
cocone. Its balanced scalar associators descend the functor on common-stage
objects and representative arrows. Pull back through the geometric-fibre
isomorphism induced by IsAlgClosure.equiv over the finite base field, and undo
the section-module equivalence. This constructs the ordinary functor. The finite
integral representative formulas show full faithfulness, exactness, shift
compatibility and preservation of bounded constructibility. The realization
family's normalized comparison for arbitrary scheme isomorphisms includes
geometric Frobenius. Transport it through the section-module equivalence and
the geometric-fibre isomorphism to obtain the displayed natural isomorphism.
Its shift law follows from the same integral representative maps. The scalar
unit and pullback-unit normalizations give Data.unit.

Apply native_exceptional_forgetful at the constant point object. Its comparison
is normalized by the native counit and the ordinary adjunction counit. The
scalar_frobenius_counit theorem identifies the ordinary left comparison's
Frobenius square, including the scalar-unit comparison. Transpose the native
counit's equivariance through the ordinary adjunction Hom equivalence. Its
injectivity identifies the transported right action with exceptionalIso followed
by G of the constant action. Thus the ordinary comparison intertwines the two
invertible actions and lifts to an isomorphism of ordinary derived pairs. This
works for each supplied native adjunction; it does not identify native derived
morphism groups with morphisms between ordinary pairs. Neither this construction
nor the counit argument requires smoothness. Identity and empty models use the
same unit and counit equations. -/
theorem exceptional_realization :
    ∃ R : CoefficientRealization.Data P X₀,
      ∀ (J : WeilComplex P.field.k₀ P.coefficients.l (Spec (.of P.field.k₀)) ⥤
          WeilComplex P.field.k₀ P.coefficients.l X₀.left)
        (adj : WeilComplex.derivedLowerShriek P.field.k₀ P.coefficients.l X₀.hom ⊣ J),
        Nonempty
          ((NativePairCohomology.native P.field.k₀ P.coefficients.l X₀.left).obj
              (J.obj (WeilSheaf.toComplex.obj
                (WeilSheaf.adicConstant P.field.k₀ P.coefficients.l
                  (Spec (.of P.field.k₀))))) ≅
            (CoefficientRealization.pairs P X₀ R).obj (exceptionalConstant P X₀ c₀ S)) := by
  classical
  obtain ⟨A⟩ := exceptional_realization_left_models P X₀ c₀ S
  refine ⟨A.source, ?_⟩
  intro J adj
  let O := operation P.field P.coefficients.l P.coefficients.different
    P.coefficients.Qbar X₀ (point P.field) (pointMap P.field X₀) c₀ S .closed
  let β := beta P.field P.coefficients.l P.coefficients.different P.coefficients.Qbar
    X₀ (point P.field) (pointMap P.field X₀) c₀ S
  let e := exceptionalIso P.field P.coefficients.l P.coefficients.different
    P.coefficients.Qbar X₀ (point P.field) (pointMap P.field X₀) c₀ S
  let γ := Adjunction.forgetfulRightMate adj O.adjunction A.left
  have : IsIso γ := exceptional_realization_right_mate_isIso P X₀ c₀ S A J adj
  let L := WeilSheaf.toComplex.obj
    (WeilSheaf.adicConstant P.field.k₀ P.coefficients.l (Spec (.of P.field.k₀)))
  obtain ⟨i⟩ := right_mate_pair_iso
    (WeilComplex.derivedLowerShriek P.field.k₀ P.coefficients.l X₀.hom) J adj
    O.F O.G O.adjunction
    (sourceFrobenius P.field P.coefficients.l P.coefficients.different
      P.coefficients.Qbar X₀)
    (targetFrobenius P.field P.coefficients.l P.coefficients.different
      P.coefficients.Qbar (point P.field))
    A.sourceModel A.targetModel A.left β A.left_frobenius γ
    (fun M ↦ mateEquiv_counit adj O.adjunction
      (TwoSquare.mk _ _ _ _ A.left.inv) M) e rfl L
  dsimp only [L, e, O] at i
  obtain ⟨k⟩ := iso_comp_map
    (B := A.targetModel.obj (WeilSheaf.toComplex.obj
      (WeilSheaf.adicConstant P.field.k₀ P.coefficients.l (Spec (.of P.field.k₀)))))
    (B' := constantWeilAlgebraicallyClosedComplex P.coefficients.l P.field
      P.coefficients.different (point P.field) P.coefficients.Qbar)
    (Endofunctor.IsoAlgebra.mapOfNatIso
      (exceptionalIso P.field P.coefficients.l P.coefficients.different
        P.coefficients.Qbar X₀ (point P.field) (pointMap P.field X₀) c₀ S)) i A.pointUnit
  rw [← exceptionalConstant_eq_map P X₀ c₀ S]
  exact ⟨(A.sourceRealization.app (J.obj (WeilSheaf.toComplex.obj
      (WeilSheaf.adicConstant P.field.k₀ P.coefficients.l
        (Spec (.of P.field.k₀)))))).symm ≪≫
    (CoefficientRealization.pairs P X₀ A.source).mapIso k⟩

end WeilConjectures.NativeCoefficientCohomology
