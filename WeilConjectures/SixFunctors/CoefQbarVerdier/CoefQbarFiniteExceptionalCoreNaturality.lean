/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierData
import WeilConjectures.SixFunctors.Common.CommonStagePullbackNormalizedDescent

/-! Naturality of the transported finite exceptional comparison component.
Source: thm-coef-qbar-verdier, retained proof step 9.
(blueprint: lem-coef-qbar-finite-exceptional-core-naturality)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false

universe u v
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefQbarVerdier
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion)

attribute [local irreducible] rationalDerivedPullback commonStageDerivedPullback
  HasDerivedCategory.standard

private theorem stage_inclusion_eq
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C H : I → Type*} [∀ i, Category (C i)] [∀ i, Category (H i)]
    {S : StageSystem C} {T : StageSystem H} (F : S.Morphism T) (i : I) :
    F.Φ i ⋙ T.ι i = S.ι i ⋙ F.functor := by
  refine Functor.hext (F := F.Φ i ⋙ T.ι i) (G := S.ι i ⋙ F.functor)
    (fun _ ↦ rfl) ?_
  intro A B a
  exact HEq.symm (heq_of_eq (F.functor_map_ι a))

private theorem paste_dual_comparison
    {C₀ H₀ C H : Type*} [Category C₀] [Category H₀] [Category C] [Category H]
    (IX : H₀ ⥤ H) (IY : C₀ ⥤ C) (dx : H₀ᵒᵖ ⥤ H₀) (dy : C₀ᵒᵖ ⥤ C₀)
    (DX : Hᵒᵖ ⥤ H) (DY : Cᵒᵖ ⥤ C) (R : C₀ ⥤ H₀) (P : C ⥤ H) (T : C₀ ⥤ H₀)
    (e : T ≅ dy.rightOp ⋙ R.op ⋙ dx)
    (bx : dx ⋙ IX ≅ IX.op ⋙ DX) (by' : dy ⋙ IY ≅ IY.op ⋙ DY)
    (pb : R ⋙ IX ≅ IY ⋙ P) {M N : C₀} (g : M ⟶ N) :
    IX.map (T.map g) ≫ IX.map (e.hom.app N) ≫
        bx.hom.app (op (R.obj (dy.obj (op N)))) ≫
        DX.map (P.map (by'.inv.app (op N)) ≫ pb.inv.app (dy.obj (op N))).op =
      IX.map (e.hom.app M) ≫ bx.hom.app (op (R.obj (dy.obj (op M)))) ≫
        DX.map (P.map (by'.inv.app (op M)) ≫ pb.inv.app (dy.obj (op M))).op ≫
        (IY ⋙ DY.rightOp ⋙ P.op ⋙ DX).map g := by
  let a := dy.map g.op
  let b := DY.map (IY.map g).op
  have hy : b ≫ by'.inv.app (op M) = by'.inv.app (op N) ≫ IY.map a :=
    by'.inv.naturality g.op
  have hq : (P.map (by'.inv.app (op N)) ≫ pb.inv.app (dy.obj (op N))) ≫
      IX.map (R.map a) =
      P.map b ≫ P.map (by'.inv.app (op M)) ≫ pb.inv.app (dy.obj (op M)) := by
    have hn := pb.inv.naturality a
    simp only [Functor.comp_map] at hn
    rw [Category.assoc, ← hn, ← Category.assoc, ← P.map_comp, ← hy, P.map_comp]
    simp only [Category.assoc]
  have he := congrArg IX.map (e.hom.naturality g)
  simp only [Functor.map_comp, Functor.comp_map, Functor.rightOp_map,
    Functor.op_map, Quiver.Hom.unop_op] at he
  have hx := bx.hom.naturality (R.map a).op
  simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op] at hx
  simp only [Functor.comp_map, Functor.rightOp_map, Functor.op_map, Quiver.Hom.unop_op]
  rw [← Category.assoc (IX.map (T.map g)), he]
  simp only [Category.assoc]
  rw [← Category.assoc (IX.map (dx.map (R.map a).op)), hx]
  simp only [Category.assoc]
  congr 2
  simp only [← DX.map_comp, ← op_comp]
  exact congrArg (fun k ↦ DX.map k.op) hq

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

variable {Y : Scheme.{u}} [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [QuasiCompact (Y ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (BX : Duality D l hl Ω X) (BY : Duality D l hl Ω Y)
  (c : Compactification f)
  (S : ConstructibleExceptionalCoefficients.System l (AuxiliaryClosure.{u} l) D hl (f := f))

/-- The explicit component used to transport a finite exceptional comparison is natural.
The proof is the pasting of naturality for the rational exceptional comparison, the
finite Verdier comparison, the pullback comparison, and the common-stage duality map.
-/
theorem finite_exceptional_comparison_naturality
    (E : Index l Ω)
    (e : RationalOperations.ExceptionalIdentification l X D hl (AuxiliaryClosure.{u} l) c
      S (fieldStage l Ω E) (BX.finite.omega E) (BY.finite.omega E)
      (BX.finite.datum E) (BY.finite.datum E))
    {M N : Stage l Ω Y E} (g : M ⟶ N) :
    (inclusion E).map ((finiteRight D l hl Ω X f c S E).map g) ≫
        (inclusion E).map (e.comparison.app N).hom ≫
      (BX.comparison E).hom.app
        (op ((@rationalDerivedPullback l _ (Coefficient.{u} l Ω E) _ _ _ X Y f
          (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)).obj
            ((BY.finite.datum E).dual.obj (op N)))) ≫
      BX.duality.dual.map
        ((CoefQbarPullback D l hl Ω f).map ((BY.comparison E).inv.app (op N)) ≫
          (pullbackInclusion D l hl Ω X f E
            ((BY.finite.datum E).dual.obj (op N))).inv).op =
    (inclusion E).map (e.comparison.app M).hom ≫
      (BX.comparison E).hom.app
        (op ((@rationalDerivedPullback l _ (Coefficient.{u} l Ω E) _ _ _ X Y f
          (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)).obj
            ((BY.finite.datum E).dual.obj (op M)))) ≫
      BX.duality.dual.map
        ((CoefQbarPullback D l hl Ω f).map ((BY.comparison E).inv.app (op M)) ≫
          (pullbackInclusion D l hl Ω X f E
            ((BY.finite.datum E).dual.obj (op M))).inv).op ≫
      (inclusion E ⋙ BY.duality.dual.rightOp ⋙
        (CoefQbarPullback D l hl Ω f).op ⋙ BX.duality.dual).map g  := by
  let := RationalVerdier.units D l hl X
  let := RationalVerdier.units D l hl Y
  let R := rationalDerivedPullback l (Coefficient.{u} l Ω E) f
  let P := CoefQbarPullback D l hl Ω f
  have hp : R ⋙ inclusion E = inclusion E ⋙ P := by
    obtain ⟨hcoh, h⟩ := commonStagePullbackNormalizedDescent l Ω f
    change R ⋙ inclusion E = inclusion E ⋙ commonStageDerivedPullback l Ω f
    rw [h]
    let F : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).Morphism
        (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X) :=
      ⟨fun E ↦ rationalDerivedPullback l (Coefficient.{u} l Ω E) f,
        commonStagePullbackTransition l Ω f, hcoh⟩
    exact stage_inclusion_eq F E
  have hc (A : Stage l Ω Y E) :
      (eqToIso hp).inv.app A = (pullbackInclusion D l hl Ω X f E A).inv := by
    rw [eqToIso.inv, eqToHom_app]
    unfold pullbackInclusion
    erw [eqToIso.inv]
    exact Functor.congr_obj hp A
  have h := paste_dual_comparison (inclusion (Y := X) E) (inclusion (Y := Y) E)
    (BX.finite.datum E).dual (BY.finite.datum E).dual BX.duality.dual BY.duality.dual
    R P (finiteRight D l hl Ω X f c S E) e.comparison (BX.comparison E)
    (BY.comparison E) (eqToIso hp) g
  simp only [hc] at h
  exact h

end WeilConjectures.CoefQbarVerdier
