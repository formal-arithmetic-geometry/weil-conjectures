/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalClassRootLimitProjection

/-! # The normalized reduction comparison on supported single sheaves

Source: diagonal coefficient changes, paragraph (3). -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
section Generic
universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄
variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  {A' : Type u₃} [Category.{v₃} A'] [Abelian A']
  {B' : Type u₄} [Category.{v₄} B'] [Abelian B']
  (E : A ⥤ B) [E.Additive] (V : B ⥤ B') [V.Additive]
  (F : A ⥤ A') [F.Additive] (E' : A' ⥤ B') [E'.Additive]
  (e : E ⋙ V ≅ F ⋙ E') (M : A)

private theorem single_complex_square :
    (V.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).hom.app M) ≫
      (HomologicalComplex.singleMapHomologicalComplex V (.up ℤ) 0).hom.app (E.obj M) ≫
      (HomologicalComplex.single B' (.up ℤ) 0).map (e.hom.app M) =
    (NatIso.mapHomologicalComplex e (.up ℤ)).hom.app
        ((HomologicalComplex.single A (.up ℤ) 0).obj M) ≫
      (E'.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M) ≫
      (HomologicalComplex.singleMapHomologicalComplex E' (.up ℤ) 0).hom.app (F.obj M) := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = 0
  · subst i
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.single_map_f_self, Functor.map_comp, Category.assoc]
    simp only [Iso.map_inv_hom_id_assoc, Iso.inv_hom_id_assoc]
    exact e.hom.naturality_assoc
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (E'.obj (F.obj M))).inv
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ i hi).eq_of_tgt _ _


universe w
variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{w} A'] [HasDerivedCategory.{w} B']
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (T : DerivedCategory A ⥤ DerivedCategory B)
  (T' : DerivedCategory A' ⥤ DerivedCategory B')
  (ε : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (ε' : DerivedCategory.Q ⋙ T' ⟶ E'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (q : T ⋙ V.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ T')

private theorem single_counit_square
    (hh :
      V.mapDerivedCategory.map
          (ε.app ((HomologicalComplex.single A (.up ℤ) 0).obj M)) ≫
        V.mapDerivedCategoryFactors.hom.app
          ((E.mapHomologicalComplex (.up ℤ)).obj
            ((HomologicalComplex.single A (.up ℤ) 0).obj M)) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app
          ((HomologicalComplex.single A (.up ℤ) 0).obj M)) =
      q.hom.app ((DerivedCategory.singleFunctor A 0).obj M) ≫
        T'.map (F.mapDerivedCategoryFactors.hom.app
          ((HomologicalComplex.single A (.up ℤ) 0).obj M)) ≫
        ε'.app ((F.mapHomologicalComplex (.up ℤ)).obj
          ((HomologicalComplex.single A (.up ℤ) 0).obj M))) :
    V.mapDerivedCategory.map
      (T.map ((DerivedCategory.singleFunctorIsoCompQ A 0).hom.app M) ≫
        ε.app ((HomologicalComplex.single A (.up ℤ) 0).obj M) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).hom.app M) ≫
        (DerivedCategory.singleFunctorIsoCompQ B 0).inv.app (E.obj M)) ≫
      (V.mapDerivedCategorySingleFunctor 0).hom.app (E.obj M) ≫
      (DerivedCategory.singleFunctor B' 0).map (e.hom.app M) =
    q.hom.app ((DerivedCategory.singleFunctor A 0).obj M) ≫
      T'.map ((F.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      (T'.map ((DerivedCategory.singleFunctorIsoCompQ A' 0).hom.app (F.obj M)) ≫
        ε'.app ((HomologicalComplex.single A' (.up ℤ) 0).obj (F.obj M)) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex E' (.up ℤ) 0).hom.app
            (F.obj M)) ≫
        (DerivedCategory.singleFunctorIsoCompQ B' 0).inv.app (E'.obj (F.obj M))) := by
  let P := (HomologicalComplex.single A (.up ℤ) 0).obj M
  let sE := (HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).hom.app M
  let sF := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M
  let sV := (HomologicalComplex.singleMapHomologicalComplex V (.up ℤ) 0).hom.app (E.obj M)
  let sE' := (HomologicalComplex.singleMapHomologicalComplex E' (.up ℤ) 0).hom.app
    (F.obj M)
  simp only [Functor.mapDerivedCategorySingleFunctor, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  dsimp [DerivedCategory.singleFunctorIsoCompQ]
  simp only [Functor.map_comp, Category.id_comp, Category.comp_id, Category.assoc]
  erw [T.map_id, V.mapDerivedCategory.map_id, V.mapDerivedCategory.map_id,
    F.mapDerivedCategory.map_id, T'.map_id, T'.map_id]
  simp only [Category.id_comp]
  dsimp only [CochainComplex.singleFunctor]
  have hε := ε'.naturality sF
  dsimp only [Functor.comp_map] at hε
  have hV := V.mapDerivedCategoryFactors_hom_naturality sE
  erw [← Category.assoc (V.mapDerivedCategory.map (DerivedCategory.Q.map sE)), hV]
  erw [← Category.assoc (T'.map (DerivedCategory.Q.map sF)), hε]
  simp only [Category.assoc]
  have hs := congrArg DerivedCategory.Q.map (single_complex_square E V F E' e M)
  simp only [Functor.map_comp] at hs
  change DerivedCategory.Q.map ((V.mapHomologicalComplex (.up ℤ)).map sE) ≫
      DerivedCategory.Q.map sV ≫ (DerivedCategory.singleFunctor B' 0).map
        (e.hom.app M) =
    DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) ≫
      DerivedCategory.Q.map ((E'.mapHomologicalComplex (.up ℤ)).map sF) ≫
      DerivedCategory.Q.map sE' at hs
  erw [hs]
  have hh' := congrArg
    (fun z ↦ z ≫ DerivedCategory.Q.map ((E'.mapHomologicalComplex (.up ℤ)).map sF) ≫
      DerivedCategory.Q.map sE') hh
  simp only [Category.assoc] at hh'
  convert hh' using 1 <;> rfl

end Generic
section Naturality
universe uA vA uB vB wA wB
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  (E : A ⥤ B) [E.Additive] (T : DerivedCategory A ⥤ DerivedCategory B)
  (ε : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)

private def singleCounit :
    DerivedCategory.singleFunctor A 0 ⋙ T ⟶ E ⋙ DerivedCategory.singleFunctor B 0 :=
  Functor.whiskerRight (DerivedCategory.singleFunctorIsoCompQ A 0).hom T ≫
    Functor.whiskerLeft (HomologicalComplex.single A (.up ℤ) 0) ε ≫
    Functor.whiskerRight
      (HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).hom DerivedCategory.Q ≫
    Functor.whiskerLeft E (DerivedCategory.singleFunctorIsoCompQ B 0).inv

private theorem singleCounit_naturality {M N : A} (f : M ⟶ N) :
    T.map ((DerivedCategory.singleFunctor A 0).map f) ≫
      (T.map ((DerivedCategory.singleFunctorIsoCompQ A 0).hom.app N) ≫
        ε.app ((HomologicalComplex.single A (.up ℤ) 0).obj N) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).hom.app N) ≫
        (DerivedCategory.singleFunctorIsoCompQ B 0).inv.app (E.obj N)) =
      (T.map ((DerivedCategory.singleFunctorIsoCompQ A 0).hom.app M) ≫
        ε.app ((HomologicalComplex.single A (.up ℤ) 0).obj M) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).hom.app M) ≫
        (DerivedCategory.singleFunctorIsoCompQ B 0).inv.app (E.obj M)) ≫
      (DerivedCategory.singleFunctor B 0).map (E.map f) := by
  have h := (singleCounit E T ε).naturality f
  simpa only [singleCounit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.comp_map, Category.assoc] using h

end Naturality

private theorem single_scalar_mono {A : Type*} [Category A] [Abelian A]
    (n : ℕ) (M : A) (hm : Mono (n • 𝟙 M)) (i : ℤ) :
    Mono (n • 𝟙 (((HomologicalComplex.single A (.up ℤ) 0).obj M).X i)) := by
  classical
  by_cases hi : i = 0
  · subst i
    let e := eqToIso (HomologicalComplex.single_obj_X_self (.up ℤ) 0 M)
    let : Mono (n • 𝟙 M) := hm
    have he : (n • 𝟙 (((HomologicalComplex.single A (.up ℤ) 0).obj M).X 0)) ≫ e.hom =
        e.hom ≫ (n • 𝟙 M) := by
      simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
        Category.id_comp, Category.comp_id]
    exact mono_of_mono_fac he
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi).mono _

universe u
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients
open DiagonalTrace
attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor diagonalCompletedSource

private theorem source_mono (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ) :
    Mono (l ^ (n + 1) • 𝟙 (diagonalIntegralSource Y)) := by
  have hm := constant_scalar_mono (ProjectiveLine Y) (l ^ (n + 1))
    (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
  have := (lowerStar AddCommGrpCat.{u + 1} (diagonalImmersion Y)).map_mono
    (l ^ (n + 1) • 𝟙 ((constantSheaf (Scheme.ProEt.topology (ProjectiveLine Y))
      AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))))
  simpa only [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id] using this

variable {l : ℕ} [Fact l.Prime] {Y Y' : Scheme.{u}} {g : Y' ⟶ Y}
  [DiagonalTraceLocalizations l (diagonalSurface Y)]
  [DiagonalTraceLocalizations l (diagonalSurface Y')]
  {hY : IsUnit (l : Γ(Y, ⊤))} {hY' : IsUnit (l : Γ(Y', ⊤))}
  {D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y))}
  {D' : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y'))}
  {d : ClassLimitPresentation l Y hY D} {d' : ClassLimitPresentation l Y' hY' D'}
  {e : CompletedRealization l (diagonalSurface Y)}
  {e' : CompletedRealization l (diagonalSurface Y')}

set_option maxHeartbeats 4000000 in
-- Instantiating the generic counit square on the concrete sheaf frame is expensive.
/-- The reduction comparison has its ordinary value on a regular single input.
Source: coefficient changes (3), the frame regular-computation square.

Proof: apply the frame computation square to the degree-zero complex of M.
The exact derived/single comparisons are induced by the degree-zero complex
comparisons. Naturality of each derived counit moves those comparisons past
it. The remaining square of complexes is the ordinary reduction square in
degree zero and the zero square elsewhere. -/
private theorem single_reduction_pullback
    (frame : DiagonalClassPullbackFrame l g d d' e e')
    (M : DiagonalAb (diagonalSurface Y))
    (hM : ∀ n : ℕ, Mono (l ^ (n + 1) • 𝟙 M)) :
    (diagonalClassTowerPull l (baseW g)).mapDerivedCategory.map
        (diagonalDerivedSingleCounit l
          (diagonalScalarExtension l (diagonalSurface Y)) D M) ≫
      ((diagonalClassTowerPull l (baseW g)).mapDerivedCategorySingleFunctor 0).hom.app
        (D.ordinary.E.obj M) ≫
      (DerivedCategory.singleFunctor _ 0).map (frame.ordinaryReduction.hom.app M) =
    frame.reduction.hom.app ((DerivedCategory.singleFunctor _ 0).obj M) ≫
      D'.T.map (((upperStar Ab.{u + 1} (baseW g)).mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      diagonalDerivedSingleCounit l
        (diagonalScalarExtension l (diagonalSurface Y')) D'
        ((upperStar Ab.{u + 1} (baseW g)).obj M) := by
  let P := (HomologicalComplex.single (DiagonalAb (diagonalSurface Y)) (.up ℤ) 0).obj M
  have hP : ∀ (n : ℕ) (i : ℤ), Mono (l ^ (n + 1) • 𝟙 (P.X i)) :=
    fun n i ↦ single_scalar_mono _ M (hM n) i
  simpa only [diagonalDerivedSingleCounit] using
    single_counit_square D.ordinary.E (diagonalClassTowerPull l (baseW g))
      (upperStar Ab.{u + 1} (baseW g)) D'.ordinary.E frame.ordinaryReduction M
      D.T D'.T D.ε D'.ε frame.reduction (frame.reduction_computation P hP)

set_option maxHeartbeats 4000000 in
-- The concrete derived and ordinary source comparisons contain large exact-functor terms.
/-- On the supported integral source the derived frame is its ordinary reduction
comparison, followed by the canonical supported source map.
Source: diagonal coefficient changes (3), regular source and quotient normalizations.
(blueprint: lem-diagonal-class-single-reduction-pullback).

Proof: multiplication by each positive prime power is monic on integral constants,
hence on their closed direct image. The degree-zero single therefore belongs to
the frame's regular computing class. Apply its computation square there. The
single-complex comparison commutes with the ordinary reduction comparison, by
naturality in degree zero; all other degrees are zero. Naturality of the derived
counit moves the supported-source map past the upstairs counit. Finally use the
two a_normalization equations and cancel the pulled-back a isomorphism. -/
theorem diagonalClassSourcePullback
    (frame : DiagonalClassPullbackFrame l g d d' e e') :
    (diagonalClassTowerPull l (baseW g)).mapDerivedCategory.map d.a.inv ≫
        frame.systemSource ≫ d'.a.hom =
      ((diagonalClassTowerPull l (baseW g)).mapDerivedCategorySingleFunctor 0).hom.app
          (D.ordinary.E.obj (diagonalIntegralSource Y)) ≫
        (DerivedCategory.singleFunctor _ 0).map
          (frame.ordinaryReduction.hom.app (diagonalIntegralSource Y) ≫
            D'.ordinary.E.map (diagonalBoundarySource (baseW g) (baseP g)
              (diagonalBaseChange_cartesian g).toCommSq)) := by
  let V := diagonalClassTowerPull l (baseW g)
  let G := V.mapDerivedCategory
  let F := upperStar Ab.{u + 1} (baseW g)
  let s := diagonalBoundarySource (baseW g) (baseP g)
    (diagonalBaseChange_cartesian g).toCommSq
  have h := single_reduction_pullback frame (diagonalIntegralSource Y) (source_mono l Y)
  have hn : D'.T.map ((DerivedCategory.singleFunctor _ 0).map s) ≫ d'.a.hom =
      diagonalDerivedSingleCounit l (diagonalScalarExtension l (diagonalSurface Y')) D'
          (F.obj (diagonalIntegralSource Y)) ≫
        (DerivedCategory.singleFunctor _ 0).map (D'.ordinary.E.map s) := by
    rw [d'.a_normalization]
    exact singleCounit_naturality D'.ordinary.E D'.T D'.ε s
  have ht : G.map d.a.hom ≫
        (V.mapDerivedCategorySingleFunctor 0).hom.app
          (D.ordinary.E.obj (diagonalIntegralSource Y)) ≫
        (DerivedCategory.singleFunctor _ 0).map
          (frame.ordinaryReduction.hom.app (diagonalIntegralSource Y) ≫
            D'.ordinary.E.map s) = frame.systemSource ≫ d'.a.hom := by
    rw [d.a_normalization]
    have hh := congrArg
      (fun z ↦ z ≫ (DerivedCategory.singleFunctor _ 0).map (D'.ordinary.E.map s)) h
    simp only [Category.assoc] at hh
    rw [← hn] at hh
    simpa only [G, V, F, s, DiagonalClassPullbackFrame.systemSource,
      diagonalClassIntegralSource, Functor.map_comp, Category.assoc] using hh
  rw [← ht]
  rw [← G.map_comp_assoc, Iso.inv_hom_id, G.map_id, Category.id_comp]

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
