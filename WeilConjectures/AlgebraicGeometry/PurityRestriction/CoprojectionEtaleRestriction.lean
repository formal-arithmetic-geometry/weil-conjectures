/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteExceptionalComposition
public import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumRightAdjointTensor
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekLocality
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleHorizontalSupportMate
public import WeilConjectures.AlgebraicGeometry.PurityTensorExchange.CanonicalTensorExchange
public import WeilConjectures.CategoryTheory.Adjunction.InvertibleCoprojectionTensorMate
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompositionCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit

/-! # Étale restriction of the canonical invertible-factor co-projection

Source: current blueprint, part-duality-trace-formula/sec-poincare-duality/
sec-the-trace-map-in-top-degree/sk-cor-trace/sk-thm-regular/sk-thm-regular.proof.md,
Steps 2 and 4(i)--(ii), and part-duality-trace-formula/sec-smooth-purity/sec-sp-grp-trace/
sec-base-change-and-composition/sk-prop-sp-purity-bc/sk-lem-coprojection/
sk-lem-coprojection.proof.md, the displayed Hom calculation
(blueprint: lem-pur-coprojection-etale-restriction).

We use ordinary étale coordinates for the finite-coefficient constructible categories.
The final maps are their images under the actual derived site-comparison pullback, so
are morphisms in D(V_proet,A). All comparisons below are constructions, not parameters.
The finite-coefficient coefficient-model equivalence and counit-preserving adjunction
transfer identify these coordinates with the condensed-coefficient statement.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale.PurityRestriction

variable (A : Type (w + 1)) [CommRing A] [Finite A]

/-- The canonical counit-preserving étale identification, using the chosen
compactification and the recorded graph/sum comparison, followed by the canonical
exact-to-left-derived pullback comparison.
Source: sk-thm-regular, Step 4(i); lem-pur-etale-sum-right-adjoint-tensor
(blueprint: lem-pur-coprojection-etale-restriction). -/
def rho {T W : Scheme.{w}} (e : T ⟶ W) [AlgebraicGeometry.Etale e]
    [IsSeparated e] [QuasiCompact e] [HasCompactification e] :
    rightDerivedUpperShriek A e ≅ (upperStar (ModuleCat.{w + 1} A) e).leftDerivedFunctor :=
  etaleTensorRho A e (HasCompactification.compactification e)
    (rightDerivedUpperShriek A e) (rightDerivedUpperShriekAdjunction A e) ≪≫
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{w + 1} A) e).symm

section Square
variable {X Z U V : Scheme.{w}}
variable (i : Z ⟶ X) (u : U ⟶ X) (v : V ⟶ Z) (j : V ⟶ U)
variable [AlgebraicGeometry.Etale u] [AlgebraicGeometry.Etale v]
variable [IsSeparated u] [IsSeparated v]
variable [HasCompactification i] [HasCompactification u]
variable [HasCompactification v] [HasCompactification j]
variable [HasCompactification (j ≫ u)] [HasCompactification (v ≫ i)]
variable [QuasiCompact j] [QuasiCompact v] [QuasiCompact u]
variable [QuasiCompact (j ≫ u)] [QuasiCompact (v ≫ i)]

/-- The displayed B, as a natural isomorphism. Its middle comparison is the canonical
compactification comparison for the equality of the two composite scheme maps.
Source: sk-thm-regular, Step 4(i), the chain Rj! u* = R(uj)! = R(iv)! = v* Ri!
(blueprint: lem-pur-coprojection-etale-restriction). -/
def B (sq : IsPullback j v u i) :
    (upperStar (ModuleCat.{w + 1} A) u).leftDerivedFunctor ⋙ rightDerivedUpperShriek A j ≅
      rightDerivedUpperShriek A i ⋙
        (upperStar (ModuleCat.{w + 1} A) v).leftDerivedFunctor :=
  Functor.isoWhiskerRight (rho A u).symm (rightDerivedUpperShriek A j) ≪≫
    (WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition A j u).symm ≪≫
    rightDerivedUpperShriekCongr A sq.w ≪≫
    WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition A v i ≪≫
    Functor.isoWhiskerLeft (rightDerivedUpperShriek A i) (rho A v)

/-- The canonical pullback-composition comparison of the square, with the same
composite map on both sides. No choice of a square isomorphism is involved.
Source: sk-thm-regular, Step 4(ii), pullback of the invertible factor
(blueprint: lem-pur-coprojection-etale-restriction). -/
def chi (sq : IsPullback j v u i) :
    (upperStar (ModuleCat.{w + 1} A) u).leftDerivedFunctor ⋙
        (upperStar (ModuleCat.{w + 1} A) j).leftDerivedFunctor ≅
      (upperStar (ModuleCat.{w + 1} A) i).leftDerivedFunctor ⋙
        (upperStar (ModuleCat.{w + 1} A) v).leftDerivedFunctor :=
  (leftDerivedUpperStarComp (ModuleCat.{w + 1} A) j u).symm ≪≫
    leftDerivedUpperStarComp (ModuleCat.{w + 1} A) v i (j ≫ u) sq.w

variable (sq : IsPullback j v u i)
variable (K L M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{w + 1} A)))
variable (e : ((derivedTensor (ModuleCat.{w + 1} A) X).obj M).obj L ≅ constantComplex A X)
variable (e' : ((derivedTensor (ModuleCat.{w + 1} A) X).obj L).obj M ≅ constantComplex A X)

/-- Left side of the restriction square. The co-projection is the existing right-adjoint
comparison induced by projection at M and the two specified evaluations: its construction
is the test-object Hom chain, not a choice from Nonempty.
Source: sk-lem-coprojection, displayed Hom calculation; sk-thm-regular, Steps 2 and 4(ii)
(blueprint: lem-pur-coprojection-etale-restriction). -/
def leftArrow :
    (rightDerivedUpperShriek A j).obj
        ((upperStar (ModuleCat.{w + 1} A) u).leftDerivedFunctor.obj
          (((derivedTensor (ModuleCat.{w + 1} A) X).obj K).obj L)) ⟶
      ((derivedTensor (ModuleCat.{w + 1} A) V).obj
        ((upperStar (ModuleCat.{w + 1} A) v).leftDerivedFunctor.obj
          ((rightDerivedUpperShriek A i).obj K))).obj
        ((upperStar (ModuleCat.{w + 1} A) v).leftDerivedFunctor.obj
          ((upperStar (ModuleCat.{w + 1} A) i).leftDerivedFunctor.obj L)) :=
  ((B A i u v j sq).app (((derivedTensor (ModuleCat.{w + 1} A) X).obj K).obj L)).hom ≫
    (upperStar (ModuleCat.{w + 1} A) v).leftDerivedFunctor.map
      (((derivedTensorRightCompRightDerivedUpperShriekIso A i L M e e').app K).hom) ≫
    (leftDerivedUpperStarTensorIso (ModuleCat.{w + 1} A) v
      ((rightDerivedUpperShriek A i).obj K)
      ((upperStar (ModuleCat.{w + 1} A) i).leftDerivedFunctor.obj L)).hom

/-- Right side of the restriction square. The evaluations for the j co-projection are
obtained by the actual pullback tensor and unit comparisons applied to e and e'.
Source: sk-thm-regular, Steps 2 and 4(ii), with the Hom chain of sk-lem-coprojection
(blueprint: lem-pur-coprojection-etale-restriction). -/
def rightArrow :
    (rightDerivedUpperShriek A j).obj
        ((upperStar (ModuleCat.{w + 1} A) u).leftDerivedFunctor.obj
          (((derivedTensor (ModuleCat.{w + 1} A) X).obj K).obj L)) ⟶
      ((derivedTensor (ModuleCat.{w + 1} A) V).obj
        ((upperStar (ModuleCat.{w + 1} A) v).leftDerivedFunctor.obj
          ((rightDerivedUpperShriek A i).obj K))).obj
        ((upperStar (ModuleCat.{w + 1} A) v).leftDerivedFunctor.obj
          ((upperStar (ModuleCat.{w + 1} A) i).leftDerivedFunctor.obj L)) :=
  let Su := (upperStar (ModuleCat.{w + 1} A) u).leftDerivedFunctor
  let eu := (leftDerivedUpperStarTensorIso (ModuleCat.{w + 1} A) u M L).symm ≪≫
    Su.mapIso e ≪≫ leftDerivedUpperStarUnitIso (ModuleCat.{w + 1} A) u
  let eu' := (leftDerivedUpperStarTensorIso (ModuleCat.{w + 1} A) u L M).symm ≪≫
    Su.mapIso e' ≪≫ leftDerivedUpperStarUnitIso (ModuleCat.{w + 1} A) u
  (rightDerivedUpperShriek A j).map
      (leftDerivedUpperStarTensorIso (ModuleCat.{w + 1} A) u K L).hom ≫
    ((derivedTensorRightCompRightDerivedUpperShriekIso A j
      (Su.obj L) (Su.obj M) eu eu').app (Su.obj K)).hom ≫
    ((derivedTensor (ModuleCat.{w + 1} A) V).map ((B A i u v j sq).app K).hom).app
      ((upperStar (ModuleCat.{w + 1} A) j).leftDerivedFunctor.obj (Su.obj L)) ≫
    ((derivedTensor (ModuleCat.{w + 1} A) V).obj
      ((upperStar (ModuleCat.{w + 1} A) v).leftDerivedFunctor.obj
        ((rightDerivedUpperShriek A i).obj K))).map ((chi A i u v j sq).app L).hom

private theorem coprojection_inv_tensorMap
    (A : Type (w + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{w}} (f : X ⟶ Y) [HasCompactification f]
    (K L M : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{w + 1} A)))
    (e : ((derivedTensor (ModuleCat.{w + 1} A) Y).obj M).obj L ≅ constantComplex A Y)
    (e' : ((derivedTensor (ModuleCat.{w + 1} A) Y).obj L).obj M ≅ constantComplex A Y) :
    (derivedTensorRightCompRightDerivedUpperShriekIso A f L M e e').inv.app K =
      rightDerivedUpperShriekTensorMap f K L := by
  let :=  leftDerivedUpperStarMonoidal (ModuleCat.{w + 1} A) f
  let π := fun N ↦ asIso (((flipFunctor _ _ _).map
    (projectionMap (ModuleCat.{w + 1} A) f)).app N)
  apply Adjunction.tensorRightCompIso_inv_eq_projectionTensorMap
    (rightDerivedUpperShriekAdjunction A f)
    (upperStar (ModuleCat.{w + 1} A) f).leftDerivedFunctor e e' π
  · intro Z N N' h
    exact projectionMap_app_app_naturality_right f Z h
  · intro Z N N'
    exact (projectionMapAssociativity A f).assoc Z N N'
  · intro Z
    dsimp only [π, asIso_hom, CategoryTheory.flipFunctor]
    simpa only [Functor.Monoidal.εIso_inv, leftDerivedUpperStarOplaxMonoidal_η] using
      projectionMap_rightUnitality (ModuleCat.{w + 1} A) f Z

private theorem pullbackComp_common
    (A : Type (w + 1)) [CommRing A] {T S S' R : Scheme.{w}}
    (a : T ⟶ S) (b : S ⟶ R) (a' : T ⟶ S') (b' : S' ⟶ R)
    (c₁ c₂ : T ⟶ R) (h₁ : c₁ = a ≫ b) (h₁' : c₁ = a' ≫ b')
    (h₂ : c₂ = a ≫ b) (h₂' : c₂ = a' ≫ b')
    (K : DerivedCategory (Sheaf R.smallEtaleTopology (ModuleCat.{w + 1} A))) :
    (leftDerivedUpperStarComp (ModuleCat.{w + 1} A) a b c₁ h₁).inv.app K ≫
        (leftDerivedUpperStarComp (ModuleCat.{w + 1} A) a' b' c₁ h₁').hom.app K =
      (leftDerivedUpperStarComp (ModuleCat.{w + 1} A) a b c₂ h₂).inv.app K ≫
        (leftDerivedUpperStarComp (ModuleCat.{w + 1} A) a' b' c₂ h₂').hom.app K := by
  obtain rfl : c₁ = c₂ := h₁.trans h₂.symm
  rfl

private theorem pullbackChi_eq
    {X Z U V : Scheme.{w}} (i : Z ⟶ X) (u : U ⟶ X) (v : V ⟶ Z) (j : V ⟶ U)
    (sq : IsPullback j v u i) :
    derivedSquareUpperStarIso (ModuleCat.{w + 1} A) sq.flip.toCommSq = chi A i u v j sq := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  dsimp only [derivedSquareUpperStarIso, chi, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  exact pullbackComp_common A j u v i (v ≫ i) (j ≫ u)
    sq.w.symm rfl rfl sq.w N

private def tensorMap_restriction_inferred (sq : IsPullback j v u i)
    (hB : rightDerivedUpperShriekBaseChangeMap A sq.flip = (B A i u v j sq).inv)
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{w + 1} A))) := by
  have h := PurityTensorExchange.tensorMap_restriction A i u v j sq K L
  rw [hB] at h
  simp only [derivedSquareUpperStarIsoInvApp, pullbackChi_eq A i u v j sq] at h
  exact h

private theorem iso_hexagon {C : Type*} [Category C]
    {P Q R S T U : C} (b : P ≅ Q) (a : Q ≅ R) (d : R ≅ S)
    (c : P ≅ T) (f : T ≅ U) (e : U ≅ S)
    (h : a.inv ≫ b.inv ≫ c.hom = d.hom ≫ e.inv ≫ f.inv) :
    b.hom ≫ a.hom ≫ d.hom = c.hom ≫ f.hom ≫ e.hom := by
  apply (cancel_epi (a.inv ≫ b.inv)).1
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    using (congrArg (fun z ↦ z ≫ f.hom ≫ e.hom) h).symm

private theorem mapped_bifunctor_hexagon
    {C D E : Type*} [Category C] [Category D] [Category E]
    (T : E ⥤ E ⥤ E) (F : C ⥤ E) (G : D ⥤ E)
    {X₀ X₁ : C} {Y₀ Y₁ : D} {P Q R S : E}
    (a : X₀ ≅ X₁) (c : Y₀ ≅ Y₁) (b : G.obj Y₀ ≅ F.obj X₀)
    (d : F.obj X₁ ≅ (T.obj R).obj S) (f : G.obj Y₁ ≅ (T.obj P).obj Q)
    (e₁ : P ≅ R) (e₂ : Q ≅ S)
    (h : F.map a.inv ≫ b.inv ≫ G.map c.hom =
      d.hom ≫ (T.map e₁.inv).app S ≫ (T.obj P).map e₂.inv ≫ f.inv) :
    b.hom ≫ F.map a.hom ≫ d.hom =
      G.map c.hom ≫ f.hom ≫ (T.map e₁.hom).app Q ≫ (T.obj R).map e₂.hom := by
  let e := (T.mapIso e₁).app Q ≪≫ (T.obj R).mapIso e₂
  have hi : F.map a.inv ≫ b.inv ≫ G.map c.hom = d.hom ≫ e.inv ≫ f.inv := by
    dsimp only [e, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv]
    rw [← Category.assoc _ _ f.inv, (T.map e₁.inv).naturality e₂.inv]
    simpa only [Category.assoc] using h
  have hh := iso_hexagon b (F.mapIso a) d (G.mapIso c) f e hi
  simpa only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Category.assoc] using hh

private theorem mapped_bifunctor_hexagon_of_inverse
    {C D E : Type*} [Category C] [Category D] [Category E]
    (T : E ⥤ E ⥤ E) (F : C ⥤ E) (G : D ⥤ E)
    {X₀ X₁ : C} {Y₀ Y₁ : D} {P Q R S : E}
    (a : X₀ ≅ X₁) (c : Y₀ ≅ Y₁) (b : G.obj Y₀ ≅ F.obj X₀)
    (d : F.obj X₁ ≅ (T.obj R).obj S) (f : G.obj Y₁ ≅ (T.obj P).obj Q)
    (e₁ : P ≅ R) (e₂ : Q ≅ S) (p : X₁ ⟶ X₀)
    (r : (T.obj P).obj Q ⟶ G.obj Y₁) (ha : a.inv = p) (hf : f.inv = r)
    (h : F.map p ≫ b.inv ≫ G.map c.hom =
      d.hom ≫ (T.map e₁.inv).app S ≫ (T.obj P).map e₂.inv ≫ r) :
    b.hom ≫ F.map a.hom ≫ d.hom =
      G.map c.hom ≫ f.hom ≫ (T.map e₁.hom).app Q ≫ (T.obj R).map e₂.hom := by
  exact mapped_bifunctor_hexagon T F G a c b d f e₁ e₂
    (by simpa only [ha, hf] using h)


-- Keep the large derived-functor constructions opaque during categorical cancellation.

private def restriction_hexagon (sq : IsPullback j v u i)
    (hB : rightDerivedUpperShriekBaseChangeMap A sq.flip = (B A i u v j sq).inv)
    (K L M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{w + 1} A)))
    (e : ((derivedTensor (ModuleCat.{w + 1} A) X).obj M).obj L ≅
      constantComplex A X) (e' : ((derivedTensor (ModuleCat.{w + 1} A) X).obj L).obj M ≅
      constantComplex A X) := by
  have h := tensorMap_restriction_inferred A i u v j sq hB K L
  let Su := (upperStar (ModuleCat.{w + 1} A) u).leftDerivedFunctor
  let eu := (leftDerivedUpperStarTensorIso (ModuleCat.{w + 1} A) u M L).symm ≪≫
    Su.mapIso e ≪≫ leftDerivedUpperStarUnitIso (ModuleCat.{w + 1} A) u
  let eu' := (leftDerivedUpperStarTensorIso (ModuleCat.{w + 1} A) u L M).symm ≪≫
    Su.mapIso e' ≪≫ leftDerivedUpperStarUnitIso (ModuleCat.{w + 1} A) u
  let q := derivedTensorRightCompRightDerivedUpperShriekIso A i L M e e'
  let qj := derivedTensorRightCompRightDerivedUpperShriekIso A j
    (Su.obj L) (Su.obj M) eu eu'
  have hx := mapped_bifunctor_hexagon_of_inverse (derivedTensor (ModuleCat.{w + 1} A) V)
    (upperStar (ModuleCat.{w + 1} A) v).leftDerivedFunctor (rightDerivedUpperShriek A j)
    (q.app K) (leftDerivedUpperStarTensorIso (ModuleCat.{w + 1} A) u K L)
    ((B A i u v j sq).app (((derivedTensor (ModuleCat.{w + 1} A) X).obj K).obj L))
    (leftDerivedUpperStarTensorIso (ModuleCat.{w + 1} A) v
      ((rightDerivedUpperShriek A i).obj K)
      ((upperStar (ModuleCat.{w + 1} A) i).leftDerivedFunctor.obj L))
    (qj.app (Su.obj K)) ((B A i u v j sq).app K) ((chi A i u v j sq).app L)
    (rightDerivedUpperShriekTensorMap i K L)
    (rightDerivedUpperShriekTensorMap j (Su.obj K) (Su.obj L))
    (coprojection_inv_tensorMap A i K L M e e')
    (coprojection_inv_tensorMap A j (Su.obj K) (Su.obj L) (Su.obj M) eu eu')
  -- Normalize the premise while preserving the public bifunctor notation in the conclusion.
  have hex := hx (by
    dsimp only [q, qj, Su, eu, eu', derivedTensorRight, Functor.comp_obj,
      Functor.flip_obj_obj, derivedTensor, curriedTensor_obj_obj]
    simp only [Iso.app_inv, curriedTensor_map_app,
      curriedTensor_obj_map]
    with_reducible exact h)
  exact hex

private theorem restriction_of_mate (sq : IsPullback j v u i)
    (hB : rightDerivedUpperShriekBaseChangeMap A sq.flip = (B A i u v j sq).inv)
    (K L M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{w + 1} A)))
    (e : ((derivedTensor (ModuleCat.{w + 1} A) X).obj M).obj L ≅
      constantComplex A X) (e' : ((derivedTensor (ModuleCat.{w + 1} A) X).obj L).obj M ≅
      constantComplex A X) :
    leftArrow A i u v j sq K L M e e' = rightArrow A i u v j sq K L M e e' := by
  have hex := restriction_hexagon A i u v j sq hB K L M e e'
  unfold leftArrow rightArrow
  exact hex

private theorem coprojection_naturality
    (A : Type (w + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{w}} (a : X ⟶ Y) [HasCompactification a]
    (K L M K' L' M' : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{w + 1} A)))
    (e : ((derivedTensor (ModuleCat.{w + 1} A) Y).obj M).obj L ≅
      constantComplex A Y) (e' : ((derivedTensor (ModuleCat.{w + 1} A) Y).obj L).obj M ≅
      constantComplex A Y)
    (d : ((derivedTensor (ModuleCat.{w + 1} A) Y).obj M').obj L' ≅
      constantComplex A Y) (d' : ((derivedTensor (ModuleCat.{w + 1} A) Y).obj L').obj M' ≅
      constantComplex A Y)
    (f : K ⟶ K') (l : L ⟶ L') :
    (rightDerivedUpperShriek A a).map (tensorHom f l) ≫
        (derivedTensorRightCompRightDerivedUpperShriekIso A a L' M' d d').hom.app K' =
      (derivedTensorRightCompRightDerivedUpperShriekIso A a L M e e').hom.app K ≫
        tensorHom ((rightDerivedUpperShriek A a).map f)
          ((upperStar (ModuleCat.{w + 1} A) a).leftDerivedFunctor.map l) := by
  apply (cancel_epi
    ((derivedTensorRightCompRightDerivedUpperShriekIso A a L M e e').inv.app K)).1
  apply (cancel_mono
    ((derivedTensorRightCompRightDerivedUpperShriekIso A a L' M' d d').inv.app K')).1
  simp only [Category.assoc, Iso.hom_inv_id_app,
    Iso.inv_hom_id_app_assoc]
  rw [coprojection_inv_tensorMap, coprojection_inv_tensorMap]
  symm
  change _ = (rightDerivedUpperShriekAdjunction A a).projectionTensorMap _ K L ≫ _
  rw [MonoidalCategory.tensorHom_def, Category.assoc,
    Adjunction.projectionTensorMap_naturality_right
      (rightDerivedUpperShriekAdjunction A a) _
      (projectionMap_app_app_naturality_right a),
    ← Category.assoc,
    Adjunction.projectionTensorMap_naturality_left
      (rightDerivedUpperShriekAdjunction A a) _
      (projectionMap_app_app_naturality_left a), Category.assoc, ← Functor.map_comp]
  simp only [MonoidalCategory.tensorHom_def]
  erw [Category.comp_id]

private theorem rightAdjointUniq_ofNatIsoLeft
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G G' : D ⥤ C}
    (adj : F ⊣ G) (adj' : F' ⊣ G') (e : F ≅ F') :
    (adj.ofNatIsoLeft e).rightAdjointUniq adj' =
      conjugateIsoEquiv adj adj' e.symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply (adj'.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_symm_rightAdjointUniq_hom_app,
    Adjunction.homEquiv_counit]
  change e.inv.app (G.obj K) ≫ adj.counit.app K =
    F'.map ((conjugateEquiv adj adj' e.inv).app K) ≫ adj'.counit.app K
  rw [conjugateEquiv_counit]

private theorem horizontalMate
    {X X' Y Y' : Scheme.{w}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {v : Y' ⟶ Y} {v' : X' ⟶ X}
    [IsSeparated f] [IsSeparated f'] [IsSeparated v] [IsSeparated v']
    [AlgebraicGeometry.Etale v] [AlgebraicGeometry.Etale v']
    [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    [LocallyOfFiniteType v] [LocallyOfFiniteType v']
    [QuasiCompact f] [QuasiCompact f'] [QuasiCompact v] [QuasiCompact v']
    [HasCompactification f] [HasCompactification f']
    [HasCompactification v] [HasCompactification v']
    [HasCompactification (v' ≫ f)] [HasCompactification (f' ≫ v)]
    [QuasiCompact (v' ≫ f)] [QuasiCompact (f' ≫ v)]
    (sq : IsPullback v' f' f v) (N : EtaleCompactSupportNormalization A) :
    mateEquiv
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{w + 1} A) v' inferInstance)
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{w + 1} A) v inferInstance)
      (TwoSquare.mk _ _ _ _ (etaleHorizontalSupportMateDelta A sq N).inv) =
    TwoSquare.mk _ _ _ _ (etaleHorizontalSupportBaseChangeIso A sq).inv := by
  apply TwoSquare.ext
  intro K
  apply ((derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{w + 1} A) v inferInstance
    ).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  rw [mateEquiv_counit]
  exact etaleHorizontalSupportMate A sq N K

private theorem lowerCongr_eq
    {X Y : Scheme.{w}} [IsNoetherian X] [IsNoetherian Y]
    {f f' : X ⟶ Y} [HasCompactification f] [HasCompactification f']
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [QuasiCompact f']
    (h : f = f') :
    rightDerivedLowerShriekCongr A h = unboundedEtaleLowerShriekCongr A h := by
  subst h
  change rightDerivedLowerShriekOfCompactificationIso A
    (HasCompactification.compactification f) (HasCompactification.compactification f) = _
  exact (unboundedEtaleCompactSupport_comparison_coherence A f).1 _

private theorem upperCongr_eq
    {X Y : Scheme.{w}} [IsNoetherian X] [IsNoetherian Y]
    {f f' : X ⟶ Y} [HasCompactification f] [HasCompactification f']
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [QuasiCompact f']
    (h : f = f') :
    rightDerivedUpperShriekCongr A h =
      conjugateIsoEquiv (rightDerivedUpperShriekAdjunction A f)
        (rightDerivedUpperShriekAdjunction A f')
        (unboundedEtaleLowerShriekCongr A h).symm := by
  unfold rightDerivedUpperShriekCongr
  rw [rightAdjointUniq_ofNatIsoLeft, lowerCongr_eq]

private theorem canonicalComparison_eq
    {U X : Scheme.{w}} [IsNoetherian U] [IsNoetherian X]
    (e : U ⟶ X) [AlgebraicGeometry.Etale e] [IsSeparated e] [QuasiCompact e]
    [HasCompactification e] :
    etaleCanonicalCompactSupportComparison A e
      (canonicalEtaleCompactSupportNormalization A) =
    canonicalEtaleCompactSupportComparison A e (HasCompactification.compactification e) := by
  have h : rightDerivedLowerShriekIso A (HasCompactification.compactification e) =
      Iso.refl _ := (unboundedEtaleCompactSupport_comparison_coherence A e).1 _
  simp only [etaleCanonicalCompactSupportComparison, h, Iso.refl_symm]
  erw [Iso.refl_trans]
  rfl

private theorem lowerCongr_symm
    {X Y : Scheme.{w}} [IsNoetherian X] [IsNoetherian Y]
    {f f' : X ⟶ Y} [HasCompactification f] [HasCompactification f']
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [QuasiCompact f']
    (h : f = f') :
    unboundedEtaleLowerShriekCongr A h.symm =
      (unboundedEtaleLowerShriekCongr A h).symm := by
  subst h
  rfl

private theorem delta_conjugate :
    conjugateIsoEquiv
      ((rightDerivedUpperShriekAdjunction A j).comp
        (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{w + 1} A) u inferInstance))
      ((derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{w + 1} A) v inferInstance).comp
        (rightDerivedUpperShriekAdjunction A i))
      (etaleHorizontalSupportMateDelta A sq.flip
        (canonicalEtaleCompactSupportNormalization A)) =
    Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{w + 1} A) u).symm
      (rightDerivedUpperShriek A j) ≪≫ B A i u v j sq ≪≫
    Functor.isoWhiskerLeft (rightDerivedUpperShriek A i)
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{w + 1} A) v) := by
  unfold etaleHorizontalSupportMateDelta
  rw [canonicalComparison_eq A v, canonicalComparison_eq A u]
  rw [conjugateIsoEquiv_trans _
    ((rightDerivedUpperShriekAdjunction A v).comp
      (rightDerivedUpperShriekAdjunction A i))]
  rw [conjugateIsoEquiv_trans _
    (rightDerivedUpperShriekAdjunction A (v ≫ i))]
  rw [conjugateIsoEquiv_trans _
    (rightDerivedUpperShriekAdjunction A (j ≫ u))]
  rw [conjugateIsoEquiv_trans _
    ((rightDerivedUpperShriekAdjunction A j).comp
      (rightDerivedUpperShriekAdjunction A u))]
  rw [conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_isoWhiskerRight]
  rw [lowerCongr_symm A sq.w,
    ← upperCongr_eq A sq.w]
  simp only [B, rho, WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition,
    etaleTensorRho, Iso.trans_assoc, Functor.isoWhiskerRight_trans,
    Functor.isoWhiskerLeft_trans, Iso.trans_symm, Iso.symm_symm_eq,
    ← conjugateIsoEquiv_iso_symm]
  apply Iso.ext
  apply NatTrans.ext
  funext K
  simp

private theorem exactMate_B :
    (mateEquiv (rightDerivedUpperShriekAdjunction A i)
      (rightDerivedUpperShriekAdjunction A j)
      (TwoSquare.mk _ _ _ _ (etaleHorizontalSupportBaseChangeIso A sq.flip).inv)).natTrans =
    Functor.whiskerLeft (rightDerivedUpperShriek A i)
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{w + 1} A) v).inv ≫
    (B A i u v j sq).inv ≫
    Functor.whiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{w + 1} A) u).hom
      (rightDerivedUpperShriek A j) := by
  have h := iterated_mateEquiv_conjugateEquiv
    (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{w + 1} A) v inferInstance)
    (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{w + 1} A) u inferInstance)
    (rightDerivedUpperShriekAdjunction A j) (rightDerivedUpperShriekAdjunction A i)
    (TwoSquare.mk _ _ _ _ (etaleHorizontalSupportMateDelta A sq.flip
      (canonicalEtaleCompactSupportNormalization A)).inv)
  rw [horizontalMate A sq.flip] at h
  change _ = (conjugateIsoEquiv
    ((rightDerivedUpperShriekAdjunction A j).comp
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{w + 1} A) u inferInstance))
    ((derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{w + 1} A) v inferInstance).comp
      (rightDerivedUpperShriekAdjunction A i))
    (etaleHorizontalSupportMateDelta A sq.flip
      (canonicalEtaleCompactSupportNormalization A))).inv at h
  rw [delta_conjugate A i u v j sq] at h
  simpa only [Iso.trans_inv, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Iso.symm_inv, Category.assoc] using h

private theorem derivedMate_B :
    rightDerivedUpperShriekBaseChangeMap A sq.flip = (B A i u v j sq).inv := by
  have hi : IsIso (rightDerivedLowerShriekBaseChangeMap A sq.flip) :=
    isIso_rightDerivedLowerShriekBaseChangeMap A sq.flip
  have he : (TwoSquare.mk _ _ _ _ (etaleHorizontalSupportBaseChangeIso A sq.flip).inv) =
    ((TwoSquare.mk _ _ _ _ (inv (rightDerivedLowerShriekBaseChangeMap A sq.flip))).whiskerTop
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{w + 1} A) v).inv).whiskerBottom
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{w + 1} A) u).hom := by
    ext K
    simp only [etaleHorizontalSupportBaseChangeIso, asIso_inv,
      unboundedEtaleCompactSupportBaseChange, IsIso.inv_comp,
      TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app, TwoSquare.mk,
      NatTrans.comp_app, Category.assoc]
    simp
  have h := exactMate_B A i u v j sq
  rw [he, mateEquiv_whiskerTop_whiskerBottom] at h
  apply NatTrans.ext
  funext K
  have hk := NatTrans.congr_app h K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, TwoSquare.whiskerLeft_app,
    TwoSquare.whiskerRight_app, rightDerivedUpperShriekBaseChangeMap] at hk ⊢
  apply (cancel_epi ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{w + 1} A) v).app
    ((rightDerivedUpperShriek A i).obj K)).inv).1
  apply (cancel_mono (((rightDerivedUpperShriek A j).mapIso
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{w + 1} A) u).app K)).hom)).1
  simpa only [Category.assoc, Iso.app_inv, Iso.app_hom, Functor.mapIso_hom,
    TwoSquare.mk, TwoSquare.natTrans] using hk

end Square

/-- The co-projection restriction equation and its naturality, in finite-coefficient
ordinary étale coordinates followed by the actual site-comparison pullback.
Source: current blueprint sk-thm-regular, Steps 2 and 4(i)--(ii), and the full Hom
calculation in sk-lem-coprojection (blueprint: lem-pur-coprojection-etale-restriction).

Proof:
1. Base change makes v étale and j closed. Finite type over k and separatedness supply
   Noetherian qcqs schemes and Nagata compactifications of the arrows and composites.
2. Work in the ordinary étale realization. Conjugate the specified lower-shriek
   compositor to obtain c. Conjugate the graph/sum comparison to obtain rho, uniquely
   fixed by its evaluation-counit equation (etaleSumRightAdjointTensor).
3. The iterated-square-mates identity and the horizontal support-mate identity identify
   the inverse exchange mate with B, in the displayed order of its five factors.
4. Expand each co-projection using its tensorRightCompIsoOfTensorIso construction:
   adjunction; cancellation with M; projection at M; adjunction; cancellation back
   with L. Projection-formula/base-change coherence identifies the middle Hom arrows.
   The outer Hom arrows agree by the counit equations and mate pasting. Transpose back.
5. Strong monoidal pullback carries both evaluations to eu and eu'. Pullback composition
   identifies the two restrictions through chi. This gives leftArrow = rightArrow.
   All Hom arrows are natural in K and in evaluation-preserving invertible isomorphisms;
   applying the same calculation to these arrows gives the second clause below.
6. Apply derived comparisonUpperStar. Finite-Tor site equivalence, the finite discrete
   coefficient equivalence, and counit-preserving Brown-adjunction transfer identify
   this with the asserted equality in D(V_proet,A), including the same naturality.
   Unit, shifted, inverse-twist, identity-pullback and empty-scheme cases are covered
   by these constructions without an orientation or a choice of comparison maps.
-/
theorem coprojectionEtaleRestriction
    {k : Type w} [Field k] {p ell : ℕ}
    (hp : 0 < p) (hchar : ringChar k = p) (hpPrime : Nat.Prime p)
    (hellPrime : Nat.Prime ell) (hneq : ell ≠ p) (hk : Finite k ∨ IsAlgClosed k)
    (hA : ∃ N : ℕ, 1 ≤ N ∧ ∀ a : A, (ell ^ N) • a = 0)
    (X Z U V : Over (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (i : Z ⟶ X) (u : U ⟶ X) (v : V ⟶ Z) (j : V ⟶ U)
    [IsClosedImmersion i.left] [AlgebraicGeometry.Etale u.left]
    (sq : IsPullback j.left v.left u.left i.left) :
    letI : AlgebraicGeometry.Etale v.left :=
      MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Etale) sq inferInstance
    letI : IsClosedImmersion j.left :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion) sq.flip inferInstance
    letI : HasCompactification i.left := HasCompactification.of_over i
    letI : HasCompactification u.left := HasCompactification.of_over u
    letI : HasCompactification v.left := HasCompactification.of_over v
    letI : HasCompactification j.left := HasCompactification.of_over j
    letI : HasCompactification (j.left ≫ u.left) := HasCompactification.of_over (j ≫ u)
    letI : HasCompactification (v.left ≫ i.left) := HasCompactification.of_over (v ≫ i)
    letI : QuasiCompact u.left := by
      have : QuasiCompact (u.left ≫ X.hom) := by rw [u.w]; infer_instance
      exact QuasiCompact.of_comp u.left X.hom
    letI : QuasiCompact v.left := by
      have : QuasiCompact (v.left ≫ Z.hom) := by rw [v.w]; infer_instance
      exact QuasiCompact.of_comp v.left Z.hom
    letI : IsSeparated u.left := by
      have : IsSeparated (u.left ≫ X.hom) := by rw [u.w]; infer_instance
      exact IsSeparated.of_comp u.left X.hom
    letI : IsSeparated v.left := by
      have : IsSeparated (v.left ≫ Z.hom) := by rw [v.w]; infer_instance
      exact IsSeparated.of_comp v.left Z.hom
    let ν := (ProEtale.comparisonUpperStar (ModuleCat.{w + 1} A) V.left).mapDerivedCategory
    ∀ (K L M : _root_.DerivedCategory
      (Sheaf X.left.smallEtaleTopology (ModuleCat.{w + 1} A))),
    DerivedCategory.boundedConstructibleFiniteTor A X.left K →
    DerivedCategory.boundedConstructibleFiniteTor A X.left L →
    DerivedCategory.boundedConstructibleFiniteTor A X.left M →
    ∀ (e : ((derivedTensor (ModuleCat.{w + 1} A) X.left).obj M).obj L ≅
      constantComplex A X.left)
      (e' : ((derivedTensor (ModuleCat.{w + 1} A) X.left).obj L).obj M ≅
      constantComplex A X.left),
    ν.map (leftArrow A i.left u.left v.left j.left sq K L M e e') =
      ν.map (rightArrow A i.left u.left v.left j.left sq K L M e e') ∧
    ∀ (K' L' M' : _root_.DerivedCategory
      (Sheaf X.left.smallEtaleTopology (ModuleCat.{w + 1} A))),
    DerivedCategory.boundedConstructibleFiniteTor A X.left K' →
    DerivedCategory.boundedConstructibleFiniteTor A X.left L' →
    DerivedCategory.boundedConstructibleFiniteTor A X.left M' →
    ∀ (f : K ⟶ K') (l : L ≅ L') (m : M ≅ M')
      (d : ((derivedTensor (ModuleCat.{w + 1} A) X.left).obj M').obj L' ≅
        constantComplex A X.left)
      (d' : ((derivedTensor (ModuleCat.{w + 1} A) X.left).obj L').obj M' ≅
        constantComplex A X.left),
      tensorHom m.hom l.hom ≫ d.hom = e.hom →
      tensorHom l.hom m.hom ≫ d'.hom = e'.hom →
      let Gi := rightDerivedUpperShriek A i.left
      let Gj := rightDerivedUpperShriek A j.left
      let Su := (upperStar (ModuleCat.{w + 1} A) u.left).leftDerivedFunctor
      let Si := (upperStar (ModuleCat.{w + 1} A) i.left).leftDerivedFunctor
      let Sv := (upperStar (ModuleCat.{w + 1} A) v.left).leftDerivedFunctor
      ν.map (Gj.map (Su.map (tensorHom f l.hom)) ≫
        leftArrow A i.left u.left v.left j.left sq K' L' M' d d') =
      ν.map (leftArrow A i.left u.left v.left j.left sq K L M e e' ≫
        tensorHom (Sv.map (Gi.map f)) (Sv.map (Si.map l.hom))) := by
  letI : AlgebraicGeometry.Etale v.left :=
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Etale) sq inferInstance
  letI : IsClosedImmersion j.left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) sq.flip inferInstance
  letI : HasCompactification i.left := HasCompactification.of_over i
  letI : HasCompactification u.left := HasCompactification.of_over u
  letI : HasCompactification v.left := HasCompactification.of_over v
  letI : HasCompactification j.left := HasCompactification.of_over j
  letI : HasCompactification (j.left ≫ u.left) := HasCompactification.of_over (j ≫ u)
  letI : HasCompactification (v.left ≫ i.left) := HasCompactification.of_over (v ≫ i)
  letI : QuasiCompact u.left := by
    have : QuasiCompact (u.left ≫ X.hom) := by rw [u.w]; infer_instance
    exact QuasiCompact.of_comp u.left X.hom
  letI : QuasiCompact v.left := by
    have : QuasiCompact (v.left ≫ Z.hom) := by rw [v.w]; infer_instance
    exact QuasiCompact.of_comp v.left Z.hom
  letI : IsSeparated u.left := by
    have : IsSeparated (u.left ≫ X.hom) := by rw [u.w]; infer_instance
    exact IsSeparated.of_comp u.left X.hom
  letI : IsSeparated v.left := by
    have : IsSeparated (v.left ≫ Z.hom) := by rw [v.w]; infer_instance
    exact IsSeparated.of_comp v.left Z.hom
  letI : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
  letI : IsNoetherian Z.left := isNoetherian_of_locallyOfFiniteType Z.hom
  letI : IsNoetherian U.left := isNoetherian_of_locallyOfFiniteType U.hom
  letI : IsNoetherian V.left := isNoetherian_of_locallyOfFiniteType V.hom
  intro ν K L M _ _ _ e e'
  constructor
  · exact congrArg ν.map (restriction_of_mate A i.left u.left v.left j.left sq
      (derivedMate_B A i.left u.left v.left j.left sq) K L M e e')
  · intro K' L' M' _ _ _ f l m d d' _ _
    apply congrArg ν.map
    dsimp only [leftArrow]
    simp only [Iso.app_hom]
    erw [← Functor.comp_map, (B A i.left u.left v.left j.left sq).hom.naturality_assoc]
    simp only [Functor.comp_map]
    rw [← Functor.map_comp_assoc,
      coprojection_naturality A i.left K L M K' L' M' e e' d d' f l.hom, Functor.map_comp,
      Category.assoc, Category.assoc]
    let Sv := (upperStar (ModuleCat.{w + 1} A) v.left).leftDerivedFunctor
    let φ := (rightDerivedUpperShriek A i.left).map f
    let ψ := (upperStar (ModuleCat.{w + 1} A) i.left).leftDerivedFunctor.map l.hom
    have hn : Sv.map (derivedTensorHom (ModuleCat.{w + 1} A) φ ψ) ≫
        (leftDerivedUpperStarTensorIso (ModuleCat.{w + 1} A) v.left _ _).hom =
      (leftDerivedUpperStarTensorIso (ModuleCat.{w + 1} A) v.left _ _).hom ≫
        derivedTensorHom (ModuleCat.{w + 1} A) (Sv.map φ) (Sv.map ψ) := by
      have h₁ := congr_app
        ((leftDerivedUpperStarTensorNatIso (ModuleCat.{w + 1} A) v.left).hom.naturality φ)
        ((upperStar (ModuleCat.{w + 1} A) i.left).leftDerivedFunctor.obj L)
      have h₂ := ((leftDerivedUpperStarTensorNatIso (ModuleCat.{w + 1} A) v.left).hom.app
        ((rightDerivedUpperShriek A i.left).obj K')).naturality ψ
      simp only [NatTrans.comp_app] at h₁ h₂
      simp only [leftDerivedUpperStarTensorIso, Iso.app_hom, Functor.map_comp,
        Category.assoc, derivedTensorHom, Sv]
      erw [h₂]
      rw [← Category.assoc, ← Category.assoc]
      erw [h₁]
      rfl
    dsimp only [Sv, φ, ψ] at hn
    simp only [derivedTensorHom, derivedTensor_map_app, derivedTensor_obj_map] at hn
    simp only [MonoidalCategory.tensorHom_def, Category.assoc]
    rw [hn]
    rfl

end AlgebraicGeometry.Etale.PurityRestriction
