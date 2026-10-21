/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.SixFunctors.RingedDerivedAdjointLift
public import Sheaf.SixFunctors.RingedDerivedComparisonData
public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.Algebra.Homology.RingedHomCompositionModel
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import WeilConjectures.Algebra.Homology.HomTensorSectionNaturality
import Sheaf.SixFunctors.RingedDerivedTensorLift

/-! # Evaluation-defined Hom comparison for ringed pullback

Source: Stacks Project, Cohomology on Sites, Tags 07A4, 08J9 and 0A98;
agent evaluation-mate calculation, steps 1-8
(blueprint: lem-coef-ringed-pullback-hom-evaluation-comparison).

## Main definitions and statement

* `pullbackHomTensorModel` restricts the fixed tensor model to flat-term K-flats.
* `ringedPullbackHomComparison` is the transpose of pulled-back evaluation.
* `RingedHomSignedRepresentatives` specifies evaluation and composition on the actual
  signed total tensor and product Hom complexes.
* `ringedPullbackHomEvaluationComparison` states naturality and compatibility with
  evaluation, arbitrary tensor-Hom transposition and internal composition.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures SheafOfModules
  CategoryTheory.MonoidalCategory

namespace CategoryTheory.RingedDerivedComparisons

/-- The already fixed derived internal Hom, with only its site arguments abbreviated.
Source: Stacks 08J9 (blueprint: lem-coef-ringed-pullback-hom-evaluation-comparison). -/
abbrev pullbackHomFunctor (X : Site.{u, w}) : X.Dᵒᵖ × X.D ⥤ X.D :=
  derivedInternalHomOfUniverses.{u, u, u, w} X.J X.A

/-- Restriction of the site's fixed tensor comparison to flat-term K-flat representatives.
This constructs the data directly; it does not choose an arbitrary tensor comparison.
Source: Stacks 07A4 (blueprint: lem-coef-ringed-pullback-hom-evaluation-comparison). -/
def pullbackHomTensorModel (X : Site.{u, w}) : RingedTensorModel X.corner :=
  { representative := Functor.isoWhiskerLeft
      (({
        obj := fun P ↦ ⟨P.obj,
          (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P.obj).2 P.property.1⟩
        map := fun a ↦ ObjectProperty.homMk a.hom } :
        ObjectProperty.FullSubcategory X.corner.mateFlat ⥤
          ObjectProperty.FullSubcategory
            (CochainComplex.IsKFlatIndependentCoefficients.{u, u, u}
              (J := X.J) (R := X.A))).prod
        ({
        obj := fun P ↦ ⟨P.obj,
          (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P.obj).2 P.property.1⟩
        map := fun a ↦ ObjectProperty.homMk a.hom } :
        ObjectProperty.FullSubcategory X.corner.mateFlat ⥤
          ObjectProperty.FullSubcategory
            (CochainComplex.IsKFlatIndependentCoefficients.{u, u, u}
              (J := X.J) (R := X.A)))) X.model.comparison }

/-- The canonical comparison in the direction FX tensor FY to F(X tensor Y).
Source: Stacks 07A4 (blueprint: lem-coef-ringed-pullback-hom-evaluation-comparison). -/
def pullbackHomTensorator {X Y : Site.{u, w}} {f : Morphism X Y}
    (l : AdjointLift f) (P Q : Y.D) :
    X.closed.tensor.obj (l.edge.left.obj P, l.edge.left.obj Q) ⟶
      l.edge.left.obj (Y.closed.tensor.obj (P, Q)) :=
  (l.edge.tensorComparison (pullbackHomTensorModel Y) (pullbackHomTensorModel X)).inv.app
    (P, Q)

/-- Transpose of canonical tensor comparison followed by pulled-back evaluation.
No invertibility of this map is part of the construction.
Source: Stacks 07A4, 08J9 (blueprint: lem-coef-ringed-pullback-hom-evaluation-comparison). -/
def ringedPullbackHomComparison {X Y : Site.{u, w}} {f : Morphism X Y}
    (l : AdjointLift f) (P Q : Y.D) :
    l.edge.left.obj ((pullbackHomFunctor Y).obj (op P, Q)) ⟶
      (pullbackHomFunctor X).obj (op (l.edge.left.obj P), l.edge.left.obj Q) :=
  X.closed.transpose _ (l.edge.left.obj P) (l.edge.left.obj Q)
    (pullbackHomTensorator l ((pullbackHomFunctor Y).obj (op P, Q)) P ≫
      l.edge.left.map (Y.closed.evaluation P Q))

private theorem uncurry_formula {D : Type*} [Category* D]
    {H : Dᵒᵖ × D ⥤ D} (S : CoefficientClosedStructure H)
    (T P Q : D) (t : T ⟶ H.obj (op P, Q)) :
    (S.transpose T P Q).symm t =
      S.tensor.map (Prod.mkHom t (𝟙 P)) ≫ S.evaluation P Q := by
  change (@MonoidalCategory.tensorRight D _ S.monoidal P).map t ≫
    S.evaluation P Q = _
  let _ := S.monoidal
  simp [CoefficientClosedStructure.tensor]

private theorem uncurry_precomp {D : Type*} [Category* D]
    {H : Dᵒᵖ × D ⥤ D} (S : CoefficientClosedStructure H)
    {T T' P Q : D} (a : T' ⟶ T) (t : T ⟶ H.obj (op P, Q)) :
    (S.transpose T' P Q).symm (a ≫ t) =
      S.tensor.map (Prod.mkHom a (𝟙 P)) ≫ (S.transpose T P Q).symm t := by
  simpa [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
    Prod.sectR] using (S.adjunction P).homEquiv_naturality_left_symm a t

section ClosedCalculus

variable {A : Type*} [Category* A] {H : Aᵒᵖ × A ⥤ A}
  (S : CoefficientClosedStructure H)

private theorem evaluation_target (K N N' : A) (n : N ⟶ N') :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op K)) n)) (𝟙 K)) ≫
      S.evaluation K N' = S.evaluation K N ≫ n := by
  simpa [CoefficientClosedStructure.evaluation, CoefficientClosedStructure.tensor,
    Prod.sectR] using (S.adjunction K).counit.naturality n

private theorem evaluation_source (K K' N : A) (f : K' ⟶ K) :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 N))) (𝟙 K')) ≫
      S.evaluation K' N =
    S.tensor.map (Prod.mkHom (𝟙 (H.obj (op K, N))) f) ≫ S.evaluation K N := by
  simpa [CoefficientClosedStructure.evaluation, CoefficientClosedStructure.tensor,
    Prod.sectR] using S.evaluation_naturality K K' N f

private theorem evaluation_both (K K' N N' : A) (f : K' ⟶ K) (n : N ⟶ N') :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op n)) (𝟙 K')) ≫
      S.evaluation K' N' =
    S.tensor.map (Prod.mkHom (𝟙 (H.obj (op K, N))) f) ≫ S.evaluation K N ≫ n := by
  have hf : Prod.mkHom f.op n =
      Prod.mkHom f.op (𝟙 N) ≫ Prod.mkHom (𝟙 (op K')) n := by simp
  rw [hf, H.map_comp]
  have ht : Prod.mkHom
      (H.map (Prod.mkHom f.op (𝟙 N)) ≫ H.map (Prod.mkHom (𝟙 (op K')) n)) (𝟙 K') =
      Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 N))) (𝟙 K') ≫
        Prod.mkHom (H.map (Prod.mkHom (𝟙 (op K')) n)) (𝟙 K') := by simp
  rw [ht, S.tensor.map_comp, Category.assoc, evaluation_target,
    ← Category.assoc, evaluation_source, Category.assoc]

private theorem uncurry_naturality (X K K' N N' : A)
    (t : X ⟶ H.obj (op K, N)) (f : K' ⟶ K) (n : N ⟶ N') :
    (S.transpose X K' N').symm (t ≫ H.map (Prod.mkHom f.op n)) =
      S.tensor.map (Prod.mkHom (𝟙 X) f) ≫ (S.transpose X K N).symm t ≫ n := by
  rw [uncurry_formula, uncurry_formula]
  have ht : Prod.mkHom (t ≫ H.map (Prod.mkHom f.op n)) (𝟙 K') =
      Prod.mkHom t (𝟙 K') ≫ Prod.mkHom (H.map (Prod.mkHom f.op n)) (𝟙 K') := by simp
  rw [ht, S.tensor.map_comp, Category.assoc, evaluation_both]
  have ht' : Prod.mkHom t (𝟙 K') ≫ Prod.mkHom (𝟙 (H.obj (op K, N))) f =
      Prod.mkHom (𝟙 X) f ≫ Prod.mkHom t (𝟙 K) := by simp
  rw [← Category.assoc, ← Category.assoc, ← S.tensor.map_comp, ht', S.tensor.map_comp]
  simp only [Category.assoc]


end ClosedCalculus

private theorem tensorator_naturality {X Y : Site.{u, w}} {f : Morphism X Y}
    (l : AdjointLift f) {P P' Q Q' : Y.D} (a : P ⟶ P') (b : Q ⟶ Q') :
    X.closed.tensor.map (Prod.mkHom (l.edge.left.map a) (l.edge.left.map b)) ≫
        pullbackHomTensorator l P' Q' =
      pullbackHomTensorator l P Q ≫ l.edge.left.map (Y.closed.tensor.map (Prod.mkHom a b)) := by
  exact (l.edge.tensorComparison (pullbackHomTensorModel Y)
    (pullbackHomTensorModel X)).inv.naturality (Prod.mkHom a b)

private theorem comparison_evaluation {X Y : Site.{u, w}} {f : Morphism X Y}
    (l : AdjointLift f) (P Q : Y.D) :
    X.closed.tensor.map (Prod.mkHom (ringedPullbackHomComparison l P Q)
        (𝟙 (l.edge.left.obj P))) ≫
        X.closed.evaluation (l.edge.left.obj P) (l.edge.left.obj Q) =
      pullbackHomTensorator l ((pullbackHomFunctor Y).obj (op P, Q)) P ≫
        l.edge.left.map (Y.closed.evaluation P Q) := by
  rw [← uncurry_formula]
  exact (X.closed.transpose _ _ _).symm_apply_apply _

private theorem comparison_transpose {X Y : Site.{u, w}} {f : Morphism X Y}
    (l : AdjointLift f) (T P Q : Y.D) (t : Y.closed.tensor.obj (T, P) ⟶ Q) :
    l.edge.left.map (Y.closed.transpose T P Q t) ≫ ringedPullbackHomComparison l P Q =
      X.closed.transpose (l.edge.left.obj T) (l.edge.left.obj P) (l.edge.left.obj Q)
        (pullbackHomTensorator l T P ≫ l.edge.left.map t) := by
  apply (X.closed.transpose _ _ _).symm.injective
  rw [uncurry_precomp, Equiv.symm_apply_apply]
  change X.closed.tensor.map _ ≫
    (X.closed.transpose _ _ _).symm (X.closed.transpose _ _ _ _) = _
  rw [Equiv.symm_apply_apply, ← Category.assoc]
  have hn := tensorator_naturality l (Y.closed.transpose T P Q t) (𝟙 P)
  rw [Functor.map_id] at hn
  rw [hn, Category.assoc, ← Functor.map_comp, ← uncurry_formula,
    Equiv.symm_apply_apply]

set_option maxHeartbeats 800000 in
-- The site and coefficient types require extra elaboration of the comparison equations.
private theorem comparison_naturality {X Y : Site.{u, w}} {f : Morphism X Y}
    (l : AdjointLift f) (P P' Q Q' : Y.D) (a : P' ⟶ P) (b : Q ⟶ Q') :
    l.edge.left.map ((pullbackHomFunctor Y).map (Prod.mkHom a.op b)) ≫
        ringedPullbackHomComparison l P' Q' =
      ringedPullbackHomComparison l P Q ≫ (pullbackHomFunctor X).map
        (Prod.mkHom (l.edge.left.map a).op (l.edge.left.map b)) := by
  apply (X.closed.transpose _ _ _).symm.injective
  rw [uncurry_precomp, uncurry_naturality]
  change X.closed.tensor.map _ ≫
      (X.closed.transpose _ _ _).symm (X.closed.transpose _ _ _ _) =
    X.closed.tensor.map _ ≫
      (X.closed.transpose _ _ _).symm (X.closed.transpose _ _ _ _) ≫ _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, ← Category.assoc]
  have hn := tensorator_naturality l
    ((pullbackHomFunctor Y).map (Prod.mkHom a.op b)) (𝟙 P')
  rw [Functor.map_id] at hn
  rw [hn, Category.assoc, ← l.edge.left.map_comp, evaluation_both]
  simp only [l.edge.left.map_comp]
  have hn' := tensorator_naturality l (𝟙 ((pullbackHomFunctor Y).obj (op P, Q))) a
  rw [Functor.map_id] at hn'
  simpa only [Category.assoc] using
    congrArg (fun z ↦ z ≫ l.edge.left.map (Y.closed.evaluation P Q) ≫
      l.edge.left.map b) hn'.symm

set_option maxHeartbeats 800000 in
-- The site and coefficient types require extra elaboration of the comparison equations.
private theorem tensorator_associativity {X Y : Site.{u, w}} {f : Morphism X Y}
    (l : AdjointLift f) (P Q T : Y.D) :
    X.closed.tensor.map (Prod.mkHom (pullbackHomTensorator l P Q)
        (𝟙 (l.edge.left.obj T))) ≫
        pullbackHomTensorator l (Y.closed.tensor.obj (P, Q)) T ≫
        l.edge.left.map (Y.closed.monoidal.associator P Q T).hom =
      (X.closed.monoidal.associator (l.edge.left.obj P)
        (l.edge.left.obj Q) (l.edge.left.obj T)).hom ≫
        X.closed.tensor.map (Prod.mkHom (𝟙 (l.edge.left.obj P))
          (pullbackHomTensorator l Q T)) ≫
        pullbackHomTensorator l P (Y.closed.tensor.obj (Q, T)) := by
  obtain ⟨m⟩ := tensorLift_exists l.edge (pullbackHomTensorModel Y)
    (pullbackHomTensorModel X) (fun _ _ _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl)
  have he (U V : Y.D) :
      (@Functor.CoreMonoidal.μIso Y.D _ Y.closed.monoidal X.D _ X.closed.monoidal
        l.edge.left m.monoidal U V).hom = pullbackHomTensorator l U V := by
    have hi : (@Functor.CoreMonoidal.μIso Y.D _ Y.closed.monoidal
        X.D _ X.closed.monoidal l.edge.left m.monoidal U V).symm =
          (l.edge.tensorComparison (pullbackHomTensorModel Y)
            (pullbackHomTensorModel X)).app (U, V) :=
      Iso.ext (m.tensor_canonical U V)
    exact congrArg Iso.inv hi
  let _ := Y.closed.monoidal
  let _ := X.closed.monoidal
  simpa only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map,
    MonoidalCategory.tensor_obj, MonoidalCategory.tensorHom_id,
    MonoidalCategory.id_tensorHom, he] using
      m.monoidal.associativity P Q T

private theorem uncurry_composition {D : Type*} [Category* D]
    {H : Dᵒᵖ × D ⥤ D} (S : CoefficientClosedStructure H) (P Q T : D) :
    S.tensor.map (Prod.mkHom (S.composition P Q T) (𝟙 P)) ≫ S.evaluation P T =
      (S.monoidal.associator (H.obj (op Q, T)) (H.obj (op P, Q)) P).hom ≫
        S.tensor.map (Prod.mkHom (𝟙 (H.obj (op Q, T))) (S.evaluation P Q)) ≫
        S.evaluation Q T := by
  rw [← uncurry_formula]
  exact (S.transpose _ _ _).symm_apply_apply _

private theorem tensor_map_comp {D : Type*} [Category* D] (K : D × D ⥤ D)
    {A B C A' B' C' : D} (a : A ⟶ B) (b : B ⟶ C)
    (a' : A' ⟶ B') (b' : B' ⟶ C') :
    K.map (Prod.mkHom a a') ≫ K.map (Prod.mkHom b b') =
      K.map (Prod.mkHom (a ≫ b) (a' ≫ b')) := by
  rw [← K.map_comp]
  rfl

set_option maxHeartbeats 800000 in
-- The site and coefficient types require extra elaboration of the comparison equations.
private theorem double_evaluation_naturality {D : Type*} [Category* D]
    {H : Dᵒᵖ × D ⥤ D} (S : CoefficientClosedStructure H)
    {U V P Q T : D} (a : U ⟶ H.obj (op Q, T)) (b : V ⟶ H.obj (op P, Q)) :
    S.tensor.map (Prod.mkHom (S.tensor.map (Prod.mkHom a b)) (𝟙 P)) ≫
        S.tensor.map (Prod.mkHom (S.composition P Q T) (𝟙 P)) ≫
        S.evaluation P T =
      (S.monoidal.associator U V P).hom ≫
        S.tensor.map (Prod.mkHom (𝟙 U)
          (S.tensor.map (Prod.mkHom b (𝟙 P)) ≫ S.evaluation P Q)) ≫
        (S.tensor.map (Prod.mkHom a (𝟙 Q)) ≫ S.evaluation Q T) := by
  rw [uncurry_composition]
  let _ := S.monoidal
  change ((a ⊗ₘ b) ⊗ₘ 𝟙 P) ≫ (α_ _ _ _).hom ≫
      (𝟙 _ ⊗ₘ S.evaluation P Q) ≫ S.evaluation Q T =
    (α_ U V P).hom ≫ (𝟙 U ⊗ₘ ((b ⊗ₘ 𝟙 P) ≫ S.evaluation P Q)) ≫
      (a ⊗ₘ 𝟙 Q) ≫ S.evaluation Q T
  rw [MonoidalCategory.associator_naturality_assoc]
  simp only [MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    Category.id_comp, Category.comp_id]

private theorem tensor_first_comp {D : Type*} [Category* D] (K : D × D ⥤ D)
    {A B C : D} (a : A ⟶ B) (b : B ⟶ C) (P : D) :
    K.map (Prod.mkHom (a ≫ b) (𝟙 P)) =
      K.map (Prod.mkHom a (𝟙 P)) ≫ K.map (Prod.mkHom b (𝟙 P)) := by
  rw [tensor_map_comp, Category.id_comp]

private theorem closed_comparison_composition
    {A B : Type*} [Category* A] [Category* B]
    {H : Aᵒᵖ × A ⥤ A} {H' : Bᵒᵖ × B ⥤ B}
    (S : CoefficientClosedStructure H) (S' : CoefficientClosedStructure H')
    (F : A ⥤ B) (c : F.prod F ⋙ S'.tensor ⟶ S.tensor ⋙ F)
    (ha : ∀ P Q T : A,
      S'.tensor.map (Prod.mkHom (c.app (P, Q)) (𝟙 (F.obj T))) ≫
          c.app (S.tensor.obj (P, Q), T) ≫ F.map (S.monoidal.associator P Q T).hom =
        (S'.monoidal.associator (F.obj P) (F.obj Q) (F.obj T)).hom ≫
          S'.tensor.map (Prod.mkHom (𝟙 (F.obj P)) (c.app (Q, T))) ≫
          c.app (P, S.tensor.obj (Q, T)))
    (β : ∀ P Q : A, F.obj (H.obj (op P, Q)) ⟶ H'.obj (op (F.obj P), F.obj Q))
    (he : ∀ P Q : A,
      S'.tensor.map (Prod.mkHom (β P Q) (𝟙 (F.obj P))) ≫
          S'.evaluation (F.obj P) (F.obj Q) =
        c.app (H.obj (op P, Q), P) ≫ F.map (S.evaluation P Q))
    (P Q T : A) :
    c.app (H.obj (op Q, T), H.obj (op P, Q)) ≫
        F.map (S.composition P Q T) ≫ β P T =
      S'.tensor.map (Prod.mkHom (β Q T) (β P Q)) ≫
        S'.composition (F.obj P) (F.obj Q) (F.obj T) := by
  let U := H.obj (op Q, T)
  let V := H.obj (op P, Q)
  apply (S'.transpose _ _ _).symm.injective
  rw [uncurry_formula, uncurry_formula]
  simp only [tensor_first_comp, Category.assoc]
  rw [he, double_evaluation_naturality, he, he]
  have hn := c.naturality (Prod.mkHom (S.composition P Q T) (𝟙 P))
  change S'.tensor.map (Prod.mkHom (F.map (S.composition P Q T)) (F.map (𝟙 P))) ≫
      c.app (H.obj (op P, T), P) =
    c.app (S.tensor.obj (U, V), P) ≫
      F.map (S.tensor.map (Prod.mkHom (S.composition P Q T) (𝟙 P))) at hn
  rw [F.map_id] at hn
  rw [← Category.assoc _ _ (F.map (S.evaluation P T)), hn,
    Category.assoc, ← F.map_comp, uncurry_composition]
  simp only [F.map_comp]
  have hn' := c.naturality (Prod.mkHom (𝟙 U) (S.evaluation P Q))
  change S'.tensor.map (Prod.mkHom (F.map (𝟙 U)) (F.map (S.evaluation P Q))) ≫
      c.app (U, Q) =
    c.app (U, S.tensor.obj (V, P)) ≫
      F.map (S.tensor.map (Prod.mkHom (𝟙 U) (S.evaluation P Q))) at hn'
  rw [F.map_id] at hn'
  have hα := congrArg (fun z ↦ z ≫
    F.map (S.tensor.map (Prod.mkHom (𝟙 U) (S.evaluation P Q))) ≫
      F.map (S.evaluation Q T)) (ha U V P)
  simp only [Category.assoc] at hα
  rw [hα]
  have hne := congrArg (fun z ↦ z ≫ F.map (S.evaluation Q T)) hn'
  simp only [Category.assoc] at hne
  rw [← hne]
  have ht : S'.tensor.map (Prod.mkHom (𝟙 (F.obj U)) (c.app (V, P))) ≫
      S'.tensor.map (Prod.mkHom (𝟙 (F.obj U)) (F.map (S.evaluation P Q))) =
    S'.tensor.map (Prod.mkHom (𝟙 (F.obj U))
      (c.app (V, P) ≫ F.map (S.evaluation P Q))) := by
    rw [tensor_map_comp, Category.id_comp]
  simpa only [Category.assoc] using
    congrArg (fun z ↦
      (S'.monoidal.associator (F.obj U) (F.obj V) (F.obj P)).hom ≫ z ≫
        c.app (U, Q) ≫ F.map (S.evaluation Q T)) ht

private theorem comparison_composition {X Y : Site.{u, w}} {f : Morphism X Y}
    (l : AdjointLift f) (P Q T : Y.D) :
    pullbackHomTensorator l ((pullbackHomFunctor Y).obj (op Q, T))
        ((pullbackHomFunctor Y).obj (op P, Q)) ≫
        l.edge.left.map (Y.closed.composition P Q T) ≫
        ringedPullbackHomComparison l P T =
      X.closed.tensor.map (Prod.mkHom (ringedPullbackHomComparison l Q T)
        (ringedPullbackHomComparison l P Q)) ≫
        X.closed.composition (l.edge.left.obj P) (l.edge.left.obj Q)
          (l.edge.left.obj T) := by
  exact closed_comparison_composition Y.closed X.closed l.edge.left
    (l.edge.tensorComparison (pullbackHomTensorModel Y) (pullbackHomTensorModel X)).inv
    (tensorator_associativity l) (ringedPullbackHomComparison l)
    (comparison_evaluation l) P Q T

/-- Apply a degree-n Hom section through its actual product projection.
Source: Stacks 0A8X (blueprint: lem-coef-ringed-pullback-hom-evaluation-comparison). -/
def ringedHomSectionApply (X : Site.{u, w}) (L M : CochainComplex X.modules ℤ)
    (n p q : ℤ) (h : p + n = q) (U : X.Cᵒᵖ)
    (a : ((homComplex (R := X.A) L M).X n).val.obj U)
    (x : (L.X p).val.obj U) : (M.X q).val.obj U :=
  ((((coefficientHomComponent.{u, u, u} X.J X.A L M n p q h).val.app U a).app
    (op (Over.mk (𝟙 U.unop)))).hom) x

/-- The representative maps have no sign on evaluation or composition; their chain-map
conditions use the signed total tensor and d(h)=d h-(-1)^degree(h) h d.
Source: Stacks 0A8X, 0A90, 0A91, 0A98
(blueprint: lem-coef-ringed-pullback-hom-evaluation-comparison). -/
def RingedHomSignedRepresentatives (X : Site.{u, w}) : Prop :=
  ∀ L M N : CochainComplex X.modules ℤ,
    ∃ (e : (coefficientTotalTensor.{u, u, u} X.J X.A).obj
        (homComplex (R := X.A) L M, L) ⟶ M)
      (m : (coefficientTotalTensor.{u, u, u} X.J X.A).obj
        (homComplex (R := X.A) M N, homComplex (R := X.A) L M) ⟶
          homComplex (R := X.A) L N),
      (∀ (r p k : ℤ) (h : r + p = k) (h' : p + r = k) (U : X.Cᵒᵖ)
        (a : ((homComplex (R := X.A) L M).X r).val.obj U)
        (x : (L.X p).val.obj U),
        (e.f k).val.app U
          (coefficientTensorGenerator.{u, u, u} X.J X.A
            (homComplex (R := X.A) L M) L r p k h U a x) =
          ringedHomSectionApply X L M r p k h' U a x) ∧
      (∀ (s r k p q t : ℤ) (h : s + r = k) (hq : p + r = q)
        (ht : q + s = t) (ht' : p + k = t) (U : X.Cᵒᵖ)
        (a : ((homComplex (R := X.A) M N).X s).val.obj U)
        (b : ((homComplex (R := X.A) L M).X r).val.obj U)
        (x : (L.X p).val.obj U),
        ringedHomSectionApply X L N k p t ht' U
          ((m.f k).val.app U
            (coefficientTensorGenerator.{u, u, u} X.J X.A
              (homComplex (R := X.A) M N) (homComplex (R := X.A) L M)
              s r k h U a b)) x =
          ringedHomSectionApply X M N s q t ht U a
            (ringedHomSectionApply X L M r p q hq U b x))

private def unitEvaluation (X : Site.{u, w}) (M : CochainComplex X.modules ℤ) :
    homComplex (R := X.A) (homComplexUnitSource X.J X.A) M ≅ M := by
  letI (n : ℤ) : IsIso (homComplexUnitEvaluation X.J X.A M n) :=
    homComplex_unit_evaluation_isIso X.J X.A M n
  exact HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ asIso (homComplexUnitEvaluation X.J X.A M n))
    (fun n m h ↦ homComplex_unit_evaluation_comm X.J X.A M n m h)

private theorem unitEvaluation_formula (X : Site.{u, w})
    (M : CochainComplex X.modules ℤ) (n : ℤ) (U : X.Cᵒᵖ)
    (a : ((homComplex (R := X.A) (homComplexUnitSource X.J X.A) M).X n).val.obj U) :
    ((unitEvaluation X M).hom.f n).val.app U a =
      ringedHomSectionApply X (homComplexUnitSource X.J X.A) M n 0 n (zero_add n) U a
        (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
          (SheafOfModules.unit X.ring)).inv.val.app U) (1 : X.A.obj.obj U)) := by
  rfl

set_option maxHeartbeats 800000 in
-- The site and coefficient types require extra elaboration of the comparison equations.
private theorem tensor_generator_map (X : Site.{u, w})
    {P Q P' Q' : CochainComplex X.modules ℤ} (a : P ⟶ P') (b : Q ⟶ Q')
    (r p k : ℤ) (h : r + p = k) (U : X.Cᵒᵖ)
    (x : (P.X r).val.obj U) (y : (Q.X p).val.obj U) :
    (((coefficientTotalTensor.{u, u, u} X.J X.A).map (Prod.mkHom a b)).f k).val.app U
        (coefficientTensorGenerator.{u, u, u} X.J X.A P Q r p k h U x y) =
      coefficientTensorGenerator.{u, u, u} X.J X.A P' Q' r p k h U
        ((a.f r).val.app U x) ((b.f p).val.app U y) := by
  subst k
  let := SheafOfModules.monoidalCategory X.A
  have hmap : (coefficientTotalTensor.{u, u, u} X.J X.A).map (Prod.mkHom a b) =
      HomologicalComplex.mapBifunctorMap a b
        (MonoidalCategory.curriedTensor X.modules) (.up ℤ) := by
    change HomologicalComplex.mapBifunctorMap a (𝟙 Q)
        (MonoidalCategory.curriedTensor X.modules) (.up ℤ) ≫
      HomologicalComplex.mapBifunctorMap (𝟙 P') b
        (MonoidalCategory.curriedTensor X.modules) (.up ℤ) = _
    simp only [HomologicalComplex.mapBifunctorMap, Functor.map_id, NatTrans.id_app,
      Category.id_comp, Category.comp_id, ← HomologicalComplex₂.total.map_comp]
  rw [hmap]
  have ht := HomologicalComplex.ι_mapBifunctorMap a b
    (MonoidalCategory.curriedTensor X.modules) (.up ℤ) r p (r + p) rfl
  have hs := homTensorSectionMap_natural X.A (a.f r) (b.f p)
  have he := congrArg (fun t :
      (P.X r ⊗ Q.X p) ⟶
        (CochainComplex.mapBifunctor P' Q' (MonoidalCategory.curriedTensor X.modules)).X
          (r + p) ↦
      (t.val.app U).hom
        (((homTensorSectionMap X.A (P.X r) (Q.X p)).app U).hom
          (x ⊗ₜ[X.A.obj.obj U] y))) ht
  have he' := congrArg (fun t ↦ (t.app U).hom (x ⊗ₜ[X.A.obj.obj U] y)) hs
  change ((a.f r ⊗ₘ b.f p).val.app U).hom
    (((homTensorSectionMap X.A (P.X r) (Q.X p)).app U).hom
      (x ⊗ₜ[X.A.obj.obj U] y)) = _ at he'
  change _ = ((homTensorSectionMap X.A (P'.X r) (Q'.X p)).app U).hom
    ((((a.f r).val ⊗ₘ (b.f p).val).app U).hom (x ⊗ₜ[X.A.obj.obj U] y)) at he'
  erw [PresheafOfModules.tensorHom_app, ModuleCat.MonoidalCategory.tensorHom_tmul] at he'
  change _ = ((CochainComplex.ιMapBifunctor P' Q'
    (MonoidalCategory.curriedTensor X.modules) r p (r + p) rfl).val.app U).hom
    (((a.f r ⊗ₘ b.f p).val.app U).hom
      (((homTensorSectionMap X.A (P.X r) (Q.X p)).app U).hom
        (x ⊗ₜ[X.A.obj.obj U] y))) at he
  exact he.trans (congrArg _ he')

set_option maxHeartbeats 800000 in
-- The site and coefficient types require extra elaboration of the comparison equations.
private theorem signed_representatives (X : Site.{u, w}) :
    RingedHomSignedRepresentatives X := by
  intro L M N
  obtain ⟨m, hm, _⟩ := ringedHomComposition_existsUnique.{u, u, u} X.J X.A L M N
  let O := homComplexUnitSource X.J X.A
  obtain ⟨v, hv, _⟩ := ringedHomComposition_existsUnique.{u, u, u} X.J X.A O L M
  let e := (coefficientTotalTensor.{u, u, u} X.J X.A).map
    (Prod.mkHom (𝟙 (homComplex (R := X.A) L M)) (unitEvaluation X L).inv) ≫
      v ≫ (unitEvaluation X M).hom
  refine ⟨e, m, ?_, ?_⟩
  · intro r p k h h' U a x
    change ((unitEvaluation X M).hom.f k).val.app U
      ((v.f k).val.app U
        ((((coefficientTotalTensor.{u, u, u} X.J X.A).map
          (Prod.mkHom (𝟙 (homComplex (R := X.A) L M)) (unitEvaluation X L).inv)).f k).val.app U
          (coefficientTensorGenerator.{u, u, u} X.J X.A
            (homComplex (R := X.A) L M) L r p k h U a x))) = _
    rw [tensor_generator_map]
    simp only [HomologicalComplex.id_f, SheafOfModules.id_val,
      PresheafOfModules.id_app, ModuleCat.id_apply]
    rw [unitEvaluation_formula]
    have hc (j : ℤ) (hj : 0 + p = j) (hr : j + r = k) :
        (coefficientHomComponent.{u, u, u} X.J X.A O M k 0 k (zero_add k)).val.app U
          ((v.f k).val.app U
            (coefficientTensorGenerator.{u, u, u} X.J X.A
              (homComplex (R := X.A) L M) (homComplex (R := X.A) O L)
              r p k h U a (((unitEvaluation X L).inv.f p).val.app U x))) =
        (coefficientHomComponent.{u, u, u} X.J X.A O L p 0 j hj).val.app U
            (((unitEvaluation X L).inv.f p).val.app U x) ≫
          (coefficientHomComponent.{u, u, u} X.J X.A L M r j k hr).val.app U a := by
      subst j
      exact hv r p k 0 k h (zero_add k) hr U a
        (((unitEvaluation X L).inv.f p).val.app U x)
    have he := congrArg (fun z ↦
      (z.app (op (Over.mk (𝟙 U.unop)))).hom
        (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
          (SheafOfModules.unit X.ring)).inv.val.app U) (1 : X.A.obj.obj U)))
      (hc p (zero_add p) h')
    change _ = ringedHomSectionApply X L M r p k h' U a
      (ringedHomSectionApply X (homComplexUnitSource X.J X.A) L p 0 p (zero_add p) U
        (((unitEvaluation X L).inv.f p).val.app U x)
        (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
          (SheafOfModules.unit X.ring)).inv.val.app U) (1 : X.A.obj.obj U))) at he
    rw [← unitEvaluation_formula] at he
    have hi := congrArg (fun z : L ⟶ L ↦ (z.f p).val.app U x)
      (unitEvaluation X L).inv_hom_id
    change ((unitEvaluation X L).hom.f p).val.app U
      (((unitEvaluation X L).inv.f p).val.app U x) = x at hi
    rw [hi] at he
    exact he
  · intro s r k p q t h hq ht ht' U a b x
    subst q
    have hc := hm s r k p t h ht' ht U a b
    exact congrArg (fun z ↦ (z.app (op (Over.mk (𝟙 U.unop)))).hom x) hc

/-- Evaluation mates for arbitrary small ringed-topos morphisms, on the fixed unbounded
module derived categories. The supplied `AdjointLift` presents Lf*, not an additional
flatness or closed-functor hypothesis.
Source: Stacks 07A4, 08J9, 0A98 and the agent's evaluation-mate coherence calculation
(blueprint: lem-coef-ringed-pullback-hom-evaluation-comparison).

Proof:
1. Use the supplied normalized adjoint lift and restrict the fixed tensor models to
   flat-term K-flat representatives. Their comparison maps are the specified ones.
2. Apply `tensorLift_exists` to obtain associativity for the canonical tensorator c.
   The representative comparison hypotheses are definitional equalities.
3. Define beta as the transpose of c followed by F(evaluation). Inverse transposition
   gives its evaluation equation.
4. Untranspose naturality. Naturality of c and of evaluation identifies both sides.
5. Untranspose the transposition identity and use naturality of c once more.
6. Internal composition is the transpose of iterated evaluation and the associator.
7. Untranspose the composition identity, substitute the evaluation equations twice,
   and use associativity of c and naturality of the associators.
8. Take the uniquely specified composition map of signed Hom complexes. Evaluation on
   the coefficient unit O identifies Hom(O,L) with L by the specified degreewise maps
   and their differential compatibility. Compose Hom(L,M) tensor Hom(O,L) to Hom(O,M)
   and conjugate by these unit-evaluation isomorphisms to obtain evaluation. On a tensor
   generator its component formula is h(u_L(u_L inverse(x))) = h(x). The composition
   representative formula is the stated component formula of the same composition map.
   No inverse to beta is used. -/
theorem ringedPullbackHomEvaluationComparison {X Y : Site.{u, w}} {f : Morphism X Y}
    (l : AdjointLift f) :
    (∀ (P P' Q Q' : Y.D) (a : P' ⟶ P) (b : Q ⟶ Q'),
      l.edge.left.map ((pullbackHomFunctor Y).map (Prod.mkHom a.op b)) ≫
          ringedPullbackHomComparison l P' Q' =
        ringedPullbackHomComparison l P Q ≫
          (pullbackHomFunctor X).map
            (Prod.mkHom (l.edge.left.map a).op (l.edge.left.map b))) ∧
    (∀ P Q : Y.D,
      X.closed.tensor.map
          (X := (l.edge.left.obj ((pullbackHomFunctor Y).obj (op P, Q)), l.edge.left.obj P))
          (Y := ((pullbackHomFunctor X).obj (op (l.edge.left.obj P), l.edge.left.obj Q),
            l.edge.left.obj P))
          (Prod.mkHom (ringedPullbackHomComparison l P Q) (𝟙 (l.edge.left.obj P))) ≫
          X.closed.evaluation (l.edge.left.obj P) (l.edge.left.obj Q) =
        pullbackHomTensorator l ((pullbackHomFunctor Y).obj (op P, Q)) P ≫
          l.edge.left.map (Y.closed.evaluation P Q)) ∧
    (∀ (T P Q : Y.D) (t : Y.closed.tensor.obj (T, P) ⟶ Q),
      l.edge.left.map (Y.closed.transpose T P Q t) ≫ ringedPullbackHomComparison l P Q =
        X.closed.transpose (l.edge.left.obj T) (l.edge.left.obj P) (l.edge.left.obj Q)
          (pullbackHomTensorator l T P ≫ l.edge.left.map t)) ∧
    (∀ P Q T : Y.D,
      pullbackHomTensorator l ((pullbackHomFunctor Y).obj (op Q, T))
          ((pullbackHomFunctor Y).obj (op P, Q)) ≫
          l.edge.left.map (Y.closed.composition P Q T) ≫
          ringedPullbackHomComparison l P T =
        X.closed.tensor.map
          (X := (l.edge.left.obj ((pullbackHomFunctor Y).obj (op Q, T)),
            l.edge.left.obj ((pullbackHomFunctor Y).obj (op P, Q))))
          (Y := ((pullbackHomFunctor X).obj (op (l.edge.left.obj Q), l.edge.left.obj T),
            (pullbackHomFunctor X).obj (op (l.edge.left.obj P), l.edge.left.obj Q)))
          (Prod.mkHom (ringedPullbackHomComparison l Q T) (ringedPullbackHomComparison l P Q)) ≫
          X.closed.composition (l.edge.left.obj P) (l.edge.left.obj Q) (l.edge.left.obj T)) ∧
    RingedHomSignedRepresentatives X ∧ RingedHomSignedRepresentatives Y := by
  exact ⟨comparison_naturality l, comparison_evaluation l, comparison_transpose l,
    comparison_composition l, signed_representatives X, signed_representatives Y⟩

end CategoryTheory.RingedDerivedComparisons
