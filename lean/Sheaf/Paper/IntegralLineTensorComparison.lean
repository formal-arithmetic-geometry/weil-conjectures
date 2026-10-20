/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q135
-/
module

public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Paper.IntegralCompletionUnitCriterion
import Sheaf.Paper.IntegralLineRoosTensor
import Sheaf.Paper.IntegralFiniteTensorComparison

/-!
# Ordinary and completed tensor with an integral coefficient line

Source: Bhatt--Scholze, Definition 3.4.10, Lemma 3.4.12(4), Proposition 3.5.1 and
Definition 3.5.2 (blueprint: lem-sf-integral-line-tensor-comparison).
The comparison is the recorded completion unit, whose representative is the map
(c,0) into Cone(1-s)[-1]. Finite comparisons are normalized on sheafified pure
tensors; the projection equation uses the actual cone projections.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace WeilConjectures
open IntegralOnSlice

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : AlgebraicGeometry.Scheme.{t})

/-- The line is placed in degree zero, using the existing single-complex functor.
Source: Bhatt--Scholze, Definition 3.4.10
(blueprint: lem-sf-integral-line-tensor-comparison). -/
def integralLineSingle : Mod l E X none ⥤ Cx l E X none :=
  HomologicalComplex.single _ (ComplexShape.up ℤ) 0

/-- Ordinary derived tensor with a sheaf in degree zero. The tensor model is the
recorded total tensor on K-flat representatives. Source: Stacks 06YN, 06YY
(blueprint: lem-sf-integral-line-tensor-comparison). -/
def integralLineOrdinary : (D l E X none) × (Mod l E X none) ⥤ D l E X none :=
  ((𝟭 (D l E X none)).prod (integralLineSingle l E X ⋙ DerivedCategory.Q)) ⋙
    (duality l E X none).closed.tensor

/-- The recorded completed tensor with the same degree-zero line.
Source: Bhatt--Scholze, Definition 3.4.10
(blueprint: lem-sf-integral-line-tensor-comparison). -/
def integralLineCompleted : (D l E X none) × (Mod l E X none) ⥤ D l E X none :=
  ((𝟭 (D l E X none)).prod (integralLineSingle l E X ⋙ DerivedCategory.Q)) ⋙
    completedTensor l E X none

/-- The canonical comparison, with its existing (c,0) cone normalization.
Source: Bhatt--Scholze, Definition 3.5.2
(blueprint: lem-sf-integral-line-tensor-comparison). -/
def integralLineComparison : integralLineOrdinary l E X ⟶ integralLineCompleted l E X :=
  Functor.whiskerLeft (integralLineOrdinary l E X) (completionUnit l E X none)

/-- The ordinary total complex P tensor T[0], with the signed direct-sum differential.
Source: Stacks 06YN (blueprint: lem-sf-integral-line-tensor-comparison). -/
def integralLineComplex (P : Cx l E X none) (T : Mod l E X none) : Cx l E X none :=
  (coefficientTotalTensor.{u, t + 1, t} (topology X none) (ring l E X none)).obj
    (P, (integralLineSingle l E X).obj T)

/-- Canonical K-flat representative comparison, transported along QP isomorphic to C.
Source: Stacks 06YY (blueprint: lem-sf-integral-line-tensor-comparison). -/
def integralLineRepresentativeIso (P : (Good l E X none).FullSubcategory)
    (T : Mod l E X none)
    (hT : CochainComplex.IsKFlatIndependentCoefficients
      (J := topology X none) (R := ring l E X none) ((integralLineSingle l E X).obj T))
    (C : D l E X none) (e : DerivedCategory.Q.obj P.obj ≅ C) :
    DerivedCategory.Q.obj (integralLineComplex l E X P.obj T) ≅
      (integralLineOrdinary l E X).obj (C, T) :=
  ((duality l E X none).models.iso (topology X none) (ring l E X none)
      (duality l E X none).closed P.obj ((integralLineSingle l E X).obj T) P.property.1 hT) ≪≫
    (duality l E X none).closed.tensor.mapIso (Iso.prod e (Iso.refl _))

/-- The finite scalar-extension complex, before restoring the completed-ring action.
Source: Stacks 06YY (blueprint: lem-sf-integral-line-tensor-comparison). -/
def integralLineFiniteComplex (n : ℕ) :=
  (reduction l E X none n).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Total tensor of the two ordinary finite reductions, over the finite ring.
Source: Stacks 06YY (blueprint: lem-sf-integral-line-tensor-comparison). -/
def integralLineFiniteTensor (P : Cx l E X none) (T : Mod l E X none) (n : ℕ) :=
  (coefficientTotalTensor.{u, t + 1, t} (topology X none) (finite l E X none n)).obj
    ((integralLineFiniteComplex l E X n).obj P,
      (integralLineFiniteComplex l E X n).obj ((integralLineSingle l E X).obj T))

/-- Restriction along the actual finite quotient projection, applied to complexes.
Source: Stacks 06YY (blueprint: lem-sf-integral-line-tensor-comparison). -/
def integralLineFiniteRestrict (n : ℕ) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (projection l E X none n))).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The actual projection from the strict Roos complex to its nth quotient.
Source: Stacks 08TC (blueprint: lem-sf-integral-line-tensor-comparison). -/
def integralLineRoosProjection (S : Cx l E X none) (n : ℕ) :
    integralOperationsRoos ((tower l E X none).obj S) ⟶
      ((level l E X none n).obj S) :=
  CochainComplex.mappingCocone.fst
      (towerTransitionEndomorphism
        (K := fun m : ℕ ↦ ((tower l E X none).obj S).obj (op m))
        (integralOperationsTowerStep ((tower l E X none).obj S))) ≫
    Pi.π (fun m : ℕ ↦ ((tower l E X none).obj S).obj (op m)) n

-- Keep the categorical proofs from unfolding the chosen tensor and completion models.
attribute [local irreducible] SheafOfModules.monoidalCategory coefficientTotalTensor
  IntegralOnSlice.duality IntegralOnSlice.completion integralLineRepresentativeIso
  IntegralOnSlice.ring IntegralOnSlice.finite IntegralOnSlice.reductionWitness
  IntegralOnSlice.reduction

private theorem roosUnit_projection (S : Cx l E X none) (n : ℕ) :
    roosUnit l E X none S ≫ integralLineRoosProjection l E X S n =
      ((augmentation l E X none).app S).app (op n) := by
  simp only [integralLineRoosProjection, roosUnit, ← Category.assoc,
    CochainComplex.mappingCocone.lift_fst, productAugmentation, Pi.lift_π]

private theorem unit_conjugate {A : Type*} [Category A] (F : A ⥤ A)
    (η : 𝟭 A ⟶ F) {M N : A} (r : M ≅ N) :
    r.hom ≫ η.app N ≫ F.map r.inv = η.app M := by
  have hn := η.naturality r.hom
  dsimp only [Functor.id_map] at hn
  rw [← Category.assoc, hn, Category.assoc, ← F.map_comp,
    r.hom_inv_id, F.map_id, Category.comp_id]

private theorem exists_goodRepresentative (C : D l E X none) :
    ∃ P : (Good l E X none).FullSubcategory,
      Nonempty (DerivedCategory.Q.obj P.obj ≅ C) := by
  classical
  let : EssentiallySmall.{max u (t + 1)} (Site X none) := essentiallySmallSelf _
  let Q := DerivedCategory.Q (C := Mod l E X none)
  let K := Q.objPreimage C
  obtain ⟨P, f, hP, hflat, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := ring l E X none) K
  let := hf
  have hg : Good l E X none P := by
    refine ⟨hP, ?_⟩
    intro i
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (ring l E X none) (P.X i)).symm (hflat i)
  exact ⟨⟨P, hg⟩, ⟨asIso (Q.map f) ≪≫ Q.objObjPreimageIso C⟩⟩

private theorem integralLineComparison_normalization
    (P : (Good l E X none).FullSubcategory) (T : Mod l E X none)
    (hT : CochainComplex.IsKFlatIndependentCoefficients
      (J := topology X none) (R := ring l E X none) ((integralLineSingle l E X).obj T))
    (hS : Good l E X none (integralLineComplex l E X P.obj T))
    (C : D l E X none) (e : DerivedCategory.Q.obj P.obj ≅ C) :
    (integralLineRepresentativeIso l E X P T hT C e).hom ≫
        (integralLineComparison l E X).app (C, T) ≫
        (completion l E X none).map
          (integralLineRepresentativeIso l E X P T hT C e).inv ≫
        (completionComparison l E X none).hom.app
          ⟨integralLineComplex l E X P.obj T, hS⟩ =
      DerivedCategory.Q.map (roosUnit l E X none (integralLineComplex l E X P.obj T)) := by
  have h := unit_conjugate (completion l E X none) (completionUnit l E X none)
    (integralLineRepresentativeIso l E X P T hT C e)
  have h' := congrArg
    (fun f ↦ f ≫ (completionComparison l E X none).hom.app
      ⟨integralLineComplex l E X P.obj T, hS⟩) h
  simpa only [integralLineComparison, Functor.whiskerLeft_app, Category.assoc] using
    h'.trans ((completionUnit_existsUnique l E X none).exists.choose_spec
      ⟨integralLineComplex l E X P.obj T, hS⟩)

private theorem integralLineComparison_projection
    (P : (Good l E X none).FullSubcategory) (T : Mod l E X none)
    (hT : CochainComplex.IsKFlatIndependentCoefficients
      (J := topology X none) (R := ring l E X none) ((integralLineSingle l E X).obj T))
    (hS : Good l E X none (integralLineComplex l E X P.obj T))
    (C : D l E X none) (e : DerivedCategory.Q.obj P.obj ≅ C) (n : ℕ)
    (β : (integralLineFiniteComplex l E X n).obj
        (integralLineComplex l E X P.obj T) ≅ integralLineFiniteTensor l E X P.obj T n) :
    (integralLineComparison l E X).app (C, T) ≫
        (completion l E X none).map
          (integralLineRepresentativeIso l E X P T hT C e).inv ≫
        (completionComparison l E X none).hom.app
          ⟨integralLineComplex l E X P.obj T, hS⟩ ≫
        DerivedCategory.Q.map
          (integralLineRoosProjection l E X (integralLineComplex l E X P.obj T) n ≫
            (integralLineFiniteRestrict l E X n).map β.hom) =
      (integralLineRepresentativeIso l E X P T hT C e).inv ≫
        DerivedCategory.Q.map
          (((augmentation l E X none).app (integralLineComplex l E X P.obj T)).app
            (op n) ≫ (integralLineFiniteRestrict l E X n).map β.hom) := by
  apply (cancel_epi (integralLineRepresentativeIso l E X P T hT C e).hom).1
  simp only [Iso.hom_inv_id_assoc]
  calc
    _ = DerivedCategory.Q.map
          (roosUnit l E X none (integralLineComplex l E X P.obj T)) ≫
        DerivedCategory.Q.map
          (integralLineRoosProjection l E X (integralLineComplex l E X P.obj T) n ≫
            (integralLineFiniteRestrict l E X n).map β.hom) := by
      rw [← integralLineComparison_normalization l E X P T hT hS C e]
      simp only [Category.assoc]
    _ = _ := by
      let Q := DerivedCategory.Q (C := Mod l E X none)
      have hp := congrArg
        (fun f ↦ f ≫ (integralLineFiniteRestrict l E X n).map β.hom)
        (roosUnit_projection l E X (integralLineComplex l E X P.obj T) n)
      have hp' := congrArg Q.map hp
      exact (Q.map_comp _ _).symm.trans
        ((congrArg Q.map (Category.assoc _ _ _).symm).trans hp')

/-- Tensor by a locally free integral line commutes with the specified completion.
Source: Bhatt--Scholze, Definition 3.4.10, Lemma 3.4.12(4), Proposition 3.5.1 and
Definition 3.5.2 (blueprint: lem-sf-integral-line-tensor-comparison).

Proof: (1) Choose a flat-term K-flat representative P of C, transporting the exact
monoidal tensor-right condition to flatness on the site. The completion-unit
criterion makes the specified completionUnit invertible at C. Naturality along
QP isomorphic to C and the recorded completionComparison then make Q(roosUnit P)
invertible. Thus roosUnit P is a quasi-isomorphism.
(2) The strict line/Roos comparison makes T[0] K-flat, preserves this
quasi-isomorphism under tensor, and identifies its composite with roosUnit of
P tensor T[0]. Its localization is therefore invertible. Conjugating the
completion unit by integralLineRepresentativeIso proves the asserted isomorphism.
(3) Naturality is the naturality of integralLineComparison itself. Conjugating the
unit by the representative isomorphism and applying its defining normalization
proves the precise representative equation for every good P.
(4) The finite total-tensor scalar-extension comparison supplies beta with its
balanced pure-tensor formula. The cocone lift-fst equation followed by the product
projection says that roosUnit followed by the actual nth Roos projection is the
recorded augmentation. Compose the representative equation with the restricted
beta and cancel the representative isomorphism to obtain the projection equation.
No boundedness, constructibility or quasi-compactness is used. -/
theorem integralLineTensorComparison
    (_hl : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (C : D l E X none) (hC : IsComplete l E X none C)
    (T : Mod l E X none) [T.IsFiniteLocallyFreeOfRank 1] :
    IsIso ((integralLineComparison l E X).app (C, T)) ∧
    (∀ (C' : D l E X none) (_hC' : IsComplete l E X none C') (f : C ⟶ C')
        (T' : Mod l E X none) [T'.IsFiniteLocallyFreeOfRank 1] (eT : T ≅ T'),
      (integralLineOrdinary l E X).map (f, eT.hom) ≫
          (integralLineComparison l E X).app (C', T') =
        (integralLineComparison l E X).app (C, T) ≫
          (integralLineCompleted l E X).map (f, eT.hom)) ∧
    ∀ (P : (Good l E X none).FullSubcategory) (e : DerivedCategory.Q.obj P.obj ≅ C),
      ∃ (hT : CochainComplex.IsKFlatIndependentCoefficients
          (J := topology X none) (R := ring l E X none)
          ((integralLineSingle l E X).obj T))
        (hS : Good l E X none (integralLineComplex l E X P.obj T)),
        (integralLineRepresentativeIso l E X P T hT C e).hom ≫
            (integralLineComparison l E X).app (C, T) ≫
            (completion l E X none).map
              (integralLineRepresentativeIso l E X P T hT C e).inv ≫
            (completionComparison l E X none).hom.app
              ⟨integralLineComplex l E X P.obj T, hS⟩ =
          DerivedCategory.Q.map (roosUnit l E X none (integralLineComplex l E X P.obj T)) ∧
        ∀ n : ℕ, ∃ β :
            (integralLineFiniteComplex l E X n).obj (integralLineComplex l E X P.obj T) ≅
              integralLineFiniteTensor l E X P.obj T n,
          (∀ (p q k : ℤ) (hpq : p + q = k) (V : X.ProEtᵒᵖ)
              (a : (finite l E X none n).obj.obj V)
              (x : (P.obj.X p).val.obj V)
              (y : (((integralLineSingle l E X).obj T).X q).val.obj V),
            (β.hom.f k).val.app V
                (generator l E X none n ((integralLineComplex l E X P.obj T).X k) V a
                  (coefficientTensorGenerator.{u, t + 1, t} (topology X none)
                    (ring l E X none) P.obj ((integralLineSingle l E X).obj T)
                    p q k hpq V x y)) =
              coefficientTensorGenerator.{u, t + 1, t} (topology X none)
                (finite l E X none n) ((integralLineFiniteComplex l E X n).obj P.obj)
                ((integralLineFiniteComplex l E X n).obj ((integralLineSingle l E X).obj T))
                p q k hpq V (generator l E X none n (P.obj.X p) V a x)
                (generator l E X none n (((integralLineSingle l E X).obj T).X q) V 1 y)) ∧
          (integralLineComparison l E X).app (C, T) ≫
              (completion l E X none).map
                (integralLineRepresentativeIso l E X P T hT C e).inv ≫
              (completionComparison l E X none).hom.app
                ⟨integralLineComplex l E X P.obj T, hS⟩ ≫
              DerivedCategory.Q.map
                (integralLineRoosProjection l E X (integralLineComplex l E X P.obj T) n ≫
                  (integralLineFiniteRestrict l E X n).map β.hom) =
            (integralLineRepresentativeIso l E X P T hT C e).inv ≫
              DerivedCategory.Q.map
                (((augmentation l E X none).app (integralLineComplex l E X P.obj T)).app
                    (op n) ≫ (integralLineFiniteRestrict l E X n).map β.hom) := by
  classical
  have hline := integralLine_roosTensor l E X T
  have hT := hline.1
  have hQI := hline.2.1
  have hroos := hline.2.2
  let F := (Functor.prod' (𝟭 (Cx l E X none))
    ((Functor.const (Cx l E X none)).obj ((integralLineSingle l E X).obj T))) ⋙
      coefficientTotalTensor.{u, t + 1, t} (topology X none) (ring l E X none)
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨P, ⟨e⟩⟩ := exists_goodRepresentative l E X C
    have hS := (hroos P).1
    let ρ := (hroos P).2.choose
    have hρ := (hroos P).2.choose_spec
    let := integralCompletionUnit_isIso l E X C hC
    have : IsIso ((completionUnit l E X none).app (DerivedCategory.Q.obj P.obj)) := by
      rw [← unit_conjugate (completion l E X none) (completionUnit l E X none) e]
      infer_instance
    have : IsIso (DerivedCategory.Q.map (roosUnit l E X none P.obj)) := by
      have hp := (completionUnit_existsUnique l E X none).exists.choose_spec P
      change (completionUnit l E X none).app (DerivedCategory.Q.obj P.obj) ≫
        (completionComparison l E X none).hom.app P = _ at hp
      rw [← hp]
      infer_instance
    have hu : QuasiIso (roosUnit l E X none P.obj) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 inferInstance
    have : QuasiIso (F.map (roosUnit l E X none P.obj)) := hQI _ _ _ hu
    have : IsIso (DerivedCategory.Q.map
        (roosUnit l E X none (integralLineComplex l E X P.obj T))) := by
      have hρ' : F.map (roosUnit l E X none P.obj) ≫ ρ.hom =
          roosUnit l E X none (integralLineComplex l E X P.obj T) := hρ
      rw [← hρ', (DerivedCategory.Q (C := Mod l E X none)).map_comp]
      infer_instance
    let r := integralLineRepresentativeIso l E X P T hT C e
    let v := (completion l E X none).map r.inv ≫
      (completionComparison l E X none).hom.app
        ⟨integralLineComplex l E X P.obj T, hS⟩
    have hn := integralLineComparison_normalization l E X P T hT hS C e
    have hi : IsIso (r.hom ≫ ((integralLineComparison l E X).app (C, T) ≫ v)) := by
      have hn' : r.hom ≫ ((integralLineComparison l E X).app (C, T) ≫ v) =
          DerivedCategory.Q.map (roosUnit l E X none
            (integralLineComplex l E X P.obj T)) := hn
      rw [hn']
      infer_instance
    have hi' := (isIso_comp_left_iff r.hom
      ((integralLineComparison l E X).app (C, T) ≫ v)).1 hi
    exact (isIso_comp_right_iff ((integralLineComparison l E X).app (C, T)) v).1 hi'
  · intro C' hC' f T' hT' eT
    exact (integralLineComparison l E X).naturality
      ((f, eT.hom) : (C, T) ⟶ (C', T'))
  · intro P e
    have hS := (hroos P).1
    refine ⟨hT, hS, integralLineComparison_normalization l E X P T hT hS C e, ?_⟩
    intro n
    obtain ⟨β, hβ⟩ := integralFiniteTensorComparison l E X P.obj
      ((integralLineSingle l E X).obj T) n
    exact ⟨β, hβ, integralLineComparison_projection l E X P T hT hS C e n β⟩

end WeilConjectures
