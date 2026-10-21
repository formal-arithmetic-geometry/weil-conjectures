/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SecSmoothPurity.CochainTensorCoherenceData
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

public import Sheaf.Paper.RingedTopoiTensorSections
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Sheaf.CategoryTheory.DiagramSiteRealization
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Paper.RingedTopoiTensorComparisonConstruction
import Sheaf.Paper.KFlatRingedToposPullback

/-! # Normalized derived pullback of strict reduction towers

Source: Stacks Project, Tags 06YS, 06YY, 07A4 and 03EL
(blueprint: lem-weil-pbc-reduction-pullback-derived-tower).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe a b c d w w' t t'
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace CategoryTheory.StrictReduction

variable {A : Type a} [Category.{b} A] [Abelian A] [MonoidalCategory A]

/-- Tensor with the actual coefficient tower, retaining every transition.
Source: Stacks 06YY, applied to strict towers
(blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
def reduction (Q : ℕᵒᵖ ⥤ A) : A ⥤ (ℕᵒᵖ ⥤ A) :=
  Functor.const ℕᵒᵖ ⋙ tensorRight Q

/-- The ordinary augmentation induced by the coefficient unit.
Source: Stacks 03CZ and 06YY
(blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
def augmentation (Q : ℕᵒᵖ ⥤ A) (e : (Functor.const ℕᵒᵖ).obj (𝟙_ A) ⟶ Q) :
    Functor.const ℕᵒᵖ ⟶ reduction Q :=
  Functor.whiskerLeft (Functor.const ℕᵒᵖ)
    ((rightUnitorNatIso (ℕᵒᵖ ⥤ A)).inv ≫ (curriedTensor (ℕᵒᵖ ⥤ A)).flip.map e)

variable [MonoidalPreadditive A]

/-- Additivity of termwise tensor reduction.
Source: Stacks 03EK, bilinearity of tensor
(blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
instance reduction_additive (Q : ℕᵒᵖ ⥤ A) : (reduction Q).Additive where
  map_add {M N} f g := by
    ext n
    change (f + g) ▷ Q.obj n = f ▷ Q.obj n + g ▷ Q.obj n
    exact (tensorRight (Q.obj n)).map_add (f := f) (g := g)

/-- Exact termwise pullback on strict towers.
Source: Stacks 02MZ, limits and colimits in diagram categories
(blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
abbrev termwise {B : Type c} [Category.{d} B] (F : A ⥤ B) :=
  (Functor.whiskeringRight ℕᵒᵖ A B).obj F

variable {B : Type c} [Category.{d} B] [Abelian B]

/-- Termwise preservation of finite limits, using pointwise limits.
Source: Stacks 02MZ (blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
instance termwise_limits (F : A ⥤ B) [PreservesFiniteLimits F] :
    PreservesFiniteLimits (termwise F) where
  preservesFiniteLimits L := preservesLimitsOfShape_of_evaluation _ L (fun n ↦
    inferInstanceAs (PreservesLimitsOfShape L ((evaluation ℕᵒᵖ A).obj n ⋙ F)))

/-- Termwise preservation of finite colimits, using pointwise colimits.
Source: Stacks 02MZ (blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
instance termwise_colimits (F : A ⥤ B) [PreservesFiniteColimits F] :
    PreservesFiniteColimits (termwise F) where
  preservesFiniteColimits L := preservesColimitsOfShape_of_evaluation _ L (fun n ↦
    inferInstanceAs (PreservesColimitsOfShape L ((evaluation ℕᵒᵖ A).obj n ⋙ F)))

/-- Constant towers commute with actual termwise pullback.
Source: Stacks 06YY (blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
def constantSquare (F : A ⥤ B) :
    Functor.const ℕᵒᵖ ⋙ termwise F ≅ F ⋙ Functor.const ℕᵒᵖ :=
  NatIso.ofComponents (fun M ↦ Functor.constComp ℕᵒᵖ M F)

variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{t} (ℕᵒᵖ ⥤ A)]

/-- The universal derived reduction and its augmentation. The counit is part of the
left-derived universal property, and is required to compute every good representative.
Source: Stacks 06YY and 06XN (blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
structure Model (Q : ℕᵒᵖ ⥤ A) (e : (Functor.const ℕᵒᵖ).obj (𝟙_ A) ⟶ Q)
    (good : CochainComplex A ℤ → Prop) where
  B : DerivedCategory A ⥤ DerivedCategory (ℕᵒᵖ ⥤ A)
  counit : DerivedCategory.Q ⋙ B ⟶
    (reduction Q).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  universal : B.IsLeftDerivedFunctor counit (HomologicalComplex.quasiIso A (.up ℤ))
  computes : ∀ P, good P → IsIso (counit.app P)
  i : (Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory ⟶ B
  augmentation_eq : ∀ P, good P →
    i.app (DerivedCategory.Q.obj P) ≫ counit.app P =
      (Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (augmentation Q e) (.up ℤ)).app P)

variable [MonoidalCategory B]

/-- The pulled-back coefficient unit, using the normalized pullback unit isomorphism.
Source: Stacks 03EL (blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
def pulledUnit (F : A ⥤ B) (j : F.obj (𝟙_ A) ≅ 𝟙_ B)
    (Q : ℕᵒᵖ ⥤ A) (e : (Functor.const ℕᵒᵖ).obj (𝟙_ A) ⟶ Q) :
    (Functor.const ℕᵒᵖ).obj (𝟙_ B) ⟶ Q ⋙ F :=
  (Functor.const ℕᵒᵖ).map j.inv ≫ (Functor.constComp ℕᵒᵖ (𝟙_ A) F).inv ≫
    Functor.whiskerRight e F

/-- The ordinary comparison as one isomorphism of strict towers, natural in the input.
Source: Stacks 03EL (blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
def ordinaryComparison (F : A ⥤ B)
    (mu : ∀ M N, F.obj (M ⊗ N) ≅ F.obj M ⊗ F.obj N)
    (hmu : ∀ {M M' N N'} (f : M ⟶ M') (g : N ⟶ N'),
      F.map (f ⊗ₘ g) ≫ (mu M' N').hom =
        (mu M N).hom ≫ (F.map f ⊗ₘ F.map g)) (Q : ℕᵒᵖ ⥤ A) :
    reduction Q ⋙ termwise F ≅ F ⋙ reduction (Q ⋙ F) :=
  NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun n ↦ mu M (Q.obj n))
    (fun {m n} g ↦ by
      change F.map (𝟙 M ⊗ₘ Q.map g) ≫ (mu M (Q.obj n)).hom =
        (mu M (Q.obj m)).hom ≫ (𝟙 (F.obj M) ⊗ₘ F.map (Q.map g))
      simpa only [F.map_id] using hmu (𝟙 M) (Q.map g)))
    (fun {M N} f ↦ by
      ext n
      change F.map (f ▷ Q.obj n) ≫ (mu N (Q.obj n)).hom =
        (mu M (Q.obj n)).hom ≫ (F.map f ▷ F.obj (Q.obj n))
      simpa only [F.map_id, tensorHom_id] using hmu f (𝟙 (Q.obj n)))

variable [HasDerivedCategory.{w'} B] [HasDerivedCategory.{t'} (ℕᵒᵖ ⥤ B)]

/-- The canonical localization of the constant-tower square.
Source: Stacks 06YY (blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
def constantDerivedSquare (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory ⋙ (termwise F).mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ (Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory :=
  letI : PreservesFiniteLimits (Functor.const ℕᵒᵖ ⋙ termwise F) :=
    comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits (Functor.const ℕᵒᵖ ⋙ termwise F) :=
    comp_preservesFiniteColimits _ _
  letI : PreservesFiniteLimits (F ⋙ Functor.const ℕᵒᵖ) :=
    comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits (F ⋙ Functor.const ℕᵒᵖ) :=
    comp_preservesFiniteColimits _ _
  (Functor.mapDerivedCategoryCompIso (Functor.const ℕᵒᵖ) (termwise F)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (constantSquare F) ≪≫
      Functor.mapDerivedCategoryCompIso F (Functor.const ℕᵒᵖ)

variable [MonoidalPreadditive B]

/-- Normalization by the universal reduction counits on every good representative.
The equation is the conjugation formula, with both exact-localization factors explicit.
Source: Stacks 06YY and 07A4
(blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
def IsNormalized (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (Q : ℕᵒᵖ ⥤ A) (e : (Functor.const ℕᵒᵖ).obj (𝟙_ A) ⟶ Q)
    (j : F.obj (𝟙_ A) ≅ 𝟙_ B)
    (goodA : CochainComplex A ℤ → Prop) (goodB : CochainComplex B ℤ → Prop)
    (MY : Model Q e goodA) (MX : Model (Q ⋙ F) (pulledUnit F j Q e) goodB)
    (mu : ∀ M N, F.obj (M ⊗ N) ≅ F.obj M ⊗ F.obj N)
    (hmu : ∀ {M M' N N'} (f : M ⟶ M') (g : N ⟶ N'),
      F.map (f ⊗ₘ g) ≫ (mu M' N').hom =
        (mu M N).hom ≫ (F.map f ⊗ₘ F.map g))
    (tau : MY.B ⋙ (termwise F).mapDerivedCategory ≅ F.mapDerivedCategory ⋙ MX.B) : Prop :=
  ∀ P, goodA P →
    (termwise F).mapDerivedCategory.map (MY.counit.app P) ≫
        (termwise F).mapDerivedCategoryFactors.hom.app
          (((reduction Q).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (ordinaryComparison F mu hmu Q) (.up ℤ)).hom.app P) =
      tau.hom.app (DerivedCategory.Q.obj P) ≫
        MX.B.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        MX.counit.app ((F.mapHomologicalComplex (.up ℤ)).obj P)

/-- Evaluation of the universal reduction counit, with its exact localization factor.
Source: Stacks 06YY, levelwise computation
(blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
def evaluationCounit (Q : ℕᵒᵖ ⥤ A)
    (e : (Functor.const ℕᵒᵖ).obj (𝟙_ A) ⟶ Q)
    (good : CochainComplex A ℤ → Prop) (M : Model Q e good) (n : ℕ) :
    DerivedCategory.Q ⋙ M.B ⋙ ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory ⟶
      (reduction Q).mapHomologicalComplex (.up ℤ) ⋙
        ((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight M.counit ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory ≫
    Functor.whiskerLeft ((reduction Q).mapHomologicalComplex (.up ℤ))
      ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.hom

end CategoryTheory.StrictReduction

namespace CategoryTheory.StrictReduction

open CochainPullback

universe uC vC uD vD r dR dS dTY dTX

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{r} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {R : Sheaf J CommRingCat.{r}} {S : Sheaf K CommRingCat.{r}}

/-- Exactly the flat-term K-flat representatives in the statement.
Source: Stacks 06YS (blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
def flatRepresentatives (R : Sheaf J CommRingCat.{r}) (P : Complex R) : Prop :=
  P.IsKFlatIndependentCoefficients ∧ ∀ n : ℤ, SheafOfModules.IsFlatOnSite (P.X n)

variable [HasDerivedCategory.{dR} (Modules R)]
  [HasDerivedCategory.{dS} (Modules S)]
  [HasDerivedCategory.{dTY} (ℕᵒᵖ ⥤ Modules R)]
  [HasDerivedCategory.{dTX} (ℕᵒᵖ ⥤ Modules S)]

/-- The universal strict-tower reduction with its coefficient-unit augmentation.
Source: Stacks 06YY (blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
abbrev RingedModel (Q : ℕᵒᵖ ⥤ Modules R)
    (e : (Functor.const ℕᵒᵖ).obj (𝟙_ (Modules R)) ⟶ Q) :=
  Model Q e (flatRepresentatives R)

/-- Generator normalization of the inverse ordinary comparison. These are exactly the
scalar-extension-adjunction generators: the mate sends Fx tensor Fq to F(x tensor q).
The insertion maps k.q are fixed by k.q_one, not arbitrary maps of sheaves.
Source: Stacks 03CZ and 03EL
(blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
def IsInversePureNormalized (f : RingedPullback R S) (k : Comparison f)
    (M N : Modules R) (a : f.L.obj M ⊗ f.L.obj N ⟶ f.L.obj (M ⊗ N)) : Prop :=
  ∀ (Z : Sheaf J (Type r))
    (x : Z ⟶ (underlying R).obj M) (y : Z ⟶ (underlying R).obj N)
    (z : Z ⟶ (underlying R).obj (M ⊗ N)),
    (∀ (U : Cᵒᵖ) (t : Z.obj.obj U), z.hom.app U t =
      (SheafOfModules.tensorObjIsoSheafification M N).inv.val.app U
        (((PresheafOfModules.sheafificationAdjunction (𝟙
          ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj)).unit.app
            (M.val ⊗ N.val)).app U
              (x.hom.app U t ⊗ₜ[R.obj.obj U] y.hom.app U t))) →
    ∀ (V : Dᵒᵖ) (t : (f.uInv.obj Z).obj.obj V),
      a.val.app V
        ((SheafOfModules.tensorObjIsoSheafification (f.L.obj M) (f.L.obj N)).inv.val.app V
          (((PresheafOfModules.sheafificationAdjunction (𝟙
            ((sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj S).obj)).unit.app
              ((f.L.obj M).val ⊗ (f.L.obj N).val)).app V
                ((f.uInv.map x ≫ f.I.moduleUnderlying.inv.app M ≫ k.q M).hom.app V t
                  ⊗ₜ[S.obj.obj V]
                  (f.uInv.map y ≫ f.I.moduleUnderlying.inv.app N ≫ k.q N).hom.app V t))) =
        (f.uInv.map z ≫ f.I.moduleUnderlying.inv.app (M ⊗ N) ≫ k.q (M ⊗ N)).hom.app V t

/-- Pullback of a strict tower of commutative algebras commutes uniquely with derived
reduction, normalized by the universal counits. The index n encodes the paper's n+1.
Source: Stacks 06YS, 06YY, 07A4 and 03EL
(blueprint: lem-weil-pbc-reduction-pullback-derived-tower).

Proof:
1. Kernels and cokernels of strict towers are levelwise (02MZ); hence so are cohomology
and quasi-isomorphisms. Constant towers and termwise exact pullback descend through
quasi-isomorphisms by exact-functor-derived-factorization.
2. Resolve by flat-term K-flat complexes (06YS). Change-of-rings-kflat-quasi-iso at every
coefficient algebra, followed by exact scalar restriction, shows reduction inverts
quasi-isomorphisms between these representatives. No coefficient algebra is assumed flat.
3. Left-derived-from-kflat-class gives the universal counit, invertible on these
representatives. Its inverse conjugates the localized coefficient-unit insertion to i.
4. Diagram-site-realization identifies the tensor of towers levelwise. Pure tensor
sections and canonical-ringed-tensor-comparison determine its transition squares. Thus
the diagonal of a flat-term K-flat representative is again flat-term K-flat, and this
model also computes tensor with the algebra tower on the diagram site.
5. The ordinary comparison is the canonical mu from 03EL: it carries the inverse image
of x tensor q to Fx tensor Fq, in every degree and at every tower level.
6. Under the extension/restriction adjunction, the scalar-extension mate sends
Fx tensor Fq to F(x tensor 1)Fq = F(x tensor q). Thus it is inverse to mu, and mu
preserves insertion of 1. The unit is the uniquely normalized moduleUnit.
7. Naturality of mu in coefficients gives every strict transition square; naturality
in the first variable gives differentials, cochain maps and homotopies.
8. Ringed-pullback-preserves-kflat preserves the resolving class. Compose the ordinary
comparison with both universal counits and the exact localization factors. The
site-derived-tensor-descent localization and localization-universal-property extend
this equation uniquely to a natural isomorphism and its inverse on all derived objects.
9. Unitality of the transitions makes the augmentation a strict cochain map. The unit
calculation in step 6 and cancellation of the counits prove the augmentation equation
on representatives; localization faithfulness proves it on all objects.
10. Exact evaluation sends the universal tower counit and ordinary comparison to the
single-level reduction counit and ordinary mu. The same resolving criterion makes each
evaluated counit universal; the evaluated representative equation therefore identifies
the evaluations with the representative-normalized derived tensor/pullback comparisons.
The proof uses no perfection, completeness, boundedness or adic hypothesis. -/
theorem reductionPullbackDerivedTower
    (f : RingedPullback R S) [IsIso f.coefficient]
    [PreservesFiniteLimits f.L] [PreservesFiniteColimits f.L]
    (k : Comparison f) (Q : CommMon (ℕᵒᵖ ⥤ Modules R)) :
    (∀ (M : Modules R) (n : ℕ),
      IsInversePureNormalized f k M (Q.X.obj (op n)) (k.mu M (Q.X.obj (op n))).inv) ∧
    Nonempty (RingedModel Q.X (MonObj.one (X := Q.X))) ∧
    Nonempty (RingedModel (Q.X ⋙ f.L)
      (pulledUnit f.L (moduleUnit f k) Q.X (MonObj.one (X := Q.X)))) ∧
    ∀ (MY : RingedModel Q.X (MonObj.one (X := Q.X)))
      (MX : RingedModel (Q.X ⋙ f.L)
        (pulledUnit f.L (moduleUnit f k) Q.X (MonObj.one (X := Q.X)))),
      ∃ tau : MY.B ⋙ (termwise f.L).mapDerivedCategory ≅ f.L.mapDerivedCategory ⋙ MX.B,
        IsNormalized f.L Q.X (MonObj.one (X := Q.X)) (moduleUnit f k)
          (flatRepresentatives R) (flatRepresentatives S) MY MX k.mu k.naturality tau ∧
        (∀ tau' : MY.B ⋙ (termwise f.L).mapDerivedCategory ≅ f.L.mapDerivedCategory ⋙ MX.B,
          IsNormalized f.L Q.X (MonObj.one (X := Q.X)) (moduleUnit f k)
            (flatRepresentatives R) (flatRepresentatives S) MY MX k.mu k.naturality tau' →
          tau' = tau) ∧
        (∀ L : DerivedCategory (Modules R),
          (termwise f.L).mapDerivedCategory.map (MY.i.app L) ≫ tau.hom.app L =
            (constantDerivedSquare f.L).hom.app L ≫ MX.i.app (f.L.mapDerivedCategory.obj L)) ∧
        (∀ n : ℕ,
          (MY.B ⋙ ((evaluation ℕᵒᵖ (Modules R)).obj (op n)).mapDerivedCategory).IsLeftDerivedFunctor
            (evaluationCounit Q.X (MonObj.one (X := Q.X))
              (flatRepresentatives R) MY n)
                (HomologicalComplex.quasiIso (Modules R) (.up ℤ))) ∧
        (∀ n : ℕ,
          (MX.B ⋙ ((evaluation ℕᵒᵖ (Modules S)).obj (op n)).mapDerivedCategory).IsLeftDerivedFunctor
            (evaluationCounit (Q.X ⋙ f.L)
              (pulledUnit f.L (moduleUnit f k) Q.X (MonObj.one (X := Q.X)))
              (flatRepresentatives S) MX n)
                (HomologicalComplex.quasiIso (Modules S) (.up ℤ))) := by
  sorry

end CategoryTheory.StrictReduction
