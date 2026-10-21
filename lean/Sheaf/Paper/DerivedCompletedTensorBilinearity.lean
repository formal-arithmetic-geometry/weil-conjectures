/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.CategoryTheory.RingedKoszulSmallModelCompletedTensor
public import Sheaf.CategoryTheory.ScalarLocalization
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Linear.LinearFunctor
import Sheaf.Paper.WeilCompletedTensorReflector
import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.CategoryTheory.LinearScalarLocalization
import Mathlib.CategoryTheory.Localization.Linear
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-! # Bilinearity of derived completed tensor and its raw rational Hom action

Source: blueprint, sec-six-functors/sk-rem-sf-pf-done/def-wf-tensor-product.md,
coefficient tensor model; Stacks Tags 06YS, 06YU, 099B, 0A0E, 00CX and 05G4
(blueprint: lem-sf-derived-completed-tensor-bilinearity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v r w w₀ a
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
namespace CategoryTheory
namespace DerivedCompletedTensor

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

/-- The induced A-action is the existing global-section action restricted along s.
At U it sends f(x) to s(a)|U f(x), with the existing additive Hom groups.
Source: Stacks 03EK (blueprint: lem-sf-derived-completed-tensor-bilinearity). -/
@[instance_reducible]
def coefficientLinear (A : Type a) [CommRing A]
    (s : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat.{r} RingCat.{r})) :
    Linear A (KoszulSmallModel.Modules R) :=
  letI : Linear (RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat.{r} RingCat.{r}))
      (KoszulSmallModel.Modules R) :=
    SheafOfModules.homLinear R.obj
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).property
  { homModule := fun M N ↦ Module.compHom (M ⟶ N) s
    smul_comp := fun M N P z f g ↦ Linear.smul_comp M N P (s z) f g
    comp_smul := fun M N P f z g ↦ Linear.comp_smul M N P f (s z) g }

variable [HasDerivedCategory.{w} (KoszulSmallModel.Modules R)]
  [HasDerivedCategory.{w₀} (ringedSiteModules.{r}
    ((sheafCompose _ (forget₂ CommRingCat.{r} RingCat.{r})).obj (KoszulSmallModel.ring R)))]
  [∀ U : SmallModel.{r} C, HasDerivedCategory.{w₀} (SheafOfModules.{r}
    ((sheafCompose (((equivSmallModel.{r} C).inverse.inducedTopology J).over U)
      (forget₂ CommRingCat.{r} RingCat.{r})).obj ((KoszulSmallModel.ring R).over U)))]

variable (I : ringedSiteModules.{r}
  ((sheafCompose _ (forget₂ CommRingCat.{r} RingCat.{r})).obj (KoszulSmallModel.ring R)))
  (ι : I ⟶ SheafOfModules.unit.{r}
    ((sheafCompose _ (forget₂ CommRingCat.{r} RingCat.{r})).obj (KoszulSmallModel.ring R)))

/-- Bilinear maps on the two raw localized Hom modules. This is only an abbreviation
for ordinary curried linear maps, using the dependency's scalar-first tensor convention.
Source: blueprint def-wf-tensor-product
(blueprint: lem-sf-derived-completed-tensor-bilinearity). -/
abbrev HomAction (A : Type a) [CommRing A]
    [Linear A (KoszulSmallModel.Modules R)]
    (L : DerivedCategory (KoszulSmallModel.Modules R) ⥤
      (KoszulSmallModel.complete R I ι).FullSubcategory) (p : A)
    (M M' N N' : (KoszulSmallModel.complete R I ι).FullSubcategory) :=
  (Localization.Away p ⊗[A] (M ⟶ M')) →ₗ[Localization.Away p]
    (Localization.Away p ⊗[A] (N ⟶ N')) →ₗ[Localization.Away p]
      (Localization.Away p ⊗[A] ((tensor R I ι L).obj (M, N) ⟶
        (tensor R I ι L).obj (M', N')))

/-- All seven clauses of the node, with the specified tensor and a natural universal
Koszul unit. The ideal mono and hgen specify exactly the finite generated ideal;
L, eta and hL say that L is its reflector, as stipulated in the node.

Source: blueprint def-wf-tensor-product, coefficient tensor model;
Stacks 03EK, 05RU, 06YS, 06YU, 099B, 0A0E, 00CX and 05G4
(blueprint: lem-sf-derived-completed-tensor-bilinearity).

Proof plan:
1. On module Hom groups use (a f)_U(x)=s(a)|U f_U(x). Composition is bilinear.
Sheaf tensor is separately linear by tensor balancing before sheafification; equality
passes to sheafification. On each signed total summand the map is f^i tensor g^j,
so sums and scalars commute with totalization.
2. The localization Q is additive (lem-sfb-derived-localization-additive).
lem-sfb-additive-localization-linear gives the induced A-action and linearity of Q.
3. For fixed flat-term K-flat P, lem-weil-pbc-kflat-fixed-tensor-triangulated gives
additive descended tensor functors. Their comparisons identify their composites with Q
with the linear total tensors of steps 1-2. Apply lem-sfb-linear-localization-descent.
The equivalence of lem-weil-pbc-site-derived-tensor-descent represents every derived
object by such P. Conjugation by its representative isomorphism preserves linearity.
4. Naturality of eta identifies eta_X followed by L(af+bg) with both eta_X followed
by a L(f)+b L(g). Injectivity of hL, with complete target LY, proves the equality.
This proves additivity and linearity of the specified reflector without linear choices.
5. Restrict tensor to the complete full subcategory and compose with L. Fixed-variable
functors are additive and linear, and simultaneous action is bilinear by composition.
6. Apply def-weil-module-base-change to the integral bilinear Hom map and A -> A[1/p].
The unique bilinear extension sends (x tensor f,y tensor g) to xy tensor B(f,g),
with the dependency's scalar-first convention. No flatness or torsion assumption enters.
7. The composition formula of lem-weil-linear-scalar-localization-category and
functoriality of B prove identity and composition on pure tensors. Each tensor is a
finite sum of pure tensors; multilinearity proves the laws on all arrows. These laws
give the bifunctor F with the prescribed object map and Hom action. Substitute inverse
powers of p in step 6 to obtain the denominator formula, including A[1/p]=0. -/
theorem bilinearity (A : Type a) [CommRing A]
    (s : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat.{r} RingCat.{r}))
    (n : ℕ) (b : Fin n → (R.obj ⋙ forget CommRingCat.{r}).sections) [Mono ι]
    (_hgen : ∀ U : SmallModel.{r} C,
      IsRingedIdealGeneratingList (KoszulSmallModel.ring R) I ι U n
        (fun i ↦ (KoszulSmallModel.globalSection R (b i)).val (op U)))
    (L : DerivedCategory (KoszulSmallModel.Modules R) ⥤
      (KoszulSmallModel.complete R I ι).FullSubcategory)
    (η : 𝟭 (DerivedCategory (KoszulSmallModel.Modules R)) ⟶
      L ⋙ (KoszulSmallModel.complete R I ι).ι)
    (_hL : ∀ (M : DerivedCategory (KoszulSmallModel.Modules R))
      (N : (KoszulSmallModel.complete R I ι).FullSubcategory),
      Function.Bijective (fun f : L.obj M ⟶ N ↦ η.app M ≫ f.hom)) :
    (fun [_scalar : Linear A (KoszulSmallModel.Modules R)] ↦
      L.Additive ∧ L.Linear A ∧
      (∀ M : DerivedCategory (KoszulSmallModel.Modules R),
        ((Functor.curry.obj (SheafOfModules.siteDerivedTensorIndependentCoefficients J R)).obj
          M).Additive ∧
        ((Functor.curry.obj (SheafOfModules.siteDerivedTensorIndependentCoefficients J R)).obj
          M).Linear A ∧
        ((Functor.curry.obj (SheafOfModules.siteDerivedTensorIndependentCoefficients J R)).flip.obj
          M).Additive ∧
        ((Functor.curry.obj (SheafOfModules.siteDerivedTensorIndependentCoefficients J R)).flip.obj
          M).Linear A) ∧
      (∀ M : (KoszulSmallModel.complete R I ι).FullSubcategory,
        ((Functor.curry.obj (tensor R I ι L)).obj M).Additive ∧
        ((Functor.curry.obj (tensor R I ι L)).obj M).Linear A ∧
        ((Functor.curry.obj (tensor R I ι L)).flip.obj M).Additive ∧
        ((Functor.curry.obj (tensor R I ι L)).flip.obj M).Linear A) ∧
      ∀ p : A, ∃ β : ∀ M M' N N' : (KoszulSmallModel.complete R I ι).FullSubcategory,
          HomAction R I ι A L p M M' N N',
        (∀ (M M' N N' : (KoszulSmallModel.complete R I ι).FullSubcategory)
          (f : M ⟶ M') (g : N ⟶ N') (x y : Localization.Away p),
          β M M' N N' (x ⊗ₜ[A] f) (y ⊗ₜ[A] g) =
            (x * y) ⊗ₜ[A] (tensor R I ι L).map (f, g)) ∧
        (∀ (M M' N N' : (KoszulSmallModel.complete R I ι).FullSubcategory)
          (β' : HomAction R I ι A L p M M' N N'),
          (∀ (f : M ⟶ M') (g : N ⟶ N') (x y : Localization.Away p),
            β' (x ⊗ₜ[A] f) (y ⊗ₜ[A] g) =
              (x * y) ⊗ₜ[A] (tensor R I ι L).map (f, g)) → β' = β M M' N N') ∧
        (∀ M N : (KoszulSmallModel.complete R I ι).FullSubcategory,
          β M M N N (1 ⊗ₜ[A] 𝟙 M) (1 ⊗ₜ[A] 𝟙 N) =
            (1 : Localization.Away p) ⊗ₜ[A] 𝟙 ((tensor R I ι L).obj (M, N))) ∧
        (∀ (M M' M'' N N' N'' : (KoszulSmallModel.complete R I ι).FullSubcategory)
          (f : Localization.Away p ⊗[A] (M ⟶ M'))
          (f' : Localization.Away p ⊗[A] (M' ⟶ M''))
          (g : Localization.Away p ⊗[A] (N ⟶ N'))
          (g' : Localization.Away p ⊗[A] (N' ⟶ N'')),
          β M M'' N N''
              (ScalarLocalization.composition A _ p M M' M'' f' f)
              (ScalarLocalization.composition A _ p N N' N'' g' g) =
            ScalarLocalization.composition A _ p
              ((tensor R I ι L).obj (M, N)) ((tensor R I ι L).obj (M', N'))
              ((tensor R I ι L).obj (M'', N''))
              (β M' M'' N' N'' f' g') (β M M' N N' f g)) ∧
        (∀ (M M' N N' : (KoszulSmallModel.complete R I ι).FullSubcategory)
          (f : M ⟶ M') (g : N ⟶ N') (k t : ℕ),
          β M M' N N'
              (((IsLocalization.Away.invSelf p : Localization.Away p) ^ k) ⊗ₜ[A] f)
              (((IsLocalization.Away.invSelf p : Localization.Away p) ^ t) ⊗ₜ[A] g) =
            ((IsLocalization.Away.invSelf p : Localization.Away p) ^ (k + t)) ⊗ₜ[A]
              (tensor R I ι L).map (f, g)) ∧
        ∃ F : ScalarLocalization A (KoszulSmallModel.complete R I ι).FullSubcategory p ×
              ScalarLocalization A (KoszulSmallModel.complete R I ι).FullSubcategory p ⥤
              ScalarLocalization A (KoszulSmallModel.complete R I ι).FullSubcategory p,
          (∀ M N : (KoszulSmallModel.complete R I ι).FullSubcategory,
            F.obj (⟨M⟩, ⟨N⟩) = ⟨(tensor R I ι L).obj (M, N)⟩) ∧
          (∀ (M M' N N' : (KoszulSmallModel.complete R I ι).FullSubcategory)
            (f : Localization.Away p ⊗[A] (M ⟶ M'))
            (g : Localization.Away p ⊗[A] (N ⟶ N')),
            HEq (F.map (X := (⟨M⟩, ⟨N⟩)) (Y := (⟨M'⟩, ⟨N'⟩)) (f, g))
              (β M M' N N' f g))) (_scalar := coefficientLinear R A s) := by
  sorry

end DerivedCompletedTensor
end CategoryTheory
