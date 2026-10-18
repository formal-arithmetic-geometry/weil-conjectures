/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.Paper.IntegralDerivedOperations
public import Sheaf.CategoryTheory.RingedSiteDualityMaps
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.Linear

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-!
# Completed integral operations on the global site and its slices

Source: Bhatt--Scholze, Definition 3.4.10 and Definition 3.5.2; Stacks Project,
Tags 06YY and 08TC (blueprint: def-pur-integral-derived-operations).

The option is only an index for the two sites in the consumer: none is the global
site; some U is its actual over-site. Coefficients and quotient projections on the
latter are sectionwise restrictions. Site object and morphism sizes stay t+1 and t.
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
namespace IntegralOnSlice

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : AlgebraicGeometry.Scheme.{t})

/-- Global or localized site objects. Source: Stacks 04D5
(blueprint: def-pur-integral-derived-operations). -/
def Site (U : Option X.ProEt) : Type (t + 1) :=
  match U with
  | none => X.ProEt
  | some V => Over V

/-- The original category structure, with Hom universe t. Source: Stacks 04D5
(blueprint: def-pur-integral-derived-operations). -/
instance siteCategory (U : Option X.ProEt) : Category.{t} (Site X U) :=
  match U with
  | none => inferInstanceAs (Category X.ProEt)
  | some V => inferInstanceAs (Category (Over V))

/-- The actual topology or its over-topology. Source: Stacks 04D5
(blueprint: def-pur-integral-derived-operations). -/
def topology (U : Option X.ProEt) : GrothendieckTopology (Site X U) :=
  match U with
  | none => AlgebraicGeometry.Scheme.ProEt.topology X
  | some V => (AlgebraicGeometry.Scheme.ProEt.topology X).over V

/-- Sectionwise coefficient restriction. Source: Stacks 04D5
(blueprint: def-pur-integral-derived-operations). -/
def restrict (U : Option X.ProEt) :
    Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{max u (t + 1)} ⥤
      Sheaf (topology X U) CommRingCat.{max u (t + 1)} :=
  match U with
  | none => 𝟭 _
  | some V => (Over.forget V).sheafPushforwardContinuous _ _ _

variable (U : Option X.ProEt)

/-- The existing completed ring on this site. Source: Bhatt--Scholze, Section 6.5
(blueprint: def-pur-integral-derived-operations). -/
def ring := (restrict.{t, u} X U).obj (completedIntegralCommRingSheafUnrestricted l E X)

/-- Finite coefficients at exponent n+1. Source: Bhatt--Scholze, Section 6.5
(blueprint: def-pur-integral-derived-operations). -/
def finite (n : ℕ) := (restrict.{t, u} X U).obj (integralCoefficientCommRingSheaf l E X n)

/-- The actual restricted quotient projection. Source: Bhatt--Scholze, Section 6.5
(blueprint: def-pur-integral-derived-operations). -/
def projection (n : ℕ) : ring l E X U ⟶ finite l E X U n :=
  (restrict.{t, u} X U).map (completedIntegralCommRingProjectionUnrestricted l E X n)

/-- Abelian sheafification in a size containing the actual site. Source: Stacks 03DA
(blueprint: def-pur-integral-derived-operations). -/
instance abSheafify : HasSheafify (topology X U) AddCommGrpCat.{max u (t + 1)} :=
  letI : EssentiallySmall.{max u (t + 1)} (Site X U) := essentiallySmallSelf _
  hasSheafifyEssentiallySmallSite _ _

/-- The locally bijective sheafification criterion. Source: Stacks 03DA
(blueprint: def-pur-integral-derived-operations). -/
instance abLocallyBijective :
    (topology X U).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
  letI : EssentiallySmall.{max u (t + 1)} (Site X U) := essentiallySmallSelf _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall (topology X U)

/-- Forget only commutativity, retaining the exact completed ring data. Source: Stacks 06YY
(blueprint: def-pur-integral-derived-operations). -/
abbrev rings := SheafOfModules.derivedChangeRingIndependentCoefficients (topology X U)
  (ring l E X U)

/-- The existing module category. Source: Stacks 06YY
(blueprint: def-pur-integral-derived-operations). -/
abbrev Mod := ringedSiteModules.{max u (t + 1)} (rings l E X U)

/-- Standard derived localization for these modules. Source: Stacks 05RU
(blueprint: def-pur-integral-derived-operations). -/
instance hasDerived : HasDerivedCategory (Mod l E X U) := HasDerivedCategory.standard _

/-- The derived category of all completed-coefficient modules on this site. Source: Stacks 05RU
(blueprint: def-pur-integral-derived-operations). -/
abbrev D := DerivedCategory (Mod l E X U)

/-- The precise cochain representatives. Source: Stacks 05RU
(blueprint: def-pur-integral-derived-operations). -/
abbrev Cx := CochainComplex (Mod l E X U) ℤ

set_option linter.defProp false in
/-- The universal scalar-extension witness along the specified projection. Source: Stacks 06YY
(blueprint: def-pur-integral-derived-operations). -/
def reductionWitness (n : ℕ) :=
  letI := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)}
    (SheafOfModules.derivedChangeRingIndependentCoefficients (topology X U) (finite l E X U n)))
  SheafOfModules.derivedChangeOfRingsIndependentCoefficients (projection l E X U n)

/-- Ordinary change of rings with the witness's fixed objects and maps. Source: Stacks 06YY
(blueprint: def-pur-integral-derived-operations). -/
def reduction (n : ℕ) := (reductionWitness l E X U n).choose

/-- Additivity supplied by the normalized scalar-extension construction. Source: Stacks 06YY
(blueprint: def-pur-integral-derived-operations). -/
instance reductionAdditive (n : ℕ) : (reduction l E X U n).Additive :=
  (reductionWitness l E X U n).choose_spec.choose_spec.choose_spec.choose

/-- Termwise reduction with the completed action restored by the actual projection.
Source: Stacks 06YY (blueprint: def-pur-integral-derived-operations). -/
def level (n : ℕ) : Cx l E X U ⥤ Cx l E X U :=
  (reduction l E X U n).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    (SheafOfModules.restrictScalars
      ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (projection l E X U n))).mapHomologicalComplex
      (ComplexShape.up ℤ)

/-- The sheafified generator s tensor x of finite reduction. Source: Stacks 03EK
(blueprint: def-pur-integral-derived-operations). -/
def generator (n : ℕ) (M : Mod l E X U) (V : (Site X U)ᵒᵖ)
    (s : (finite l E X U n).obj.obj V) (x : M.val.obj V) :
    ((reduction l E X U n).obj M).val.obj V :=
  (eqToHom ((reductionWitness l E X U n).choose_spec.choose M).symm).val.app V
    ((toSheafify (topology X U)
      (SheafOfModules.changeOfRingsPresheaf (projection l E X U n) M).presheaf).app V
        (s ⊗ₜ[(ring l E X U).obj.obj V, ((projection l E X U n).hom.app V).hom] x))

/-- The coefficient reduction, forgetting commutativity only. Source: Stacks 03EK
(blueprint: def-pur-integral-derived-operations). -/
def rho (n : ℕ) :
    (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      (finite l E X U (n + 1)) ⟶
      (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        (finite l E X U n) :=
  match U with
  | none => integralCoefficientSheafTransition l E X n
  | some V => ((Over.forget V).sheafPushforwardContinuous _ _ _).map
      (integralCoefficientSheafTransition l E X n)

/-- Consecutive reduction maps are uniquely specified on generators. Source: Stacks 03EK
(blueprint: def-pur-integral-derived-operations).
Proof: send s tensor x to rho(s) tensor x. The projection compatibility makes this
balanced and completed-linear. Restrictions and differentials commute with this
formula. Sheafification and tensor generation give existence and uniqueness. -/
theorem transition_existsUnique (n : ℕ) :
    ∃! τ : level l E X U (n + 1) ⟶ level l E X U n,
      ∀ (P : Cx l E X U) (i : ℤ) (V : (Site X U)ᵒᵖ)
        (s : (finite l E X U (n + 1)).obj.obj V) (x : (P.X i).val.obj V),
        ((τ.app P).f i).val.app V (generator l E X U (n + 1) (P.X i) V s x) =
          generator l E X U n (P.X i) V ((rho l E X U n).hom.app V s) x := by
  sorry

/-- The actual transition fixed by the preceding tensor formula. Source: Stacks 03EK
(blueprint: def-pur-integral-derived-operations). -/
def transition (n : ℕ) := (transition_existsUnique l E X U n).exists.choose

/-- The actual strict reduction tower. Source: Bhatt--Scholze, Definition 3.5.2
(blueprint: def-pur-integral-derived-operations). -/
def tower : Cx l E X U ⥤ (ℕᵒᵖ ⥤ Cx l E X U) :=
  (Functor.ofOpSequence (X := fun n ↦ level l E X U n) (transition l E X U)).flip

/-- The unique augmentation has x mapped to 1 tensor x at every positive exponent.
Source: Bhatt--Scholze, Definition 3.5.2 (blueprint: def-pur-integral-derived-operations).
Proof: the scalar-extension adjunction unit is completed-linear and natural. Apply
it degreewise; its compatibility with rho follows because rho preserves one. Pure
tensor generation and sheafification determine the maps uniquely. -/
theorem augmentation_existsUnique :
    ∃! γ : (Functor.const ℕᵒᵖ : Cx l E X U ⥤ (ℕᵒᵖ ⥤ Cx l E X U)) ⟶ tower l E X U,
      ∀ (P : Cx l E X U) (n : ℕ) (i : ℤ) (V : (Site X U)ᵒᵖ) (x : (P.X i).val.obj V),
        (((γ.app P).app (op n)).f i).val.app V x =
          generator l E X U n (P.X i) V 1 x := by
  sorry

/-- The canonical reduction augmentation. Source: Bhatt--Scholze, Definition 3.5.2
(blueprint: def-pur-integral-derived-operations). -/
def augmentation := (augmentation_existsUnique l E X U).exists.choose

/-- K-flat representatives with flat terms. Source: Stacks 06YN
(blueprint: def-pur-integral-derived-operations). -/
def Good : ObjectProperty (Cx l E X U) := fun P ↦
  CochainComplex.IsKFlatIndependentCoefficients (J := topology X U) (R := ring l E X U) P ∧
    ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
      (R := ring l E X U) (P.X i)

/-- Localization of the resolving class into the existing derived category. Source: Stacks 06YN
(blueprint: def-pur-integral-derived-operations). -/
def qGood := (Good l E X U).ι ⋙ DerivedCategory.Q

/-- The actual Roos complex of the strict quotient tower. Source: Stacks 08TC
(blueprint: def-pur-integral-derived-operations). -/
def roos := tower l E X U ⋙ integralOperationsRoosFunctor

/-- Quotient completion on all good representatives. Source: Stacks 08TC
(blueprint: def-pur-integral-derived-operations). -/
def roosGood := (Good l E X U).ι ⋙ roos l E X U ⋙ DerivedCategory.Q

/-- Completion is the unique descent equipped with its representative comparison.
Source: Stacks 06YN, 08TC (blueprint: def-pur-integral-derived-operations).
Proof: restriction has exact underlying sheaves, also on a slice; the pro-etale
countable-product theorem restricts to its over-site. Reduction carries K-flat
quasi-isomorphisms to quasi-isomorphisms. Roos preserves these by exact products.
Every derived object has a good representative. The resolving-class localization
therefore descends roosGood, and is fully faithful on natural transformations,
which determines this functor together with its comparison uniquely. -/
theorem completion_exists :
    ∃ F : D l E X U ⥤ D l E X U,
      Nonempty (qGood l E X U ⋙ F ≅ roosGood l E X U) ∧
      ∀ (F' : D l E X U ⥤ D l E X U) (e : qGood l E X U ⋙ F ≅ roosGood l E X U)
        (e' : qGood l E X U ⋙ F' ≅ roosGood l E X U),
        ∃! a : F ≅ F', Functor.whiskerLeft (qGood l E X U) a.hom ≫ e'.hom = e.hom := by
  sorry

/-- Completion chosen with its determining representative normalization. Source: Stacks 08TC
(blueprint: def-pur-integral-derived-operations). -/
def completion := (completion_exists l E X U).choose

/-- The normalized comparison on every good representative. Source: Stacks 08TC
(blueprint: def-pur-integral-derived-operations). -/
def completionComparison : qGood l E X U ⋙ completion l E X U ≅ roosGood l E X U :=
  (completion_exists l E X U).choose_spec.1.some

/-- The augmentation into the termwise product. Source: Bhatt--Scholze, Definition 3.5.2
(blueprint: def-pur-integral-derived-operations). -/
def productAugmentation (P : Cx l E X U) :
    P ⟶ ∏ᶜ (fun n : ℕ ↦ ((tower l E X U).obj P).obj (op n)) :=
  Pi.lift (fun n ↦ ((augmentation l E X U).app P).app (op n))

/-- The zero homotopy witnesses the strict augmentation's composite with 1-s.
Source: Stacks 08TC (blueprint: def-pur-integral-derived-operations).
Proof: postcompose with every product projection. Consecutive quotient augmentations
agree after transition by naturality of augmentation. Hence c(1-s)=0. The differential
of the zero cochain and the cochain of the zero chain map are both zero. -/
theorem roosUnit_condition (P : Cx l E X U) :
    CochainComplex.HomComplex.δ (-1) 0
      (0 : CochainComplex.HomComplex.Cochain P
        (∏ᶜ fun n : ℕ ↦ ((tower l E X U).obj P).obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (productAugmentation l E X U P ≫
          towerTransitionEndomorphism
            (K := fun n : ℕ ↦ ((tower l E X U).obj P).obj (op n))
            (integralOperationsTowerStep ((tower l E X U).obj P))) = 0 := by
  sorry

/-- The prescribed quotient unit is the explicit chain map (c,0) into Cone(1-s)[-1].
Source: Stacks 08TC (blueprint: def-pur-integral-derived-operations). -/
def roosUnit (P : Cx l E X U) :
    P ⟶ integralOperationsRoos ((tower l E X U).obj P) :=
  CochainComplex.mappingCocone.lift
    (towerTransitionEndomorphism
      (K := fun n : ℕ ↦ ((tower l E X U).obj P).obj (op n))
      (integralOperationsTowerStep ((tower l E X U).obj P)))
    (productAugmentation l E X U P) 0 (roosUnit_condition l E X U P)

/-- The quotient unit descends uniquely with its (c,0) normalization on good representatives.
Source: Stacks 06YN, 08TC (blueprint: def-pur-integral-derived-operations).
Proof: the chain-level unit commutes with maps, by its product components and its zero
second cochain. Its equality survives quasi-isomorphisms between good representatives.
Fully faithful restriction of transformations along the resolving-class localization
supplies exactly one natural transformation with the displayed formula. -/
theorem completionUnit_existsUnique :
    ∃! η : 𝟭 (D l E X U) ⟶ completion l E X U,
      ∀ P : (Good l E X U).FullSubcategory,
        η.app ((qGood l E X U).obj P) ≫ (completionComparison l E X U).hom.app P =
          DerivedCategory.Q.map (roosUnit l E X U P.obj) := by
  sorry

/-- The unique completion unit determined on all K-flat flat-term representatives.
Source: Stacks 08TC (blueprint: def-pur-integral-derived-operations). -/
def completionUnit : 𝟭 (D l E X U) ⟶ completion l E X U :=
  (completionUnit_existsUnique l E X U).exists.choose

/-- The ambient internal Hom, with independent site and coefficient sizes. Source: Stacks 08J7
(blueprint: def-pur-integral-derived-operations). -/
def hom := derivedInternalHomOfUniverses.{t + 1, t, u} (topology X U) (ring l E X U)

/-- The normalized ordinary derived tensor-Hom model. Source: Stacks 08JD
(blueprint: def-pur-integral-derived-operations). -/
def duality : RingedSiteDualityModel.{t + 1, t, u, (max u (t + 1)) + 1}
    (topology X U) (ring l E X U) :=
  Classical.choice (ringedSiteDualityMaps_exists (topology X U) (ring l E X U))

/-- Completed tensor as quotient completion of ordinary derived tensor. The balanced
finite-level identity identifies this with the recorded two-reduction construction.
Source: Bhatt--Scholze, Definition 3.4.10 (blueprint: def-pur-integral-derived-operations). -/
def completedTensor : (D l E X U) × (D l E X U) ⥤ D l E X U :=
  (duality l E X U).closed.tensor ⋙ completion l E X U

/-- The global specialization computes precisely the recorded finite-tensor Roos model,
so this extension does not introduce a different global tensor product.
Source: Bhatt--Scholze, Definition 3.4.10; Stacks 06YY
(blueprint: def-pur-integral-derived-operations).
Proof: for flat-term K-flat P,Q, their ordinary tensor is K-flat with flat terms.
Apply completionComparison to that tensor and the ordinary tensor comparison of
RingedSiteDualityModel.models. At each finite level reassociate balanced tensors:
(p tensor a) tensor (q tensor b) maps to (p tensor q) tensor ab, and its inverse
sends (p tensor q) tensor a to (p tensor 1) tensor (q tensor a). Both maps preserve
the total differential and every quotient transition. Their strict tower isomorphism
gives a Roos isomorphism, natural in P,Q. Compose with the representative comparisons.
The target is exactly integralOperationsTensorOnGood, not an arbitrary derived model. -/
theorem completedTensor_global_comparison :
    Nonempty (((integralOperationsGoodLocalization l E X).prod
      (integralOperationsGoodLocalization l E X)) ⋙ completedTensor l E X none ≅
        integralOperationsTensorOnGood l E X) := by
  sorry

end IntegralOnSlice
end WeilConjectures
