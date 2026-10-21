/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Paper.PurInverseImageTensorHom
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients

/-! # Coefficient-compatible K-flat tensor models under a scheme isomorphism

Source: Bhatt--Scholze, Section 6.5, Lemma 6.5.9(4), and the agent calculation
with the specified quotient towers
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model).

The index n means positive exponent n+1. Inverse image is the recorded sectionwise
model, with its action transported by the completed or finite structure map.
Scalar tensors use the existing sheafified tensor, with scalar written first.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme WeilConjectures
open scoped ChangeOfRings
namespace AlgebraicGeometry.ProEtale.IsomorphismScalarTensor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

/-- The existing ordinary extension at a finite level, supplied with its universal
counit. Its objects and maps are fixed by the sheafified balanced tensor.
Source: Stacks 03EK and 06YY
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
def finiteChangeData (W : Scheme.{t}) (n : ℕ) :=
  Classical.choice (SheafOfModules.nonempty_derivedChangeOfRingsCochainModel
    (integralScalarQuotientSheafMap l E L ι W n))

/-- Ordinary extension from E's finite coefficient ring to L's, with the same index.
Source: Stacks 03EK (blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
abbrev finiteExtension (W : Scheme.{t}) (n : ℕ) :=
  (finiteChangeData l E L ι W n).E

/-- The actual balanced pure tensor in finite extension, including the witness's
object identification. Source: Stacks 03EK
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
def finitePure (W : Scheme.{t}) (n : ℕ)
    (M : integralOperationsFiniteModules l E W n) (U : W.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l L W n).obj.obj U) (x : M.val.obj U) :
    ((finiteExtension l E L ι W n).obj M).val.obj U :=
  (eqToHom ((finiteChangeData l E L ι W n).obj_eq M).symm).val.app U
    ((toSheafify (ProEt.topology W)
      (SheafOfModules.changeOfRingsPresheaf
        (integralScalarQuotientSheafMap l E L ι W n) M).presheaf).app U
      (s ⊗ₜ[(integralCoefficientCommRingSheaf l E W n).obj.obj U,
        ((integralScalarQuotientSheafMap l E L ι W n).hom.app U).hom] x))

/-- Completed-coefficient inverse image on complexes.
Source: Stacks 03D6 (blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
abbrev inverseComplex :=
  (inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ)

/-- Z as a functor of P. Source: Stacks 03EL
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
abbrev leftComplex :=
  inverseComplex l E g ⋙ completedOrdinaryScalarComplex l E L ι X

/-- G_L Q as a functor of P. Source: Stacks 03EL
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
abbrev rightComplex :=
  completedOrdinaryScalarComplex l E L ι Y ⋙ inverseComplex l L g

/-- The lower left: reduce over E, transport its finite action, then extend to L.
Source: Stacks 03EK and 03EL
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
abbrev finiteLeft (n : ℕ) :=
  unrestrictedIntegralFiniteComplex l E Y n ⋙
    (inverseImageFiniteModules l E g n).mapHomologicalComplex (.up ℤ) ⋙
      (finiteExtension l E L ι X n).mapHomologicalComplex (.up ℤ)

/-- The lower right: extend directly to L's finite coefficients, then inverse image.
Source: Stacks 03EK and 03EL
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
abbrev finiteRight (n : ℕ) :=
  integralScalarFiniteComplex l E L ι Y n ⋙
    (inverseImageFiniteModules l L g n).mapHomologicalComplex (.up ℤ)

/-- Lower-left complex with its completed L action, for quotient and transition maps.
Source: Stacks 03D2 (blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
abbrev restrictedLeft (n : ℕ) :=
  finiteLeft l E L ι g n ⋙ integralOperationsRestrict l L X n

/-- Lower-right complex with its completed L action, for quotient and transition maps.
Source: Stacks 03D2 (blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
abbrev restrictedRight (n : ℕ) :=
  finiteRight l E L ι g n ⋙ integralOperationsRestrict l L X n

/-- A double tensor in the lower-left complex, in the canonical sectionwise model.
Source: Stacks 03EK and 03EL
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
def doublePure (n : ℕ) (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (i : ℤ) (U : X.ProEt)
    (s : (integralCoefficientCommRingSheaf l L X n).obj.obj (op U))
    (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj
      (op ((proEtaleIsoPostcompose g).obj U)))
    (x : (P.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    (((restrictedLeft l E L ι g n).obj P).X i).val.obj (op U) :=
  finitePure l E L ι X n
    ((inverseImageFiniteModules l E g n).obj
      ((unrestrictedIntegralReductionFunctor l E Y n).obj (P.X i))) (op U) s
    (unrestrictedIntegralTensorSection l E Y n (P.X i)
      (op ((proEtaleIsoPostcompose g).obj U)) a x)

attribute [local irreducible] completedScalarChangeData completedOrdinaryScalarExtension
  completedDerivedScalarExtension completedScalarCounit completedScalarTensorSection
  integralScalarReductionWitness integralScalarReduction integralScalarTensorSection
  unrestrictedIntegralReductionExistence unrestrictedIntegralReductionFunctor
  unrestrictedIntegralTensorSection inverseImageCompletedCoefficientMap finiteChangeData
  finitePure doublePure

/-- K-flatness and flat terms for inverse image, Q and Z.
Source: the node calculation, Steps 1–7; Stacks 03EK, 03EL and 06YY
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
def PreservesModels : Prop :=
    ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
      integralOperationsGoodComplex l E X ((inverseComplex l E g).obj P.obj) ∧
      integralOperationsGoodComplex l L Y
        ((completedOrdinaryScalarComplex l E L ι Y).obj P.obj) ∧
      integralOperationsGoodComplex l L X ((leftComplex l E L ι g).obj P.obj)

/-- The local formula for the completed tensor isomorphism.
Source: the node calculation, Steps 1–7; Stacks 03EK, 03EL and 06YY
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
def CompletedFormula
    (b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
        (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g) : Prop :=
    ∀ (P : (integralOperationsGoodComplex l E Y).FullSubcategory) (i : ℤ) (U : X.ProEt)
      (s : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj
        (op ((proEtaleIsoPostcompose g).obj U)))
      (x : (P.obj.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
      ((b.hom.app P).f i).val.app (op U)
        (completedScalarTensorSection l E L ι X
          (((inverseComplex l E g).obj P.obj).X i) (op U)
          ((inverseImageCompletedCoefficientMap l L g).hom.app (op U) s) x) =
        completedScalarTensorSection l E L ι Y (P.obj.X i)
          (op ((proEtaleIsoPostcompose g).obj U)) s x

/-- The finite comparison on double pure tensors.
Source: the node calculation, Steps 1–7; Stacks 03EK, 03EL and 06YY
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
def FiniteFormula
    (bfin : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ finiteLeft l E L ι g n ≅
          (integralOperationsGoodComplex l E Y).ι ⋙ finiteRight l E L ι g n) : Prop :=
    ∀ (n : ℕ) (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (i : ℤ) (U : X.ProEt)
      (s : (integralCoefficientCommRingSheaf l L X n).obj.obj (op U))
      (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj
        (op ((proEtaleIsoPostcompose g).obj U)))
      (x : (P.obj.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
      (((integralOperationsRestrict l L X n).map ((bfin n).hom.app P)).f i).val.app (op U)
        (doublePure l E L ι g n P.obj i U s a x) =
      integralScalarTensorSection l E L ι Y n (P.obj.X i)
        (op ((proEtaleIsoPostcompose g).obj U))
        ((@id ((integralCoefficientCommRingSheaf l L Y n).obj.obj
            (op ((proEtaleIsoPostcompose g).obj U)))
          ((inv (inverseImageFiniteCoefficientMap l L g n)).hom.app (op U) s)) *
          (integralScalarQuotientSheafMap l E L ι Y n).hom.app
            (op ((proEtaleIsoPostcompose g).obj U)) a) x

/-- The canonical quotient from Z on pure tensors.
Source: the node calculation, Steps 1–7; Stacks 03EK, 03EL and 06YY
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
def LeftQuotientFormula
    (vleft : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g n) : Prop :=
    ∀ (n : ℕ) (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (i : ℤ) (U : X.ProEt)
      (s : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj
        (op ((proEtaleIsoPostcompose g).obj U)))
      (x : (P.obj.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
      (((vleft n).app P).f i).val.app (op U)
        (completedScalarTensorSection l E L ι X
          (((inverseComplex l E g).obj P.obj).X i) (op U)
          ((inverseImageCompletedCoefficientMap l L g).hom.app (op U) s) x) =
      doublePure l E L ι g n P.obj i U
        ((completedIntegralCommRingProjectionUnrestricted l L X n).hom.app (op U)
          ((inverseImageCompletedCoefficientMap l L g).hom.app (op U) s)) 1 x

/-- The inverse image of the coefficient quotient from Q.
Source: the node calculation, Steps 1–7; Stacks 03EK, 03EL and 06YY
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
def RightQuotientFormula
    (vright : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g n) : Prop :=
    ∀ (n : ℕ) (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (i : ℤ) (U : X.ProEt)
      (s : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj
        (op ((proEtaleIsoPostcompose g).obj U)))
      (x : (P.obj.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
      (((vright n).app P).f i).val.app (op U)
        (completedScalarTensorSection l E L ι Y (P.obj.X i)
          (op ((proEtaleIsoPostcompose g).obj U)) s x) =
      integralScalarTensorSection l E L ι Y n (P.obj.X i)
        (op ((proEtaleIsoPostcompose g).obj U))
        ((completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app
          (op ((proEtaleIsoPostcompose g).obj U)) s) x

/-- The specified completed-to-finite square.
Source: the node calculation, Steps 1–7; Stacks 03EK, 03EL and 06YY
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
def QuotientSquare
    (b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
        (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g)
    (bfin : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ finiteLeft l E L ι g n ≅
          (integralOperationsGoodComplex l E Y).ι ⋙ finiteRight l E L ι g n)
    (vleft : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g n)
    (vright : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g n) : Prop :=
    ∀ (n : ℕ) (P : (integralOperationsGoodComplex l E Y).FullSubcategory),
      b.hom.app P ≫ (vright n).app P =
        (vleft n).app P ≫ (integralOperationsRestrict l L X n).map ((bfin n).hom.app P)

/-- The quotient transition on the two scalar factors on the left.
Source: the node calculation, Steps 1–7; Stacks 03EK, 03EL and 06YY
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
def LeftTransitionFormula
    (tleft : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g (n + 1) ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g n) : Prop :=
    ∀ (n : ℕ) (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (i : ℤ) (U : X.ProEt)
      (s : (integralCoefficientCommRingSheaf l L X (n + 1)).obj.obj (op U))
      (a : (integralCoefficientCommRingSheaf l E Y (n + 1)).obj.obj
        (op ((proEtaleIsoPostcompose g).obj U)))
      (x : (P.obj.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
      (((tleft n).app P).f i).val.app (op U)
        (doublePure l E L ι g (n + 1) P.obj i U s a x) =
      doublePure l E L ι g n P.obj i U
        ((integralCoefficientSheafTransition l L X n).hom.app (op U) s)
        ((integralCoefficientSheafTransition l E Y n).hom.app
          (op ((proEtaleIsoPostcompose g).obj U)) a) x

/-- The quotient transition on the final scalar factor on the right.
Source: the node calculation, Steps 1–7; Stacks 03EK, 03EL and 06YY
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
def RightTransitionFormula
    (tright : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g (n + 1) ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g n) : Prop :=
    ∀ (n : ℕ) (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (i : ℤ) (U : X.ProEt)
      (s : (integralCoefficientCommRingSheaf l L Y (n + 1)).obj.obj
        (op ((proEtaleIsoPostcompose g).obj U)))
      (x : (P.obj.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
      (((tright n).app P).f i).val.app (op U)
        (integralScalarTensorSection l E L ι Y (n + 1) (P.obj.X i)
          (op ((proEtaleIsoPostcompose g).obj U)) s x) =
      integralScalarTensorSection l E L ι Y n (P.obj.X i)
        (op ((proEtaleIsoPostcompose g).obj U))
        ((integralCoefficientSheafTransition l L Y n).hom.app
          (op ((proEtaleIsoPostcompose g).obj U)) s) x

/-- The specified finite comparison commutes with quotient transitions.
Source: the node calculation, Steps 1–7; Stacks 03EK, 03EL and 06YY
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
def TransitionSquare
    (bfin : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ finiteLeft l E L ι g n ≅
          (integralOperationsGoodComplex l E Y).ι ⋙ finiteRight l E L ι g n)
    (tleft : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g (n + 1) ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g n)
    (tright : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g (n + 1) ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g n) : Prop :=
    ∀ (n : ℕ) (P : (integralOperationsGoodComplex l E Y).FullSubcategory),
      (integralOperationsRestrict l L X (n + 1)).map ((bfin (n + 1)).hom.app P) ≫
          (tright n).app P =
        (tleft n).app P ≫ (integralOperationsRestrict l L X n).map ((bfin n).hom.app P)

/-- Canonical K-flat computations and descent of the same chain comparison.
Source: the node calculation, Steps 1–7; Stacks 03EK, 03EL and 06YY
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
def DerivedModel
    (b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
        (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g)
    (β : inverseImageIntegralDerived l E g ⋙ completedDerivedScalarExtension l E L ι X ≅
        completedDerivedScalarExtension l E L ι Y ⋙ inverseImageIntegralDerived l L g) : Prop :=
    ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
      IsIso (completedScalarCounit l E L ι Y P.obj) ∧
      IsIso (completedScalarCounit l E L ι X ((inverseComplex l E g).obj P.obj)) ∧
      β.hom.app (DerivedCategory.Q.obj P.obj) ≫
          (inverseImageIntegralDerived l L g).map (completedScalarCounit l E L ι Y P.obj) ≫
          (inverseImageIntegralModules l L g).mapDerivedCategoryFactors.hom.app
            ((completedOrdinaryScalarComplex l E L ι Y).obj P.obj) =
        (completedDerivedScalarExtension l E L ι X).map
            ((inverseImageIntegralModules l E g).mapDerivedCategoryFactors.hom.app P.obj) ≫
          completedScalarCounit l E L ι X ((inverseComplex l E g).obj P.obj) ≫
          DerivedCategory.Q.map (b.hom.app P)

/-- The completed and finite tensor comparisons, their quotient/transition squares,
and their normalized descent to the ordinary unbounded derived categories.

Source: Bhatt--Scholze, Section 6.5, Lemma 6.5.9(4) for completed pullback;
the coefficient-extension calculation is the node's agent calculation, not a
quoted assertion of Bhatt--Scholze
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model).

Proof:
1. Write j for completedCoefficientMap. Compose c_L g⁻¹(j_Y) and j_X c_E
with every finite projection. Naturality of the constant coefficient comparisons
(lem-weil-proetale-isomorphism-inverse-image), the defining equations of c_E,c_L
(def-weil-inverse-image-pullback-comparison), and the same-index quotient maps
(def-weil-integral-scalar-extension) give identical components. The limit
universal property (def-pur-sheaf-inverse-limit) gives equality.
2. Apply lem-weil-pbc-ringed-topoi-derived-tensor-pullback to (g⁻¹,c_E).
It preserves K-flat complexes with flat terms. Apply lem-pur-kflat-change-of-rings
to R_Y → S_Y and R_X → S_X to obtain the assertions for Q and Z.
3. The sheafified balanced tensor comparison of
lem-pur-isomorphism-inverse-image-tensor-hom sends c_L(s) tensor g⁻¹(p)
to g⁻¹(s tensor p). Step 1 identifies the actions. Naturality in each term
makes this a natural chain isomorphism; tensor with a coefficient ring in
degree zero has differential d tensor 1 (def-pc-tensor-complex-sheaves).
4. Reduce at level n+1. Balanced reassociation sends t tensor (a tensor p)
to t*iota(a) tensor p; its inverse inserts 1 in the middle factor.
Transport by c_E,c_L gives exactly the finite formula below, in both directions.
These local maps descend through sheafification (def-pur-sheaf-tensor-product).
5. Both routes around the quotient square send c_L(s) tensor g⁻¹(p)
to g⁻¹(pi_L(s) tensor p). Both routes around a transition square send
t tensor (a tensor p) to q_L(t)*iota(q_E(a)) tensor p. The coefficient
projection equations and q_L*iota_(n+1)=iota_n*q_E identify the results,
also for ramified extensions. Local tensor generation proves the equalities.
6. Choose a flat-term K-flat resolution (lem-pc-kflat-resolution).
Exact inverse image preserves its quasi-isomorphism, and step 2 makes its
inverse image K-flat. The counits of lem-pur-derived-change-of-rings identify
Q and Z with the specified ordinary derived extensions. Localize b_P.
7. Naturality of the local formula gives b_P' (G_E(f) tensor 1) =
G_L(f tensor 1) b_P, also on chain homotopies. Scalar extension preserves
quasi-isomorphisms between K-flat complexes (lem-pur-derived-change-of-rings).
The K-flat localization equivalence of lem-weil-pbc-site-derived-tensor-descent
therefore descends b uniquely. Its normalized representative equation below
implies independence under all canonical K-flat representative comparisons.
No boundedness, completeness, or constructibility is used. -/
theorem isomorphism_scalar_tensor_kflat_model
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    ∃ (b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
        (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g)
      (β : inverseImageIntegralDerived l E g ⋙ completedDerivedScalarExtension l E L ι X ≅
        completedDerivedScalarExtension l E L ι Y ⋙ inverseImageIntegralDerived l L g)
      (bfin : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ finiteLeft l E L ι g n ≅
          (integralOperationsGoodComplex l E Y).ι ⋙ finiteRight l E L ι g n)
      (vleft : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g n)
      (vright : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g n)
      (tleft : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g (n + 1) ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g n)
      (tright : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g (n + 1) ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g n),
    PreservesModels l E L ι g ∧
    CompletedFormula l E L ι g b ∧
    FiniteFormula l E L ι g bfin ∧
    LeftQuotientFormula l E L ι g vleft ∧
    RightQuotientFormula l E L ι g vright ∧
    QuotientSquare l E L ι g b bfin vleft vright ∧
    LeftTransitionFormula l E L ι g tleft ∧
    RightTransitionFormula l E L ι g tright ∧
    TransitionSquare l E L ι g bfin tleft tright ∧
    DerivedModel l E L ι g b β := by
  sorry

end AlgebraicGeometry.ProEtale.IsomorphismScalarTensor
