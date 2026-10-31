/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Integral.AdicIntegralTensorCoordinates
public import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.Algebra.Homology.BifunctorFlip
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses

/-! # Comparing normalized ordinary integral tensor presentations

Source: Stacks 07A4, 06YS; Bhatt--Scholze Definition 3.4.10.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- The unique comparison obtained by descending the two signed total-tensor models.
It is constructed by fully faithful restriction, without choosing an unproved witness.
Source: Stacks 07A4 and 06YS.
(blueprint: def-sf-adic-tensor-presentation-comparison). -/
def tensorPresentationComparison (N : ConstructibleTensorCompletionPresentation l E X) :
    N.tensor ≅ (pullbackTensorCalculus l E X).integralClosed.tensor := by
  let G := integralOperationsGoodComplex l E X
  let q := integralOperationsGoodLocalization l E X
  let i := ObjectProperty.lift
    (CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted l E X) :
        ObjectProperty (CochainComplex (integralTowerModules l E X) ℤ)) G.ι
    (fun P ↦ P.property.1)
  let r := Functor.isoWhiskerLeft (i.prod i)
    (pullbackTensorCalculus l E X).integralTensorModel.comparison
  let T := (Functor.whiskeringLeft _ _
    (DerivedCategory (integralTowerModules l E X))).obj (q.prod q)
  let h := (SheafOfModules.cochain_tensor_model_rigidity (ProEt.topology X)
    (completedIntegralCommRingSheafUnrestricted l E X)).choose_spec.2.2
  let ff : T.FullyFaithful :=
    ((Functor.FullyFaithful.nonempty_iff_map_bijective T).2
      (fun U V ↦ h _ inferInstance U V)).some
  exact ff.preimageIso (N.model.symm ≪≫ r)

attribute [local irreducible] tensorPresentationComparison

/-- The quotient-completion map expressed on the fixed ambient ordinary tensor.
Source: Bhatt--Scholze Definition 3.4.10.
(blueprint: def-sf-adic-tensor-presentation-comparison). -/
def tensorPresentationCompletion (N : ConstructibleTensorCompletionPresentation l E X) :
    (pullbackTensorCalculus l E X).integralClosed.tensor ⟶ integralCompletedTensor l E X :=
  (tensorPresentationComparison l E X N).inv ≫ N.comparison

/-- Balanced scalar extension expressed on the fixed ambient ordinary tensor.
Source: BS Proposition 6.8.14 and Remark 6.8.15.
(blueprint: def-sf-adic-tensor-presentation-comparison). -/
def finiteAmbientScalarTensor (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] (A : At l X R)
    (I : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (N : FiniteNormalization l X R A I) :
    (pullbackTensorCalculus l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) I) X).integralClosed.tensor
        ⋙
        pbcDerivedExtend (coefficientMap l X R I) ≅
    ((pbcDerivedExtend (coefficientMap l X R I)).prod
      (pbcDerivedExtend (coefficientMap l X R I))) ⋙ A.closed.tensor :=
  Functor.isoWhiskerRight (tensorPresentationComparison l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) I) X N.completion).symm
      (pbcDerivedExtend (coefficientMap l X R I)) ≪≫ N.ordinary

private theorem map_iso_cancellation {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {a b c : C} {d : D} (e : a ≅ b) (t : a ⟶ c)
    (s : d ⟶ F.obj a) :
    s ≫ F.map t = (s ≫ F.map e.hom) ≫ F.map (e.inv ≫ t) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.map_comp_assoc, e.hom_inv_id, F.map_id, Category.id_comp]

/-- Factor the finite tensor map into ordinary scalar tensor and integral completion.
Source: BS Definition 3.4.10 and Remark 6.8.15.
(blueprint: def-sf-adic-tensor-presentation-comparison). -/
theorem finiteIntegralTensorMap_factor (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] (A : At l X R)
    (I : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (N : FiniteNormalization l X R A I)
    (K L : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) I) X) :
    finiteIntegralTensorMap l X R A I N K L =
      (finiteAmbientScalarTensor l X R A I N).inv.app (K.obj, L.obj) ≫
        (pbcDerivedExtend (coefficientMap l X R I)).map
          ((tensorPresentationCompletion l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) I) X
              N.completion).app (K.obj, L.obj)) := by
  exact map_iso_cancellation (pbcDerivedExtend (coefficientMap l X R I))
    ((tensorPresentationComparison l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) I) X
        N.completion).app (K.obj, L.obj))
    (N.completion.comparison.app (K.obj, L.obj)) (N.ordinary.inv.app (K.obj, L.obj))

end WeilConjectures.AdicQbarRealization
