/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4 -/
module

public import Sheaf.Paper.SemilinearSystemModels
import Sheaf.Algebra.Homology.CochainTensorModelRigidity

/-! # Uniqueness from tensor representatives
Source: Stacks 06YU and 07A4. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
universe c v r
open CategoryTheory CategoryTheory.Limits
namespace WeilConjectures.SemilinearSections

variable {C C' : Type c} [Category.{v} C] [Category.{v} C']
  [EssentiallySmall.{max c v r} C] [EssentiallySmall.{max c v r} C']
  (J : GrothendieckTopology C) (J' : GrothendieckTopology C')
  (R : Sheaf J CommRingCat.{max c v r}) (S : Sheaf J' CommRingCat.{max c v r})
  (F : Mod.{c, v, max c v r} J R ⥤ Mod.{c, v, max c v r} J' S)
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (A : Closed.{c, v, r} J R) (B : Closed.{c, v, r} J' S)
  (TA : Models.{c, v, r} J R A) (TB : Models.{c, v, r} J' S B)

/-- A derived tensor comparison is determined by its inverse representative equations.
Source: Stacks 06YU (blueprint: lem-sf-system-pullback-tensor-normalization).
Proof: restriction to pairs of K-flat flat-term complexes is faithful by the tensor
model rigidity theorem. At each pair cancel the invertible tensor model and exact
factorization arrows. The two given equations then identify the inverse comparisons. -/
theorem tensorComparison_unique_on_flat_representatives
    (m n : A.tensor ⋙ F.mapDerivedCategory ≅
      (F.mapDerivedCategory.prod F.mapDerivedCategory) ⋙ B.tensor)
    (K : TensorComparisonModel.{c, v, r} J J' R S F A B TA TB m)
    (hn : ∀ (P Q : CochainComplex (Mod.{c, v, max c v r} J R) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q)
      (flatP : flatTerms.{c, v, r} J R P) (flatQ : flatTerms.{c, v, r} J R Q),
      (tensorModelIso.{c, v, r} J' S B TB
        ((F.mapHomologicalComplex (.up ℤ)).obj P)
        ((F.mapHomologicalComplex (.up ℤ)).obj Q)
        (K.kflat P hP flatP) (K.kflat Q hQ flatQ)).hom ≫
      B.tensor.map (Prod.mkHom (F.mapDerivedCategoryFactors.inv.app P)
        (F.mapDerivedCategoryFactors.inv.app Q)) ≫
      n.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      F.mapDerivedCategory.map ((tensorModelIso.{c, v, r} J R A TA P Q hP hQ).inv) ≫
      F.mapDerivedCategoryFactors.hom.app ((totalTensor.{c, v, r} J R).obj (P, Q)) =
        DerivedCategory.Q.map (K.chain P Q)) : m = n := by
  apply (Iso.symm_bijective).injective
  apply Iso.ext
  obtain ⟨_, _, _, hf⟩ := SheafOfModules.cochain_tensor_model_rigidity J R
  apply (hf _ inferInstance _ _).1
  apply NatTrans.ext
  funext X
  rcases X with ⟨P, Q⟩
  change m.inv.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) =
    n.inv.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)
  have hP := P.property.1
  have hQ := Q.property.1
  have flatP := P.property.2
  have flatQ := Q.property.2
  let e := B.tensor.mapIso (Iso.prod
    (F.mapDerivedCategoryFactors.app P.obj).symm
    (F.mapDerivedCategoryFactors.app Q.obj).symm)
  apply (cancel_epi e.hom).1
  apply (cancel_epi (tensorModelIso.{c, v, r} J' S B TB
    ((F.mapHomologicalComplex (.up ℤ)).obj P.obj)
    ((F.mapHomologicalComplex (.up ℤ)).obj Q.obj)
    (K.kflat P.obj hP flatP) (K.kflat Q.obj hQ flatQ)).hom).1
  apply (cancel_mono (F.mapDerivedCategory.map
    ((tensorModelIso.{c, v, r} J R A TA P.obj Q.obj hP hQ).inv) ≫
      F.mapDerivedCategoryFactors.hom.app ((totalTensor.{c, v, r} J R).obj
        (P.obj, Q.obj)))).1
  simpa only [e, Functor.mapIso_hom, Iso.prod_hom, Iso.app_hom, Iso.app_inv,
    Iso.symm_hom, Iso.symm_inv, Category.assoc] using
    (K.derived P.obj Q.obj hP hQ flatP flatQ).trans
      (hn P.obj Q.obj hP hQ flatP flatQ).symm

end WeilConjectures.SemilinearSections
