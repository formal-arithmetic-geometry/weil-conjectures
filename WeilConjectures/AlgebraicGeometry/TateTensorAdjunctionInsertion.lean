/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
public import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.CategoryTheory.Exact.NormalizedTensorAdjunctionInsertion
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorFactorization
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorHomotopyFactorization

/-! # Tensor of normalized scalar-adjunction insertions

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-setup/sec-the-purity-statement/sk-thm-purity-transport/sk-thm-purity-transport.proof.md,
Step 1 (compatibility with the finite reductions), finite-level scalar/tensor reduction.
(blueprint: lem-pur-tate-tensor-adjunction-insertion)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Etale

private theorem flat_single_comparison
    {B : Type (u + 1)} [CommRing B] (T : Scheme.{u})
    (L M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B))
    (hL : ObjectProperty.flat L) :
    (singleFunctorObjTensorIso L M hL).hom =
      Functor.LaxMonoidal.μ DerivedCategory.Q
        ((CochainComplex.singleFunctor _ 0).obj L)
        ((CochainComplex.singleFunctor _ 0).obj M) ≫
        DerivedCategory.Q.map (singleCochainTensorIso L M).hom := by
  rw [singleFunctorObjTensorIso_homotopy_factorization L M hL]
  simp only [singleFunctorObjIsoQh, DerivedCategory.singleFunctorIsoCompQ]
  simp only [Functor.LaxMonoidal.transport_μ, Functor.LaxMonoidal.comp_μ, Category.assoc]
  erw [← DerivedCategory.quotientCompQhIso_hom_naturality]
  have hμ (K N : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ) :
      DerivedCategory.Qh.map (Functor.LaxMonoidal.μ
        (HomotopyCategory.quotient (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) (.up ℤ))
        K N) = 𝟙 _ := DerivedCategory.Qh.map_id _
  rw [hμ]
  erw [Category.id_comp]
  erw [Iso.trans_hom, Iso.trans_hom, Iso.trans_inv]
  have h1 (X : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) :
      ((Iso.refl (DerivedCategory.singleFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) 0)).app X).hom = 𝟙 _ := rfl
  have h2 (X : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) :
      ((Iso.refl (DerivedCategory.singleFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) 0)).app X).inv = 𝟙 _ := rfl
  erw [h1, h1, h2, Category.id_comp, Category.id_comp, Category.comp_id]
  rfl

private theorem mapComplex_unit_formula
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {E : C ⥤ D} {U : D ⥤ C} [E.Additive] [U.Additive] (adj : E ⊣ U)
    (P : CochainComplex C ℤ) :
    (adj.mapHomologicalComplex (.up ℤ)).unit.app P =
      (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
        (NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ U)) (.up ℤ)).inv.app P := by
  ext i
  simp only [Functor.id_obj, Functor.comp_obj, Adjunction.mapHomologicalComplex_unit_app_f,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplexIdIso_inv_app_f,
    NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
    Iso.refl_inv, NatTrans.id_app]
  erw [Category.id_comp, Category.comp_id]

-- The kernel re-check of the final instantiation of the generic normalized tensor lemma
-- (scalarAdjointInsertion's derived adjunction against `E ⊣ U.mapDerivedCategory`) exceeds
-- the default budget; elaboration itself is within it.
set_option maxHeartbeats 2000000 in
/-- Tensoring the two normalized scalar insertions agrees with inserting their ordinary
semilinear tensor product, under the published scalar tensorator and flat-single comparisons.
The ordinary restriction tensorator is `Functor.LaxMonoidal.μ` of exact scalar restriction.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-setup/sec-the-purity-statement/sk-thm-purity-transport/sk-thm-purity-transport.proof.md,
Step 1 (compatibility with the finite reductions), finite-level scalar/tensor reduction.
(blueprint: lem-pur-tate-tensor-adjunction-insertion)

Proof:
1. The tensor of the two flat source sheaves is flat by exactness of successive tensoring.
Scalar extension of a flat sheaf is flat: restriction identifies tensoring with its extension
with ordinary tensoring by that sheaf. Restriction preserves and reflects exactness. This
uses the sheaf tensor balancing relations and the exact restriction in
`lem-pur-sheaf-ring-derived-coefficient-adjunction`; no flatness of the ring map is needed.
2. For each source sheaf and their tensor, use its flat single as a K-flat representative
(`lem-sf-etale-single-flat-tensor`). The normalized coefficient adjunction identifies its
insertion with the canonical scalar representative followed by the single of the ordinary
adjunct, sending x tensor b to b times eta(x). The inverse exact-single comparison in
`def-sp-exact-degree-zero-adjoint-interface` is precisely the one in this calculation.
3. The representative square of `def-pur-exceptional-coefficient-normalizations` identifies
the published tensorIso with balancing (x tensor y) tensor b mapped to
(x tensor 1) tensor (y tensor b). Apply
`lem-pur-etale-single-tensorator-naturality` to the two ordinary adjuncts and cancel the
canonical representative isomorphisms. The desired equation reduces to equality of the
ordinary balanced tensor maps. All complexes are in degree zero, so no shift sign occurs.
4. The left ordinary composite sends (x tensor y) tensor b to
eta1(x) tensor b eta2(y), equal to b times (eta1(x) tensor eta2(y)), the right composite.
The formulas are balanced and commute with restriction. The presheaf tensor universal
property and then sheafification prove equality of sheaf maps. This uses
`def-pur-sheaf-tensor-product`, without any assertion about generation of global sections.
Apply the single functor and the representative square to obtain the displayed equality. -/
theorem tateTensor_scalarAdjointInsertion
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u})
    (L₁ L₂ : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (P₁ P₂ : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B))
    (hL₁ : ObjectProperty.flat L₁) (hL₂ : ObjectProperty.flat L₂)
    (hP₁ : ObjectProperty.flat P₁) (hP₂ : ObjectProperty.flat P₂)
    (η₁ : L₁ ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).obj P₁)
    (η₂ : L₂ ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).obj P₂) :
    (ExceptionalCoefficients.tensorIso φ T).hom.app
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L₁,
          (_root_.DerivedCategory.singleFunctor _ 0).obj L₂) ≫
      (SheafExactDegreeZero.scalarAdjointInsertion T.smallEtaleTopology φ η₁ ⊗ₘ
        SheafExactDegreeZero.scalarAdjointInsertion T.smallEtaleTopology φ η₂) ≫
      (singleFunctorObjTensorIso P₁ P₂ hP₁).hom =
    (scalarExtension φ T).map (singleFunctorObjTensorIso L₁ L₂ hL₁).hom ≫
      SheafExactDegreeZero.scalarAdjointInsertion T.smallEtaleTopology φ
        ((η₁ ⊗ₘ η₂) ≫
          Functor.LaxMonoidal.μ (Sheaf.restrictScalars T.smallEtaleTopology φ) P₁ P₂) := by
  let F := ProEtale.etaleSheafExtendScalars φ T
  let U := Sheaf.restrictScalars T.smallEtaleTopology φ
  let a : F ⊣ U := ProEtale.etaleSheafExtendScalarsAdjunction φ T
  let : F.IsLeftAdjoint := a.isLeftAdjoint
  let : F.OplaxMonoidal := composeAndSheafifyOplaxMonoidal T.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u + 1} φ)
  let E := scalarExtension φ T
  let ad : E ⊣ U.mapDerivedCategory := Adjunction.ofIsRightAdjoint _
  have : a.IsMonoidal := by
    exact isMonoidal_sheafAdjunction T.smallEtaleTopology
      (ModuleCat.extendRestrictScalarsAdj.{u + 1} φ)
  have hrep (P : CochainComplex
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
      scalarExtensionRepresentative φ T P = (ad.homEquiv _ _).symm
        (DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
          U.mapDerivedCategoryFactors.inv.app
            ((F.mapHomologicalComplex (.up ℤ)).obj P)) := by
    unfold scalarExtensionRepresentative
    rw [mapComplex_unit_formula a P]
    rfl
  have hn : ExceptionalCoefficients.TensorNormalization φ T
      (ExceptionalCoefficients.tensorIso φ T) := by
    have he : ExceptionalCoefficients.tensorIso φ T =
        (ExceptionalCoefficients.tensorIso_existsUnique φ T).choose :=
      eq_of_heq (ExceptionalCoefficients.siteTensorIso_existsUnique φ T).choose_spec.1
    rw [he]
    exact (ExceptionalCoefficients.tensorIso_existsUnique φ T).choose_spec.1
  rw [flat_single_comparison T P₁ P₂ hP₁, flat_single_comparison T L₁ L₂ hL₁]
  unfold SheafExactDegreeZero.scalarAdjointInsertion
  have key := SheafExactDegreeZero.normalizedTensor_adjointInsertion F U a E ad
    (scalarExtensionRepresentative φ T) hrep (ExceptionalCoefficients.tensorIso φ T)
    hn L₁ L₂ P₁ P₂ η₁ η₂
  exact key

end AlgebraicGeometry.Etale
