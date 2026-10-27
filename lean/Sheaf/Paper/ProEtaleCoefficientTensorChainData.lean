/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ProEtaleCoefficientPullback
public import Sheaf.Algebra.Homology.RingIsomorphismTensorTransport
public import Sheaf.Paper.ProEtaleCoefficientTensorIso
import all Sheaf.Paper.ProEtaleCoefficientOrdinaryTensorSquare
import Sheaf.Algebra.Homology.TensorTotalComparisonSquare

/-! # The chain square for change of coefficient isomorphism -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
  CategoryTheory.Functor.mapHomologicalComplex
attribute [local irreducible] SheafOfModules.monoidalCategory
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CoefficientTensorChain

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

attribute [local irreducible] ordinaryPullback proEtaleOrdinaryTensorPullback
  proEtaleRingModulePullback

private theorem total_summand (P Q : CochainComplex (proEtaleRingModules Y R) ℤ)
    (a b n : ℤ) (h : a + b = n) :
    CochainComplex.ιMapBifunctor
        (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj P)
        (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj Q)
        (proEtaleOrdinaryTensor X S) a b n h ≫
        ((proEtaleTensorPullbackTotalIso f R S c P Q).hom.f n) =
      (proEtaleOrdinaryTensorPullback f R S c (P.X a) (Q.X b)).inv ≫
        (proEtaleRingModulePullback f R S c).map
          (CochainComplex.ιMapBifunctor P Q (proEtaleOrdinaryTensor Y R) a b n h) := by
  dsimp only [proEtaleTensorPullbackTotalIso, asIso_hom,
    proEtaleTensorPullbackTotal, tensorPullbackTotal, tensorPullbackTotalComponent]
  exact HomologicalComplex.ι_mapBifunctorDesc _ _ _ _

attribute [local irreducible] tensorIso complexPullback proEtaleTensorPullbackTotalIso

set_option maxHeartbeats 800000 in
-- Elaborate the three termwise tensor comparisons with their coefficient universes.
/-- The normalized restriction tensor map commutes with ordinary geometric tensor
pullback, as an equality of chain maps before localization.

Source: Stacks, Modules on Sites, Tag 03EL, its universal bilinear-map proof;
Cohomology on Sites, Tag 07A4, signed direct-sum totalization.
(blueprint: lem-pbc-coefficient-restriction-tensor-chain-square)

Proof: the supplied ring-isomorphism transport is normalized on pure tensors by
its pure_hom field and on each totalization summand by its total_summand field.
Precompose both sides in each total degree with each bidegree coproduct injection.
Use total_summand for the restriction map and the signed-total definition of each
geometric tensor pullback comparison. It remains to compare module sheaf maps.
Precompose with the sheafification unit and use the adjunction-unit normalization
of the geometric tensor pullbacks and ordinaryPullback. Both maps send a generalized
pure tensor to the same pair of inverse-image sections with scalar action changed
by c. TensorProduct.ext proves equality on presheaf tensors; the sheafification
adjunction then gives equality on sheaf tensors. Scalar restriction along c is an
equivalence and preserves these coproducts. Their universal property proves equality
of the degree maps, and extensionality gives the equality of chain maps. No derived
tensor model, localization or flatness assumption enters this calculation. The proof
also applies to zero coefficients, zero complexes, empty sites, and c equal to the
identity: it uses only tensor and coproduct universal properties. -/
theorem restriction_tensor_chain_square (o : SheafOfModules.RingIsoTensorTransport
    (J := ProEt.topology X)
    (R := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (S := S) c) :
    ∀ P Q : CochainComplex (proEtaleRingModules Y R) ℤ,
        (complexPullback f R S c).hom.app ((total Y R).obj (P, Q)) ≫
            (proEtaleTensorPullbackTotalIso f R
              ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
              (Iso.refl _) P Q).inv =
          ((pbcRestrict c.hom).mapHomologicalComplex (.up ℤ)).map
              (proEtaleTensorPullbackTotalIso f R S c P Q).inv ≫
            (tensorIso f R S c o).hom.app
              (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj P,
                ((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj Q) ≫
            (total X ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)).map
              (Prod.mkHom ((complexPullback f R S c).hom.app P)
                ((complexPullback f R S c).hom.app Q)) := by
  intro P Q
  let U := pbcRestrict c.hom
  have : U.IsEquivalence := by
    change (SheafOfModules.scalarRestriction c.hom).IsEquivalence
    rw [← o.functor_eq]
    infer_instance
  exact HomologicalComplex.tensorTotalComparisonSquare
    (proEtaleRingModulePullback f R S c) U
    (proEtaleRingModulePullback f R
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _))
    (proEtaleOrdinaryTensor Y R) (proEtaleOrdinaryTensor X S)
    (proEtaleOrdinaryTensor X ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R))
    (ordinaryPullback f R S c) (complexPullback f R S c)
    (complex_component f R S c)
    (proEtaleOrdinaryTensorPullback f R S c)
    (proEtaleOrdinaryTensorPullback f R
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _))
    (proEtaleTensorPullbackTotalIso f R S c)
    (proEtaleTensorPullbackTotalIso f R
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _))
    (total_summand f R S c)
    (total_summand f R
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _))
    o.monoidal.toMonoidal.toOplaxMonoidal.δ (tensorIso f R S c o)
    (tensorIso_summand f R S c o)
    (ordinary_bifunctor_square f R S c o) P Q


/-- Localization of the normalized chain square.
Source: functoriality of localization, Stacks Tag 07A4.
(blueprint: lem-pbc-coefficient-restriction-tensor-chain-square) -/
theorem restriction_tensor_localized_square
    (o : SheafOfModules.RingIsoTensorTransport (J := ProEt.topology X)
      (R := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (S := S) c)
    (P Q : CochainComplex (proEtaleRingModules Y R) ℤ) :
    DerivedCategory.Q.map ((complexPullback f R S c).hom.app ((total Y R).obj (P, Q))) ≫
      DerivedCategory.Q.map (proEtaleTensorPullbackTotalIso f R
        ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _) P Q).inv =
    DerivedCategory.Q.map (((pbcRestrict c.hom).mapHomologicalComplex (.up ℤ)).map
      (proEtaleTensorPullbackTotalIso f R S c P Q).inv) ≫
      DerivedCategory.Q.map ((tensorIso f R S c o).hom.app
        (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj P,
          ((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj Q)) ≫
      DerivedCategory.Q.map
        ((total X ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)).map
          (Prod.mkHom ((complexPullback f R S c).hom.app P)
            ((complexPullback f R S c).hom.app Q))) := by
  simpa only [Functor.map_comp] using congrArg DerivedCategory.Q.map
    (restriction_tensor_chain_square f R S c o P Q)

end AlgebraicGeometry.Scheme.CoefficientTensorChain
