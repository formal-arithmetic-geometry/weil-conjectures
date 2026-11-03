/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.FiniteSiteTensorProjection
import WeilConjectures.AlgebraicGeometry.DerivedSingleUnitRightUnitor

/-!
# Tensor comparison followed by a trace and the right unit

Source: the projective counit identification in the first paragraph of
`lem-amb-affine-space-top-trace.proof.md`.
(blueprint: lem-route-tensor-trace-right-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

/-- Naturality of tensor comparison, followed by its defining right-unit constraint.
Source: the projective-line counit identification in the first paragraph of
`lem-amb-affine-space-top-trace.proof.md`.
(blueprint: lem-route-tensor-trace-right-unit)

Proof: the single-unit factor before the ordinary right unitor cancels by the
canonical unit identity. Naturality of the tensor comparison moves the tensor of
the trace across its component. Expand rightUnit, which consists of the inverse
unit component followed by the image of the ordinary right unitor. Cancel that
component with its inverse, and combine the comparison images by functoriality.
All cancellations are categorical identities, valid also for zero rings and
empty schemes.
-/
theorem tensorComparison_trace_rightUnit
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (K L : Etale.DerivedCategoryModule A T) (t : L ⟶ Etale.ordinaryFiniteUnit A T) :
    (tensorComparison A T K L).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} A) T).obj ((comparison A T).obj K)).map
          ((comparison A T).map t) ≫ (rightUnit A T K).hom =
      (comparison A T).map (((Etale.ordinaryFiniteTensor A T).obj K).map t ≫
        (Etale.derivedTensorSingleUnitIso K).hom) := by
  let C := comparison A T
  let G := (derivedTensor (ModuleCat.{u + 1} A) T).obj (C.obj K)
  have hn : C.map (((Etale.ordinaryFiniteTensor A T).obj K).map t) ≫
        (tensorComparison A T K (Etale.ordinaryFiniteUnit A T)).hom =
      (tensorComparison A T K L).hom ≫ G.map (C.map t) := by
    simpa only [C, G, tensorComparison, comparison, geoP1Comparison,
      Etale.ordinaryFiniteTensor, Functor.comp_map, Iso.app_hom] using
      (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} A) K).hom.naturality t
  simp only [Etale.derivedTensorSingleUnitIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [Etale.map_singleFunctorObjUnitIso_hom_comp, Functor.map_comp]
  rw [← reassoc_of% hn]
  simp only [rightUnit, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.hom_inv_id_assoc]
  rfl

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
