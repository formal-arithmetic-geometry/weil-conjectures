/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q160
-/
module

public import Sheaf.Paper.WeilTensorProduct
public import Sheaf.Paper.PbcWeilCategory
public import Sheaf.Paper.PbcUniformCompleteTriangulated
public import Sheaf.CategoryTheory.ScalarLocalizationTriangulated
public import Sheaf.Paper.LocalizedTStructure
import Sheaf.Paper.PbcRationalCategory
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.WeilCompletedTensorReflector
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
import Sheaf.CategoryTheory.RingedCompleteTriangulated

/-! # Tensor product of rational adic Weil complexes

Source: Weil blueprint, sec-algebraic-groups-lie-algebras/sk-p-cyclotomic,
Tensor product of Weil complexes (blueprint: lem-wf-tensor-weil).
The coefficient category is the existing raw rationalization of compatible uniform
integral complexes. Exactness is asserted only on that underlying coefficient category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local irreducible] wfRationalTensor wfConstructibleInclusion
  wfRationalTensorPullback WeilConjectures.wfWeilStructure
  ScalarLocalization.category ScalarLocalization.preadditive
  ScalarLocalization.linear ScalarLocalization.linearOriginal

namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (X₀ : Over (Spec (CommRingCat.of D.k₀)))
  [IsSeparated X₀.hom] [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  (E : Padic.FiniteCoefficientFields c.l c.Qbar)

/-- The coefficient category already used by the given Weil pairs, without their structures.
Source: blueprint, Tensor product of Weil complexes (blueprint: lem-wf-tensor-weil). -/
abbrev wfTensorCoefficientCategory :=
  PbcRationalCategory (D.geometricFiber X₀).left (pbcStageDatum.{u} c.l c.Qbar E)
    (pbcStageUniformizer.{u} c.l c.Qbar E)

/-- The existing inclusion of constructible rational objects into the completed ambient
category. Source: blueprint, Tensor product of Weil complexes (blueprint: lem-wf-tensor-weil).
-/
abbrev wfTensorCoefficientInclusion :
    wfTensorCoefficientCategory D c X₀ E ⥤ WfAmbient D c X₀ E :=
  wfConstructibleInclusion (D.geometricFiber X₀).left (pbcStageDatum.{u} c.l c.Qbar E)
    1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
    (wfUniformizer_generates D c E) (pbcStageUniformizer.{u} c.l c.Qbar E)

/-- The completed tensor restricts to Weil pairs, with its specified carrier, Frobenius
and morphism formulas, and is exact in each underlying coefficient variable.
Source: Weil blueprint, sec-algebraic-groups-lie-algebras/sk-p-cyclotomic,
Tensor product of Weil complexes (blueprint: lem-wf-tensor-weil).

Proof plan:
1. Represent the two rational objects integrally. The closure statement
   lem-ag-uniform-complete-tensor places their K-flat tensor followed by the specified
   Koszul completion in the compatible uniform category. Raw localization gives T,
   with exactly the ambient object and fraction formulas of def-wf-tensor-product.
2. The ringed-topoi canonical tensor comparison is natural on K-flat models. The
   coefficient identifications, Koszul tower transitions and completion reflector are
   natural; site-derived-tensor descent and the fraction rule extend this to all maps.
3. Compose that comparison with the tensor of the two Weil isomorphisms. Its inverse
   is the tensor of the inverses followed by the inverse comparison. This is precisely
   wfTensorFrobenius, with no extra cocycle datum.
4. For commuting morphisms u,v, naturality gives
   T(u,v) theta = T(u phi,v phi) mu = T(phi Pu,phi Pv) mu = theta P(T(u,v)).
   Hence tensor defines W. Identities and compositions are inherited from the ambient
   bifunctor; equality of Weil maps is equality of the underlying arrows.
5. K-flat fixed tensor is exact, including shifts and connecting maps; Koszul completion
   is exact by lem-sfb-ringed-complete-triangulated. Uniform-complete triangulated
   closure restricts this exactness integrally. Scalar-localization triangulation
   describes every rational distinguished triangle as an isomorphic localized integral
   triangle, so the fraction rule and localized shift comparisons give exactness of T
   in both variables. No triangulation of the fixed-pair category is used.

The two Fact instances below are supplied by the recorded geometric-fiber theorem;
they add no hypotheses. LocalizedTStructure supplies precisely the induced shift and
isomorphic-image triangles on this same raw category. HEq records the literal formulas
when the equal carrier objects have different elaborated dependent types. -/
theorem wf_tensor_weil :
    ∃ (T : wfTensorCoefficientCategory D c X₀ E × wfTensorCoefficientCategory D c X₀ E ⥤
        wfTensorCoefficientCategory D c X₀ E)
      (W : WeilD D c X₀ E × WeilD D c X₀ E ⥤ WeilD D c X₀ E),
      ((wfTensorCoefficientInclusion D c X₀ E).prod
        (wfTensorCoefficientInclusion D c X₀ E)) ⋙ wfTensor D c X₀ E =
          T ⋙ wfTensorCoefficientInclusion D c X₀ E ∧
      (∀ K L : WeilD D c X₀ E,
        (W.obj (K, L)).carrier = T.obj (K.carrier, L.carrier) ∧
        HEq (wfWeilStructure D c X₀ E (W.obj (K, L))) (wfTensorFrobenius D c X₀ E K L)) ∧
      (∀ (K K' L L' : WeilD D c X₀ E) (f : K ⟶ K') (g : L ⟶ L'),
        HEq (W.map (Prod.mkHom f g)).hom.f (T.map (Prod.mkHom f.hom.f g.hom.f))) ∧
      (fun [hDim : Fact (∃ n : ℕ, topologicalKrullDim (D.geometricFiber X₀).left ≤ n)]
        [hInv : Fact (∀ t : (D.geometricFiber X₀).left,
          IsUnit (c.l : (D.geometricFiber X₀).left.presheaf.stalk t))] ↦
        ∀ L : wfTensorCoefficientCategory D c X₀ E,
          (∃ s : ((Functor.curry.obj T).obj L).CommShift ℤ,
            (fun [sInst : ((Functor.curry.obj T).obj L).CommShift ℤ] ↦
              ((Functor.curry.obj T).obj L).IsTriangulated) (sInst := s)) ∧
          (∃ s : ((Functor.curry.obj T).flip.obj L).CommShift ℤ,
            (fun [sInst : ((Functor.curry.obj T).flip.obj L).CommShift ℤ] ↦
              ((Functor.curry.obj T).flip.obj L).IsTriangulated) (sInst := s)))
        (hDim := ⟨(weilGeometricFiber_coefficientHypotheses D c X₀).2.1⟩)
        (hInv := ⟨(weilGeometricFiber_coefficientHypotheses D c X₀).2.2⟩) := by
  sorry

end WeilConjectures
