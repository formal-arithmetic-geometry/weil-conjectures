/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Sheaf.AlgebraicGeometry.SchemeOrdinaryEvaluationFormula
public import Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom
public import Sheaf.Algebra.Homology.KFlat
import Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison
import Sheaf.AlgebraicGeometry.DerivedTensorSymmetry
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions

/-! # Evaluation with actual models on one scheme site
Source: Stacks Project, Tags 08DJ, 08DM and 08DQ.
(blueprint: lem-pc-kinjective-scheme-evaluation-models).
There is no site equivalence in this statement: Q is the one localization used
by both ordinary models and the canonical tensor-Hom family.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

/-- Compute derived evaluation using ordinary complexes on the same scheme site.
Source: Stacks Project, Tags 08DJ, 08DM and 08DQ, representative calculation.
(blueprint: lem-pc-kinjective-scheme-evaluation-models).

Proof: resolve the degree-zero unit by the fixed functorial K-injective resolution.
Apply hhom to its resolution map: Hom(P,eta_unit) is a quasi-isomorphism. Compose
its inverse localization with the recorded internal-Hom factorization to identify
the ordinary dual with RHom(K,1), including eK. The same factorization computes
Hom(P,F), because F is already K-injective; compose with eK and eN to obtain b.
K-flatness of the ordinary dual makes the localization tensor comparison invertible.
Use symmetry to put that K-flat dual first, apply kFlat_derivedTensor_comparison_natIso,
and restore the order F tensor dual. Compose with eN and the dual comparison to get a.
For the square, replace the tensor inputs by K-flat resolutions. Use the canonical
representative equation of schemeDerivedTensorHomEquiv with the identity of the
derived dual. On a summand F^p tensor dual^q followed by the r-th Hom projection,
uncurrying this identity and applying the right unitor gives the displayed ordinary
unit-action formula if r+q=0 and zero otherwise. This is hf. The coproduct inclusions
and product projections detect equality of the resulting chain maps. Naturality
with the resolution maps then identifies the localized maps; cancel the localized
Hom-resolution isomorphisms. Finally the canonical family's three-variable
naturality transports along eK and eN. No inverse of f, finite freeness or boundedness
is used. The same equations hold for zero complexes and the empty scheme. -/
theorem exists_kInjective_scheme_evaluation_models (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (K N : schemeDerivedCategory Y)
    (P F : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hhom : ∀ (M M' : CochainComplex
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) (t : M ⟶ M'),
      QuasiIso t → QuasiIso (((homComplexFunctor (R := Y.sheaf)).obj (op P)).map t))
    (hdual : (homComplex (R := Y.sheaf) P
      ((HomologicalComplex.single _ (.up ℤ) 0).obj
        (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace))))).IsKFlat)
    (eK : DerivedCategory.Q.obj P ≅ K) (eN : DerivedCategory.Q.obj F ≅ N)
    (f : pullbackTensorTotal Y F
        (homComplex (R := Y.sheaf) P
          ((HomologicalComplex.single _ (.up ℤ) 0).obj
            (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace))))) ⟶
      homComplex (R := Y.sheaf) P F)
    (hf : IsSchemeOrdinaryEvaluation Y P F f) [F.IsKInjective] :
    let H := derivedInternalHom (Opens.grothendieckTopology Y.toRingedSpace) Y.sheaf
    let D := H.obj (op K, 𝟙_ (schemeDerivedCategory Y))
    let g := ((schemeDerivedTensorHomEquiv Y) (N ⊗ D) K N).symm
      ((α_ N D K).hom ≫ N ◁
        ((schemeDerivedTensorHomEquiv Y) D K
          (𝟙_ (schemeDerivedCategory Y)) (𝟙 D)) ≫ (ρ_ N).hom)
    ∃ a : N ⊗ D ≅ DerivedCategory.Q.obj (pullbackTensorTotal Y F
          (homComplex (R := Y.sheaf) P
            ((HomologicalComplex.single _ (.up ℤ) 0).obj
              (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))))),
      ∃ b : H.obj (op K, N) ≅ DerivedCategory.Q.obj (homComplex (R := Y.sheaf) P F),
        g ≫ b.hom = a.hom ≫ DerivedCategory.Q.map f := by sorry

end AlgebraicGeometry
