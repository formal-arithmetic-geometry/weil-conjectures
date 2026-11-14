/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.AlgebraicGeometry.AffineScheme

import WeilConjectures.AlgebraicGeometry.AffineBasisAcyclicSectionsPreservesHomology
import WeilConjectures.AlgebraicGeometry.AffineBasisKInjectiveSectionsPreservesHomology
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Epi part of affine-basis section resolution comparison

## References

* Stacks Project, Tags 08C2 and 071B
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option linter.unusedVariables false in
/-- The section resolution map induces a epimorphism on homology in each degree.
(Stacks, Tags 08C2 and 071B). -/
theorem affineBasisSections_resolution_homology_epi
    (X : Scheme.{u}) (V : X.Opens) (hV : IsAffineOpen V)
    (F J : CochainComplex X.Modules ℤ) [J.IsKInjective]
    (i : F ⟶ J) [QuasiIso i]
    (hterms : ∀ (W : X.Opens), IsAffineOpen W → W ≤ V → ∀ (n : ℤ) (q : ℕ),
      Subsingleton (((F.X n).restrict W.ι).H (q + 1)))
    (hcokernels : ∀ (W : X.Opens), IsAffineOpen W → W ≤ V → ∀ (n : ℤ) (q : ℕ),
      Subsingleton (((cokernel (F.d (n - 1) n)).restrict W.ι).H (q + 1)))
    (hhomology : ∀ (W : X.Opens), IsAffineOpen W → W ≤ V → ∀ (n : ℤ) (q : ℕ),
      Subsingleton (((F.homology n).restrict W.ι).H (q + 1))) (n : ℤ) :
    let S := SheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace) (op V)
    letI : S.Additive := inferInstanceAs
      ((SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
        PresheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace).obj (op V)).Additive)
    Epi (HomologicalComplex.homologyMap
      ((S.mapHomologicalComplex (ComplexShape.up ℤ)).map i) n) := by
  clear hterms
  dsimp
  let S := SheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace) (op V)
  let : S.Additive := inferInstanceAs
    ((SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
      PresheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace).obj (op V)).Additive)
  have hJ : ∀ (W : X.Opens), IsAffineOpen W → W ≤ V → ∀ (r : ℤ) (q : ℕ),
      Subsingleton (((J.homology r).restrict W.ι).H (q + 1)) := by
    intro W hW hWV r q
    let := hhomology W hW hWV r q
    let e := (Scheme.Modules.restrictFunctor W.ι).mapIso
      (asIso (HomologicalComplex.homologyMap i r))
    exact (Scheme.Modules.H.mapLinearEquiv e (q + 1)).symm.injective.subsingleton
  let := affineBasisAcyclicSections_preservesLeftHomology X V hV F
    hcokernels hhomology n
  let := affineBasisKInjectiveSections_preservesLeftHomology X V hV J hJ n
  let φ := (HomologicalComplex.shortComplexFunctor X.Modules (.up ℤ) n).map i
  change Epi (ShortComplex.homologyMap (S.mapShortComplex.map φ))
  have : IsIso (ShortComplex.homologyMap φ) :=
    inferInstanceAs (IsIso (HomologicalComplex.homologyMap i n))
  have h := ShortComplex.mapHomologyIso_hom_naturality φ S
  have : IsIso (ShortComplex.homologyMap (S.mapShortComplex.map φ) ≫
      ((J.sc n).mapHomologyIso S).hom) := by
    rw [h]
    infer_instance
  have : IsIso (ShortComplex.homologyMap (S.mapShortComplex.map φ)) :=
    IsIso.of_isIso_comp_right _ ((J.sc n).mapHomologyIso S).hom
  infer_instance

end AlgebraicGeometry
