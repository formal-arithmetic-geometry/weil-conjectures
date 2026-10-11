/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage

/-! # The dualizing complex of a smooth proper curve

Source: Stacks Project, Tag 0BRT, Lemma 48.15.7, specialized to a field and relative
 dimension one (blueprint: lem-sc-smooth-proper-curve-dualizing).
-/

@[expose] public section

universe u wC wk

open CategoryTheory

namespace AlgebraicGeometry

/-- The right adjoint of `Rg_*` on quasi-coherent complexes takes `𝒪_k` to `Ω¹_{C/k}[1]`.
Source: Stacks Project, Tag 0BRT, Lemma 48.15.7, relative dimension one
(blueprint: lem-sc-smooth-proper-curve-dualizing).

`R` is the restriction of the recorded derived direct image: `comparison` identifies its
composite with the full-subcategory inclusion with that derived direct image. `a` is its
right adjoint. `O` is the structure sheaf in degree zero, represented in `D_QCoh`; `hO`
identifies its underlying derived object with the standard single-complex construction.

Proof: apply `lem-sc-smooth-proper-relative-dualizing-general` with `S = Spec k`, `X = C`,
`f = g`, and `d = 1`. The spectrum of a field is Noetherian, and `g` has exactly the smoothness,
properness and pure relative dimension hypotheses required there. The differential sheaf
of that node identifies with `g.relativeDifferentials`, the sheaf recorded by
`def-sc-kahler-differentials`. Finally the first exterior power is the module itself and the
shift by `d` is the shift by one. Transport across `comparison` and `hO` gives the displayed
isomorphism for the supplied representatives and right adjoint. -/
theorem smoothProperCurve_dualizing
    (k : Type u) [Field k] (C : Scheme.{u}) (g : C ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 g] [IsProper g]
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings C.toRingedSpace))]
    [HasDerivedCategory.{wk}
      (SheafOfModules.{u} (moduleRings (Spec (.of k)).toRingedSpace))]
    (R : schemeDerivedQCohCategory C ⥤ schemeDerivedQCohCategory (Spec (.of k)))
    (comparison : R ⋙ (schemeDerivedQCohProperty (Spec (.of k))).ι ≅
      (schemeDerivedQCohProperty C).ι ⋙ schemeDerivedDirectImage g)
    (a : schemeDerivedQCohCategory (Spec (.of k)) ⥤ schemeDerivedQCohCategory C)
    (adj : R ⊣ a) (O : schemeDerivedQCohCategory (Spec (.of k)))
    (hO : O.obj ≅
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of k)).toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings (Spec (.of k)).toRingedSpace))) :
    Nonempty ((a.obj O).obj ≅
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings C.toRingedSpace)) 0).obj
          g.relativeDifferentials)⟦(1 : ℤ)⟧) := by
  sorry

end AlgebraicGeometry
