/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.AlgebraicGeometry.DerivedDirectImageUniformTruncationBound

/-! # Boundedness below of finite twisted inverse image

Source: Stacks Project, Duality for Schemes, Tag 0A9I (finite case, Tag 0AX2)
(blueprint: lem-sc-finite-twisted-inverse-bounded-below).
-/

@[expose] public section

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry

/-- The right adjoint of derived direct image on quasi-coherent complexes preserves
boundedness below for a finite morphism of Noetherian schemes. `comparison` identifies `R`
with the restriction of the shared derived direct image; `adj` specifies its right adjoint.
Quasi-coherence of the image is included in the codomain of `a`.

Source: Stacks Project, Tag 0A9I, specialized to the finite case of Tag 0AX2
(blueprint: lem-sc-finite-twisted-inverse-bounded-below).
Proof:
1. Finite morphisms of Noetherian schemes are quasi-compact and quasi-separated, with
quasi-compact target. Apply lem-pc-derived-direct-image-uniform-truncation-bound to shifted
complexes to obtain a uniform integer N with Rf_* D^{≤r} contained in D^{≤r+N}.
2. Choose c with H^i(K) = 0 for i ≤ c. Set A = τ_{≤c-N} a(K). The bound gives
Rf_* A in D^{≤c}, while K is in D^{≥c+1}. Adjunction identifies Hom(A,a(K)) with
Hom(Rf_* A,K), which vanishes by lem-pc-derived-tstructure-orthogonality.
3. The truncation map A → a(K) is consequently zero, but induces an isomorphism on
cohomology in degrees ≤c-N. These cohomology sheaves vanish, proving boundedness below.
The codomain of the right adjoint already ensures quasi-coherent cohomology. -/
theorem finiteTwistedInverse_boundedBelow
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsNoetherian X] [IsNoetherian Y]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (R : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory Y)
    (comparison : R ⋙ (schemeDerivedQCohProperty Y).ι ≅
      (schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (adj : R ⊣ a) (K : schemeDerivedQCohCategory Y)
    (hK : ∃ n : ℤ, K.obj.IsGE n) :
    ∃ n : ℤ, (a.obj K).obj.IsGE n := by
  sorry

end AlgebraicGeometry
