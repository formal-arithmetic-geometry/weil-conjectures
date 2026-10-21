/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
public import Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso

import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# The scalar-cone total-tensor model and its descent

Source: `WeilConjectures/CategoryTheory/DerivedCategory/Monoidal/TensorMappingCone.lean`,
`kFlat_scalarCone`, `tensorScalarConeIso'`, `tensorScalarConeIso`, and their naturality;
blueprint main-20261015, `det-pe-derived-nakayama-resolution`, resolution paragraph
(blueprint: lem-pe-scalar-cone-tensor-model).

The scalar cone and tensor products are the existing upstream constructions.
The K-flat predicate is the recorded two-sided binary-total-tensor predicate.
-/

@[expose] public section

universe u v r

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [HasDerivedCategory.{v} A] [MonoidalCategory A] [MonoidalClosed A]
  [MonoidalPreadditive A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
  {B : Type r} [CommRing B] [Linear B A] [MonoidalLinear B A]

/-- The cochain scalar-cone functor: on a chain map it uses the diagonal square.
Source: `TensorMappingCone.lean`, `tensorScalarConeIso'_hom_naturality`, and blueprint
`det-pe-derived-nakayama-resolution`, naturality in the complex
(blueprint: lem-pe-scalar-cone-tensor-model).

Scalar linearity gives the commutative square. The functor laws are the existing
`mappingCone.map_id` and `mappingCone.map_comp` identities. -/
noncomputable def scalarConeCochainFunctor (b : B) : CochainComplex A ℤ ⥤ CochainComplex A ℤ where
  obj C := CochainComplex.mappingCone (b • 𝟙 C)
  map {C D} f := CochainComplex.mappingCone.map (b • 𝟙 C) (b • 𝟙 D) f f (by simp)
  map_id C := CochainComplex.mappingCone.map_id (b • 𝟙 C)
  map_comp {C D E} f g :=
    CochainComplex.mappingCone.map_comp (b • 𝟙 C) (b • 𝟙 D) (b • 𝟙 E)
      f f (by simp) g g (by simp)

/-- The scalar cone is two-sided K-flat; its natural total-tensor model, followed by
localization's canonical tensor comparison, descends compatibly to the derived category.
Source: `TensorMappingCone.lean`, lines 55–158, and blueprint main-20261015,
`det-pe-derived-nakayama-resolution`, the resolution and natural cone description
(blueprint: lem-pe-scalar-cone-tensor-model).

Proof plan, following the node's six steps:
1. In degree n, total tensoring with the scalar cone has two summands. The unitors
identify them with C^n and C^(n+1). On the right tensor multiply the second summand
by (-1)^(n+1); on the left tensor use the identity. The differential matrices then
become the cone matrix. This is the upstream `tensorScalarConeIso'` construction.
2. Scalar linearity makes the square of each chain map commute. Its diagonal cone
map commutes with these degreewise identifications, giving a natural isomorphism.
3. The degreewise split sequence C → Cone(b_C) → C[1] is natural in C. Apply
`lem-weil-pbc-complex-ses-homology-long-exact` and its naturality node. For a
quasi-isomorphism, the four outer maps in each five-term cohomology diagram are
isomorphisms; `lem-weil-pbc-five-lemma` makes the middle map an isomorphism.
4. Conjugate both total tensor maps by the isomorphisms of steps 1–2. Step 3 proves
that both preserve quasi-isomorphisms, exactly `IsKFlatForTotalTensor`.
5. `lem-sfb-derived-monoidal` computes the canonical lax tensor comparison using
the identity K-flat resolution of the scalar cone. It is invertible. Composing
with Q applied to step 1 gives θ, naturally in C, with the displayed formula.
6. Step 3 shows that the localized cone functor inverts quasi-isomorphisms.
`lem-weil-pbc-localization-universal-property` descends it to F and lifts the
comparison with derived right tensoring to δ. The last equality records that
this descent agrees with θ on every cochain representative. -/
theorem scalarCone_totalTensor_model (b : B) :
    CochainComplex.IsKFlatForTotalTensor (scalarCone (A := A) b) ∧
    ∃ (Φ : tensorRight (scalarCone (A := A) b) ≅ scalarConeCochainFunctor (A := A) b)
      (θ : Q ⋙ tensorRight (Q.obj (scalarCone (A := A) b)) ≅
        scalarConeCochainFunctor (A := A) b ⋙ Q),
      (∀ C : CochainComplex A ℤ,
        θ.hom.app C = Functor.LaxMonoidal.μ Q C (scalarCone b) ≫ Q.map (Φ.hom.app C)) ∧
      (HomologicalComplex.quasiIso A (.up ℤ)).IsInvertedBy
        (scalarConeCochainFunctor (A := A) b ⋙ Q) ∧
      ∃ (F : DerivedCategory A ⥤ DerivedCategory A)
        (η : Q ⋙ F ≅ scalarConeCochainFunctor (A := A) b ⋙ Q)
        (δ : tensorRight (Q.obj (scalarCone (A := A) b)) ≅ F),
        ∀ C : CochainComplex A ℤ,
          δ.hom.app (Q.obj C) ≫ η.hom.app C = θ.hom.app C := by
  sorry

end DerivedCategory
