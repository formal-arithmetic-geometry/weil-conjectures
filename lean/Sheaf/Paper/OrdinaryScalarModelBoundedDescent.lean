/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B9
-/
module

public import Sheaf.Paper.FiniteConstantModelResolution
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Ordinary scalar models on the pro-etale site -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [∀ T : Scheme.{u}, (FiniteConstantModel.modelFunctor A T).Additive]

/-- Bounded ordinary scalar models with finitely presented cohomology descend to Dbc.
Source: blueprint internal-Hom stability proof, paragraph 3, perfect-factor membership;
Stacks 093J, 00VH, 00VM (blueprint: lem-sfb-ordinary-scalar-model-bounded-descent).

Proof: a Noetherian quasi-compact scheme is quasi-separated. Take a finite affine
open cover and apply finite_affine_proetale_refinement to the specified cover.
Restrict each given model to the resulting finite family, using coefficient
localization and the composition isomorphisms for inverse image. The same scalar
complexes still give the models on these charts. Evaluation of continuous functions
on the one-point profinite set identifies the scalar ring with A (up to its
specified universe lift). Under the resulting equivalence of ordinary modules
with internal scalar modules, finite presentation is precisely a finite matrix
presentation. Constant sheafification followed by extension of scalars is the
functor finiteConstantScalarExtension, naturally in both modules and maps.
These equivalences preserve homology, finite presentation and zero terms.
Choose the minimum of the finitely many lower bounds and the maximum of their
upper bounds, enlarged to include zero; this also handles an empty finite cover.
The exact realization hypotheses and the scalar cohomology presentations now
satisfy localModel_cohomology_descent. Its Dbc conclusion transports back to Q.
For the empty scheme the sheaf category is zero and the interval [0,0] suffices.
No projectivity of the scalar cohomology, uniform original cover bound, or
completeness restriction is assumed. -/
theorem ordinaryScalarModel_bounded_descent
    (S : Scheme.{u}) [CompactSpace S] [IsLocallyNoetherian S]
    (Q : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousCoefficientRingObj A) S)))
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S)
    (F : 𝒰.I₀ → CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (hexact : ∀ T : Scheme.{u},
      PreservesFiniteLimits (FiniteConstantModel.modelFunctor A T) ∧
        PreservesFiniteColimits (FiniteConstantModel.modelFunctor A T))
    (hbounded : ∀ i : 𝒰.I₀, ∃ a b : ℤ, ∀ q : ℤ,
      q < a ∨ b < q → IsZero ((F i).X q))
    (hmodel : ∀ i : 𝒰.I₀, Nonempty
      (((CondensedRing.upperStar (Profinite.continuousCoefficientRingObj A)
        (𝒰.f i)).mapDerivedCategory).obj Q ≅ DerivedCategory.Q.obj
          (((FiniteConstantModel.modelFunctor A (𝒰.X i)).mapHomologicalComplex
            (.up ℤ)).obj (F i))))
    (hfp : ∀ (i : 𝒰.I₀) (q : ℤ), Module.FinitePresentation A ((F i).homology q)) :
    constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj A) S Q := by
  sorry

end AlgebraicGeometry.ProEtale
