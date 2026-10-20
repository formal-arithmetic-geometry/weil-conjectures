/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.InternalHomDualTorAmplitude

/-!
# Locally constant perfect condensed-coefficient complexes

Source: blueprint main-20261015, sec-six-functors-basics/
sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-internal-hom.md, coefficient-model convention
(blueprint: def-sfb-locally-constant-perfect-complex).

Finite projective scalar models are represented by the existing finite-free retracts on the
condensed point. Their maps, including differentials, are matrices over the scalar ring Λ(*).
This is stronger than being perfect over the ringed site: the model is chosen on the point.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Pro-etale locally, a bounded complex of finite projective scalar modules, realized by
point pullback. The finite-projective condensed module and termwise realization are the
existing definitions in `InternalHomDualTorAmplitude`; all differentials are chosen on the
point before pullback. Bounds may depend on the cover member.
Source: blueprint internal-Hom stability statement, locally constant perfect convention
(blueprint: def-sfb-locally-constant-perfect-complex). -/
def IsLocallyConstantPerfectComplex
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (S : Scheme.{u})
    (P : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))) : Prop :=
  ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S, ∀ i : 𝒰.I₀,
    ∃ F : CochainComplex (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) ℤ,
      (∃ c d : ℤ, ∀ n : ℤ, n < c ∨ d < n → IsZero (F.X n)) ∧
      (∀ n : ℤ, FiniteProjectiveCondensedModule (Mon.mk Λ) (F.X n)) ∧
      ∃ hG : ((upperStarFromPoint (𝒰.X i)).mapMod Λ).PreservesZeroMorphisms,
        Nonempty (((CondensedRing.upperStar Λ (𝒰.f i)).mapDerivedCategory).obj P ≅
          DerivedCategory.Q.obj (scalarExtensionComplex
            (Λ := Mon.mk Λ) (U := 𝒰.X i)
            ((upperStarFromPoint (𝒰.X i)).mapMod Λ) hG F))

end AlgebraicGeometry.ProEtale
