/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.QlbarCoefficient.CommonStage.Linear
public import WeilConjectures.CategoryTheory.DerivedCategory.QlbarCoefficient.FinExt
public import WeilConjectures.CategoryTheory.DerivedCategory.QlbarCoefficient.FiniteField

/-!
# The `ℚ̄_ℓ`-coefficient bounded constructible derived category

This file assembles the pieces into the definition of `Dᵇ_c(Y, ℚ̄_ℓ)`.

The coefficient passage is

`{Dᵇ_c(Y, 𝒪_E/ℓⁿ)}ₙ ⇝ Dᵇ_c(Y, 𝒪_E) ⇝ Dᵇ_c(Y, E) ⇝ Dᵇ_c(Y, ℚ̄_ℓ)`,

and all four stages are now present:

- the finite reductions are the cones of `ℓⁿ • 𝟙` in `D(Y_proét, 𝒪_E)`;
- `Dᵇ_c(Y, 𝒪_E)` is `AlgebraicGeometry.Scheme.ProEt.AdicDerivedCategory`: the derived
  `ℓ`-complete objects whose reductions are constructible with an amplitude independent of
  `n`;
- `Dᵇ_c(Y, E)` is `AlgebraicGeometry.Scheme.ProEt.FiniteFieldDerivedCategory`, the
  rationalization obtained by inverting `ℓ`;
- `Dᵇ_c(Y, ℚ̄_ℓ)` is the common-stage category of the family `E ↦ Dᵇ_c(Y, E)` indexed by
  the directed poset `FinExt ℓ` of finite subextensions.

## What is and is not constructed here

The last step needs, besides the finite stages themselves, the **scalar extension**
functors `T_{F/E} : Dᵇ_c(Y, E) ⥤ Dᵇ_c(Y, F)` together with their unit and associativity
comparisons — that is, a `CategoryTheory.TransitionSystem` on `FinExt ℓ`. That datum is
`ScalarExtensionSystem`; constructing it is left to later work. Note that `𝒪_F` is finite
free over `𝒪_E`, so `- ⊗_{𝒪_E} 𝒪_F` is *exact* and no derived tensor product is needed:
the expected route is `sheafCompose` of `ModuleCat.extendScalars` followed by
`Functor.mapDerivedCategory`.

Given such a system, `QlbarDerivedCategory` is a category by
`CategoryTheory.TransitionSystem.CommonStage.category`, using only the directedness of
`FinExt ℓ`. The structure on it — additive, `ℚ̄_ℓ`-linear, triangulated — is supplied by
the other files of this folder once the corresponding compatibilities of the scalar
extension are known, and is not set up here.

## Main definitions

- `AlgebraicGeometry.Scheme.ProEt.finiteStage`: the coefficient category `Dᵇ_c(Y, E)` at a
  finite stage `E`.
- `AlgebraicGeometry.Scheme.ProEt.ScalarExtensionSystem`: the scalar-extension datum.
- `AlgebraicGeometry.Scheme.ProEt.QlbarDerivedCategory`: the category `Dᵇ_c(Y, ℚ̄_ℓ)`.
-/

@[expose] public section

universe u

open CategoryTheory

noncomputable section

namespace AlgebraicGeometry.Scheme.ProEt

variable (Y : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The coefficient category at the finite stage `E`: the `E`-coefficient bounded
constructible derived category `Dᵇ_c(Y, E)`, obtained from the `𝒪_E`-adic one by inverting
`ℓ`. -/
abbrev finiteStage (E : FinExt ℓ) : Type _ :=
  FiniteFieldDerivedCategory Y (FinExt.integersULift.{u} E)
    ((ℓ : ℕ) : FinExt.integersULift.{u} E)

/-- The scalar-extension datum for the `ℓ`-adic coefficient formalism: for every inclusion
`E ⊆ F` of finite subextensions an exact functor `Dᵇ_c(Y, E) ⥤ Dᵇ_c(Y, F)`, together with
the unit and associativity comparisons and their coherences.

Constructing this is left to later work; see the module docstring. -/
abbrev ScalarExtensionSystem : Type _ := TransitionSystem (finiteStage Y ℓ)

/-- The **`ℚ̄_ℓ`-coefficient bounded constructible derived category** `Dᵇ_c(Y, ℚ̄_ℓ)`:
objects are pairs `(E, K)` with `K` an object of `Dᵇ_c(Y, E)` for a finite subextension
`E`, and morphisms are represented after passage to a common finite coefficient field,

`Hom((E, K), (F, L)) = colim_{M ⊇ E, F} Hom_{Dᵇ_c(Y, M)} (T_{M/E} K, T_{M/F} L)`.

The colimit is filtered because `FinExt ℓ` is directed, which is the only property of the
index used. -/
abbrev QlbarDerivedCategory (S : ScalarExtensionSystem Y ℓ) : Type _ :=
  TransitionSystem.CommonStage S

instance (S : ScalarExtensionSystem Y ℓ) : Category (QlbarDerivedCategory Y ℓ S) :=
  inferInstanceAs <| Category (TransitionSystem.CommonStage S)

/-- The canonical functor from a finite stage: `Dᵇ_c(Y, E) ⥤ Dᵇ_c(Y, ℚ̄_ℓ)`. The stage `E`
records a finite field of definition, not extra structure: by
`CategoryTheory.TransitionSystem.CommonStage.stageIso`, `(E, K)` and
`(F, T_{F/E} K)` are canonically isomorphic. -/
abbrev fromFiniteStage (S : ScalarExtensionSystem Y ℓ) (E : FinExt ℓ) :
    finiteStage Y ℓ E ⥤ QlbarDerivedCategory Y ℓ S :=
  TransitionSystem.CommonStage.stageFunctor S E

/-- The scalars of the `ℚ̄_ℓ`-coefficient category: at the stage `E` they are the subring
`E ⊆ ℚ̄_ℓ`, and `Dᵇ_c(Y, E)` is `E`-linear because `E = 𝒪_E[1/ℓ]`.

The two arithmetic inputs are proved: monotonicity of `E ↦ E` is `FinExt.subring_mono`,
and the fact that every element of `ℚ̄_ℓ` is already defined at some finite stage is
`FinExt.exists_mem_subring`. What is assumed is the identification `𝒪_E[1/ℓ] = E`, in the
form of the localization instances. -/
@[instance_reducible]
def scalarSystem (S : ScalarExtensionSystem Y ℓ)
    [∀ E : FinExt ℓ, Algebra (FinExt.integersULift.{u} E) (FinExt.subring ℓ E)]
    [∀ E : FinExt ℓ, IsLocalization
      (Submonoid.powers ((ℓ : ℕ) : FinExt.integersULift.{u} E)) (FinExt.subring ℓ E)] :
    TransitionSystem.ScalarSystem S (AlgebraicClosure ℚ_[ℓ]) where
  k := FinExt.subring ℓ
  mono := FinExt.subring_mono
  exists_mem := FinExt.exists_mem_subring
  linear _ := inferInstance

end AlgebraicGeometry.Scheme.ProEt
