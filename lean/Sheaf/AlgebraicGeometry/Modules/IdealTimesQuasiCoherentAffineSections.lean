/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Products of quasi-coherent ideals and modules

Source: Stacks Project, Schemes, Tags 01I8 and 01IC; Modules, Tags 01CE and 01AH;
Cohomology of Schemes, Tag 087X
(blueprint: lem-weil-pbc-ideal-times-quasi-coherent-affine-sections).

A quasi-coherent ideal is a `Scheme.IdealSheafData`, with module realization and inclusion
`toModules` and `toModulesι`. The product `𝒥𝓕`, its inclusion and the powers `𝒥ⁿ`
(`𝒥ⁿ⁺¹ = 𝒥 · 𝒥ⁿ`) are the landed `Scheme.idealModuleProduct`, `Scheme.idealModuleProductι`
and `Scheme.idealSheafPower` (lem-weil-pbc-ideal-module-product-stalk). Restriction to an
open `V` is `Scheme.Modules.restrictFunctor V.ι` on modules and `IdealSheafData.comap V.ι`
on ideals. Subsheaves of `𝓕|_V` are compared as the subobjects `Subobject.mk (image.ι _)`
of their inclusions, as in lem-weil-pbc-affine-pushforward-ideal-product.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Products and quotients by quasi-coherent ideals, including affine sections and
restriction to arbitrary opens. Let `𝒥` be a quasi-coherent ideal and `𝓕` a quasi-coherent
module on `X`. Then `𝒥𝓕`, `𝓕/𝒥𝓕` and every `𝒥ⁿ` (`n ≥ 1`) are quasi-coherent; on every
affine open `U`, `(𝒥𝓕)(U) = 𝒥(U)𝓕(U)`, `𝓕(U) → (𝓕/𝒥𝓕)(U)` is surjective with kernel
`𝒥(U)𝓕(U)`, and `𝒥ⁿ(U) = 𝒥(U)ⁿ`; for every open `V`, `(𝒥𝓕)|_V = (𝒥|_V)(𝓕|_V)` as
subobjects of `𝓕|_V`. Source: Stacks, Tags 01I8, 01IC, 01CE, 01AH and 087X
(blueprint: lem-weil-pbc-ideal-times-quasi-coherent-affine-sections).

Proof:
1. On an affine open, the tilde/global-sections comparison identifies the ideal and module
with the tilde sheaves of `I` and `M`. The tensor comparison identifies multiplication
with `I ⊗ M → M`, sending `a ⊗ s` to `a • s` (the nodes
lem-weil-pbc-affine-tilde-gamma-adjunction, lem-weil-pbc-spec-module-tilde-sections and
lem-weil-pbc-quasi-coherent-tensor-product-affine-sections).
2. The image and cokernel calculation (lem-weil-pbc-quasi-coherent-module-cokernel-image)
gives quasi-coherence, the image `I • ⊤`, and surjectivity with precisely that kernel.
3. Apply the same calculation inductively to the ideal and its previous power
(`𝒥ⁿ⁺¹ = 𝒥 · 𝒥ⁿ`, the module being `𝒥ⁿ`). This gives quasi-coherence of every positive
power and sections `I ^ n`; `n = 1` is the original ideal.
4. Restriction to `V` is exact and commutes with the tensor product and the unitor, and the
restricted inclusion of `𝒥` is the inclusion of `𝒥|_V`; so it carries the multiplication of
`𝒥` on `𝓕` to that of `𝒥|_V` on `𝓕|_V` and preserves its image
(lem-weil-pbc-module-restriction-open-immersion-colimits and the image/cokernel node). -/
theorem ideal_times_quasiCoherent_affine_sections {X : Scheme.{u}}
    (J : X.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent] :
    (idealModuleProduct J.toModulesι F).IsQuasicoherent ∧
    (cokernel (idealModuleProductι J.toModulesι F)).IsQuasicoherent ∧
    (∀ n : ℕ, 0 < n → (idealSheafPower J.toModulesι n).1.IsQuasicoherent) ∧
    (∀ U : X.affineOpens,
      Set.range ((idealModuleProductι J.toModulesι F).app U.1) =
        {s | s ∈ J.ideal U • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1))} ∧
      Function.Surjective ((cokernel.π (idealModuleProductι J.toModulesι F)).app U.1) ∧
      (∀ s : Γ(F, U.1),
        (cokernel.π (idealModuleProductι J.toModulesι F)).app U.1 s = 0 ↔
          s ∈ J.ideal U • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1))) ∧
      (∀ n : ℕ, 0 < n →
        Set.range ((idealSheafPower J.toModulesι n).2.app U.1) =
          {a | a ∈ J.ideal U ^ n})) ∧
    (∀ V : X.Opens,
      Subobject.mk (image.ι ((restrictFunctor V.ι).map (idealModuleProductι J.toModulesι F))) =
        Subobject.mk (image.ι (idealModuleProductι (J.comap V.ι).toModulesι
          ((restrictFunctor V.ι).obj F)))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
