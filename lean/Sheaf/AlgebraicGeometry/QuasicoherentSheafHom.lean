/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-! # Quasi-coherence of sheaf Hom from a finitely presented module

Source: Stacks Project, Schemes, Section 01LA, item (10), using Modules, Lemma 01CQ
(blueprint: lem-weil-pbc-sheaf-hom-finite-presentation-quasi-coherent).
-/

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- On a scheme `X`, sheaf Hom from a finitely presented module `G` into a quasi-coherent
module `F` is quasi-coherent. Its sections over `W` are the `O_W`-linear maps
`G|_W ⟶ F|_W`, as in `SheafOfModules.homObj`.
Source: Stacks Project, Schemes, Section 01LA, item (10), and Modules, Lemma 01CQ
(blueprint: lem-weil-pbc-sheaf-hom-finite-presentation-quasi-coherent).

Proof:
1. At each point choose a finite free cokernel presentation `O_U^m → O_U^n → G|_U`
   using `def-weil-pbc-module-finite-type-presentation`. Restriction preserves that
   cokernel and quasi-coherence of `F`, by
   `lem-weil-pbc-module-restriction-open-immersion-colimits`.
2. Finite direct sums of `F|_U` are quasi-coherent by
   `lem-weil-pbc-quasi-coherent-module-direct-sum`. For rank zero, the zero module is
   the kernel of the identity of `F|_U`, using `lem-weil-pbc-quasi-coherent-module-kernel`.
3. Write the presentation map as a matrix `(a_ik)` of sections of `O_U`. The induced
   map `(F|_U)^n → (F|_U)^m` sends `(s_i)` to `(∑ i, a_ik s_i)_k`. On every open
   `W ⊆ U`, a map from `O_W^n` is determined by the images of the basis sections.
   It factors uniquely through `G|_W` exactly when that tuple is in this matrix
   map's kernel. The identification commutes with restriction, so `def-pur-sheaf-hom`
   identifies the Hom sheaf on `U` with this kernel. The kernel is quasi-coherent by
   `lem-weil-pbc-quasi-coherent-module-kernel`.
4. Every point has such a neighbourhood. Its affine refinements give the required
   local quasi-coherence of the Hom sheaf by `pqf-def-coherent`. -/
theorem isQuasicoherent_homObj_of_isFinitePresentation (X : Scheme.{u}) (G F : X.Modules)
    [G.IsFinitePresentation] [F.IsQuasicoherent] :
    (SheafOfModules.homObj (R := X.sheaf) G F).IsQuasicoherent := by
  sorry

end AlgebraicGeometry.Scheme.Modules
