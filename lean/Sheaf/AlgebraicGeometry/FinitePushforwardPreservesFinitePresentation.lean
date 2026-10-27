/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q146
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Sheaf.RingTheory.FiniteExtensionModuleFinitePresentation

/-!
# Finite pushforward preserves finite presentation

Source: Stacks Project, Descent, Tag 05B4, lemma-finite-finitely-presented-module,
forward implication (blueprint: lem-trf-finite-pushforward-preserves-finite-presentation).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite morphism locally of finite presentation sends a finitely presented
quasi-coherent module to a finitely presented module by Zariski direct image.
Source: Stacks Project, Descent, Tag 05B4, lemma-finite-finitely-presented-module,
forward implication (blueprint: lem-trf-finite-pushforward-preserves-finite-presentation).

Here `pushforward f` is the canonical direct image: its sections on `V` are
`Γ(F, f ⁻¹ᵁ V)`, with scalars restricted along `f.app V`. Since a finite morphism
is quasi-compact and quasi-separated, local finite presentation is equivalent
to the finite-presentation assumption of Tag 05B4.

Proof:
1. Finiteness makes `f` affine (def-weil-finite-integral-morphism), hence quasi-compact
   and quasi-separated (lem-weil-pbc-affine-morphism-permanence). Consequently
   `f_*F` is quasi-coherent (pqf-lem-pushforward-qcoh).
2. For any affine open `V` of `Y`, its inverse image `U` is affine, and
   `B = Γ(X,U)` is finite over `A = Γ(Y,V)` (def-weil-finite-integral-morphism).
   It is a finitely presented `A`-algebra by local finite presentation
   (lem-weil-pbc-lfp-affine-opens-finite-presentation). Restrict the local finite
   presentations of `F` to `U` (def-weil-pbc-module-finite-type-presentation).
   The affine criterion (lem-weil-pbc-quasi-coherent-finite-type-affine) then
   shows that `M = Γ(F,U)` is finitely presented over `B`.
3. The finite-extension theorem (lem-trf-finite-extension-module-finite-presentation)
   makes `M` finitely presented over `A`. This is exactly the module of sections
   of `f_*F` on `V`, including its scalar action through `f.app V`.
4. By the affine criterion (lem-weil-pbc-quasi-coherent-finite-type-affine), the
   quasi-coherent module `f_*F` has finite presentation on every affine open.
   These opens cover `Y`; their local presentations are local presentations on
   `Y` (def-weil-pbc-module-finite-type-presentation). -/
theorem isFinitePresentation_pushforward_of_isFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] :
    ((pushforward f).obj F).IsFinitePresentation := by
  sorry

end AlgebraicGeometry.Scheme.Modules
