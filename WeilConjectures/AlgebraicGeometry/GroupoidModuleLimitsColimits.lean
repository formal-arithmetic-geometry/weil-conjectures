/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeGroupoidModule
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.StalkFlatTensorPullbackKernels
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.RingTheory.RingHom.Flat

/-!
# Underlying limits and colimits of flat groupoid modules

Source: Stacks Project, Groupoids, Tags 077R and 077S
(blueprint: lem-sfb-groupoid-module-limits-colimits).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Flat groupoid modules form an abelian category, with finite limits and small
colimits computed on the underlying module sheaves.
Source: Stacks Project, Groupoids, Tags 077R and 077S
(blueprint: lem-sfb-groupoid-module-limits-colimits).

Proof:
1. In the ambient Grothendieck abelian module category, form a diagram's colimit as
   the cokernel of the difference map from the sum indexed by arrows to the sum
   indexed by objects. Quasi-coherent sums and cokernels show it is quasi-coherent
   (lem-pc-scheme-modules-grothendieck-abelian,
   lem-weil-pbc-quasi-coherent-module-cokernel-image,
   lem-pc-quasicoherent-module-coproducts). The same formula gives zero for an empty diagram.
2. Pullbacks preserve quasi-coherence and, by their tensor adjunction, all colimits;
   they are additive. Flat pullbacks preserve kernels by the stalkwise flat tensor
   theorem. The projections from composable arrows are flat by base change, and
   their composite to U is flat by composition of flat stalk ring maps
   (lem-weil-pbc-module-pullback-quasi-coherent, def-pc-module-pullback,
   lem-weil-pbc-left-adjoint-preserves-colimits,
   lem-sc-stalk-flat-tensor-pullback-kernels,
   lem-weil-pbc-flat-morphism-base-change, lem-weil-pbc-flat-ring-map-comp).
3. Equivariant maps are closed under the additive operations and composition.
   Forgetting is faithful. The inverse of an invertible underlying map intertwines
   descent by multiplying the equivariance equation by its inverses. Zero and
   finite sums have the zero and block diagonal descent structures; their
   universal properties hold componentwise.
4. For a colimit of underlying modules, define descent by its equations on the
   colimit legs. The inverse descent maps define its inverse. The unit and cocycle
   laws hold after every leg, and these legs detect equality since pullback
   preserves the colimit, also on the composable-arrow scheme.
5. An equivariant cocone induces a unique underlying map from this colimit.
   Its equivariance follows after precomposing with the pulled-back legs. This
   proves the colimit universal property, also for any given equivariant cocone
   whose underlying cocone is a colimit (def-weil-pbc-category-colimit).
6. A kernel of an underlying equivariant map is quasi-coherent. Flatness gives
   pulled-back kernel universal properties; factor the descent maps through the
   kernel inclusions to obtain mutually inverse descent maps
   (lem-weil-pbc-quasi-coherent-module-kernel).
7. The kernel unit law follows by cancelling its monic inclusion; it needs no
   flatness of e. The cocycle follows by cancellation after the flat composite
   from composable arrows. A factor through the kernel is equivariant by cancelling
   its s-pulled-back inclusion, so this is also the equivariant kernel.
8. Apply the colimit construction to the parallel pair consisting of a map and
   zero. This gives its underlying cokernel with descent. All pullbacks preserve
   the cokernel, so the descent laws follow by epimorphism cancellation.
9. A monomorphism has zero equivariant kernel and hence zero underlying kernel;
   it is therefore monic underneath. Its canonical comparison with the kernel of
   its cokernel is equivariant and invertible underneath, hence invertible above.
   Dually every epimorphism is a cokernel. Together with preadditivity, zero,
   finite biproducts, kernels and cokernels this proves the abelian axioms
   (def-sp-abelian).
10. A finite limit is the kernel of the difference map between the finite sum
    over objects and the finite sum over arrows, whose a-component is
    D(a) composed with the source projection minus the target projection.
    The same formula underneath proves computation of finite limits. For a span
    it is the kernel of [f,-g], giving the asserted pullback. The empty shape gives
    zero, the terminal object. Thus the forgetful functor creates finite limits
    and small colimits, preserves them, and reflects the stated colimit cocones. -/
theorem groupoidModule_limits_colimits
    (S U R : Scheme.{u}) (π : U ⟶ S)
    (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R) (c : pullback s t ⟶ R)
    (hG : IsGroupoid s t e i c) (_hS : s ≫ π = t ≫ π) [Flat s] [Flat t] :
    Nonempty (Abelian (GroupoidModule s t e i c hG)) ∧
      (GroupoidModule.forgetToQuasiCoherent (hG := hG)).Faithful ∧
      (GroupoidModule.forgetToQuasiCoherent (hG := hG)).ReflectsIsomorphisms ∧
      HasFiniteLimits (GroupoidModule s t e i c hG) ∧
      HasColimitsOfSize.{u, u} (GroupoidModule s t e i c hG) ∧
      PreservesFiniteLimits (GroupoidModule.forgetToModules (hG := hG)) ∧
      PreservesColimitsOfSize.{u, u} (GroupoidModule.forgetToModules (hG := hG)) ∧
      (∀ (J : Type) [SmallCategory J] [FinCategory J],
        Nonempty (CreatesLimitsOfShape J (GroupoidModule.forgetToModules (hG := hG)))) ∧
      Nonempty (CreatesColimitsOfSize.{u, u}
        (GroupoidModule.forgetToModules (hG := hG))) ∧
      (∀ (J : Type u) [SmallCategory J] (D : J ⥤ GroupoidModule s t e i c hG),
        SheafOfModules.IsQuasicoherent (R := U.ringCatSheaf)
          (colimit (D ⋙ GroupoidModule.forgetToModules (hG := hG)))) ∧
      (∀ (J : Type u) [SmallCategory J] (D : J ⥤ GroupoidModule s t e i c hG)
          (k : Cocone D),
        Nonempty (IsColimit
          ((GroupoidModule.forgetToModules (hG := hG)).mapCocone k)) →
        Nonempty (IsColimit k)) := by
  sorry

end AlgebraicGeometry.Scheme
