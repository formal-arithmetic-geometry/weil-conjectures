/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Sheaf.AlgebraicGeometry.Coherent
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Finite type of kernels of finite free surjections

Source: Stacks Project, Modules, Lemma 01BP(1)
(blueprint: lem-weil-pbc-finite-presentation-kernel-surjection-finite-type).
-/

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

/-- If a module has a local finite presentation, the kernel of a finite free
surjection onto it is locally of finite type.
Source: Stacks Project, Modules, Lemma 01BP(1)
(blueprint: lem-weil-pbc-finite-presentation-kernel-surjection-finite-type).

Proof (following the four steps of the node):
1. A map out of a finite free module is determined by the images of its basis sections,
   and every finite tuple of sections defines such a map
   (`def-weil-sheaf-of-modules-category`). Kernels are sectionwise, commute with restriction
   to opens, and receive the unique factorization of every map whose composite is zero.
2. Fix a point x and choose a presentation chi, phi on a neighbourhood U
   (`F.IsFinitePresentation`, Stacks 01BN: exact O_U^m -> O_U^n -> F|U -> 0).
   By local lifting for epimorphisms
   (`lem-weil-pbc-ringed-space-module-exactness-local-lifting`), shrink U finitely many
   times to lift the r images under psi through phi and the n images under phi
   through psi. The lifts define alpha and beta with phi alpha = psi and psi beta = phi.
   Exactness and surjectivity persist on the smaller open by the same local criteria.
3. The map gamma = (beta chi, 1 - beta alpha) from the free module of rank m + r satisfies
   psi gamma = 0: psi beta chi = phi chi = 0 and psi (1 - beta alpha) = psi - phi alpha = 0.
   Hence gamma factors through the restriction of kernel psi, by Step 1.
4. If psi(s) = 0 on an open W inside U, then phi(alpha(s)) = 0. Exactness and local lifting
   (`lem-weil-pbc-ringed-space-module-exactness-local-lifting`) give a covering W_i of W
   and sections t_i with chi(t_i) = alpha(s)|W_i. On W_i, gamma(t_i, s|W_i) = s|W_i.
   Thus the factorization of gamma is an epimorphism onto (kernel psi)|U. Every point has
   such a neighbourhood with m + r generators, so kernel psi is of finite type
   (`pqf-def-coherent`, finite-type clause; Stacks Definition 01B5). -/
theorem finitePresentation_kernel_surjection_finiteType
    (X : RingedSpace.{u})
    (F : SheafOfModules.{u} (moduleRings X))
    [F.IsFinitePresentation]
    (r : ℕ)
    (ψ : SheafOfModules.free (R := moduleRings X) (ULift.{u} (Fin r)) ⟶ F)
    (hψ : Epi ψ) :
    (kernel ψ).IsFiniteType := by
  sorry

end AlgebraicGeometry.RingedSpace
