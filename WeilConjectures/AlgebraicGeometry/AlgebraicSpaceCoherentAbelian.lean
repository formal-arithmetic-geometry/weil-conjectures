/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import WeilConjectures.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Coherent modules on locally Noetherian algebraic spaces

Source: Stacks Project, Spaces Cohomology, Tags 07UB and 07UC,
lemma-coherent-Noetherian and lemma-coherent-abelian-Noetherian
(blueprint: lem-sfb-space-coherent-abelian).

By 07UB, on a locally Noetherian algebraic space a module is coherent exactly when
it is finitely presented on its small etale ringed site. We use Mathlib's existing
`SheafOfModules.IsFinitePresentation`, as in `CoherentSubobjects`, without introducing
another coherence predicate. The same criterion is equivalent to quasi-coherence
on the site and coherence of the pullback to every etale scheme chart.

Kernels, cokernels and finite sums are specified by their universal properties in
all module sheaves. Thus the assertion applies to every choice of these objects. The terminal module
is the zero module, since its sections are the zero modules.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Kernels, cokernels, zero, finite direct sums and extensions of coherent modules
on a locally Noetherian algebraic space are coherent. Coherence is expressed by
finite presentation, equivalently site quasi-coherence and chartwise coherence by
07UB. A finite direct sum is a bilimit bicone, including the empty family.

Source: Stacks Project, Spaces Cohomology, Tags 07UB and 07UC
(blueprint: lem-sfb-space-coherent-abelian).

Proof:
1. On each locally Noetherian scheme chart, coherent means quasi-coherent of finite
   type (pqf-lem-coherent-ft-locnoeth). The affine finite-type criterion
   (lem-weil-pbc-quasi-coherent-finite-type-affine), the tilde-section adjunction
   (lem-weil-pbc-affine-tilde-gamma-adjunction), tilde pullback base change and tilde
   sections identify this with finite affine modules and their tensor-sections
   sheaves. The Zariski/etale quasi-coherent equivalence identifies the chartwise
   condition with coherence on the small etale site, hence finite presentation by
   07UB. Local free presentations also give the required site quasi-coherence.
2. Apply lem-sfb-space-coherent-kernel-cokernel-extension with Z = X after this
   identification. It gives the zero, kernel, cokernel and extension assertions in
   the ambient module-sheaf category. The extension middle term is arbitrary.
3. For two coherent modules the direct sum is an extension: include the first
   summand and project to the second, with the second inclusion splitting that
   projection. This is a short exact sequence. Induction on the finite number of
   summands, starting with the zero module for the empty family, gives finite sums.
   Universal properties identify any kernel, cokernel or bilimit bicone with these
   constructions, and finite presentation is invariant under isomorphism. -/
theorem coherent_kernel_cokernel_zero_finite_sum_extension
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T)) :
    (∀ (F G : X.Modules) (f : F ⟶ G),
      F.IsFinitePresentation → G.IsFinitePresentation →
      (∀ k : KernelFork f, IsLimit k → k.pt.IsFinitePresentation) ∧
      (∀ c : CokernelCofork f, IsColimit c → c.pt.IsFinitePresentation)) ∧
    SheafOfModules.IsFinitePresentation (⊤_ X.Modules) ∧
    (∀ (I : Type v) [Finite I] (F : I → X.Modules),
      (∀ i : I, (F i).IsFinitePresentation) →
      ∀ b : Bicone F, b.IsBilimit → b.pt.IsFinitePresentation) ∧
    (∀ c : ShortComplex X.Modules, c.ShortExact →
      c.X₁.IsFinitePresentation → c.X₃.IsFinitePresentation → c.X₂.IsFinitePresentation) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
