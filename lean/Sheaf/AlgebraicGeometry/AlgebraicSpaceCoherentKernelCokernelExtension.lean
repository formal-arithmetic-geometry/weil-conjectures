/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage

/-!
# Kernels, cokernels and extensions of coherent algebraic-space modules

Source: Stacks Project, Spaces Cohomology, Tags 07UB and 07UC
(blueprint: lem-sfb-space-coherent-kernel-cokernel-extension).

On a locally Noetherian algebraic space, Tag 07UB identifies coherence with finite
presentation on the small etale ringed site. On an affine etale chart Spec R this is
precisely the sheaf associated to a finite R-module N, with sections B tensor_R N on
affine etale maps Spec B to Spec R. We use Mathlib's existing finite-presentation
predicate, as in the project's other coherent algebraic-space statements.

Kernel forks and cokernel coforks are taken in all module sheaves, and quantified
with their universal properties. The terminal module is the zero module. These
formulations do not choose a second abelian structure or impose extra instances.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Coherent modules on a locally Noetherian algebraic space contain zero and are
closed under kernels, cokernels, extensions and isomorphisms in all module sheaves.
Source: Stacks Project, Spaces Cohomology, Tags 07UB and 07UC
(blueprint: lem-sfb-space-coherent-kernel-cokernel-extension).

Proof:
1. Restrict to an arbitrary Noetherian affine etale chart V = Spec R. Restriction
   is exact by lem-pur-site-restriction-module-adjunction-exact. The fully faithful
   Zariski/etale comparison of lem-trf-scheme-zariski-etale-quasi-coherent-equivalence
   is exact into ambient module sheaves by
   lem-sfb-scheme-etale-module-exact-finiteness-comparison. Tilde sections and
   pullback base change identify the chart restriction with B tensor_R N for a
   finite R-module N. The affine finite-type criterion and
   pqf-lem-coherent-ft-locnoeth identify these with coherent Zariski modules.
   Conversely use the affine tilde/global-sections adjunction. Affine covers of
   every locally Noetherian chart show that these modules are site quasi-coherent.
2. Lift a map of coherent chart restrictions through the fully faithful scheme
   comparison. Apply lem-weil-pbc-coherent-modules-kernel-cokernel-sum to its
   kernel and cokernel. Exact comparison, and then exact restriction, identify
   these with the ambient etale kernel and cokernel. Step 1 gives the required
   finite-module formula on every affine chart. Universal properties identify
   every limiting kernel fork and colimiting cokernel cofork with these objects.
3. For an extension with coherent endpoints, step 1 makes the endpoints
   quasi-coherent. By lem-sfb-space-qcoh-extension-closed the middle term is
   quasi-coherent too. Restrict the short exact sequence to V and use the scheme
   comparison. Scheme kernels, images, cokernels and homology are quasi-coherent
   by lem-weil-pbc-quasi-coherent-module-kernel and
   lem-weil-pbc-quasi-coherent-module-cokernel-image. Exact comparison kills its
   homology and full faithfulness reflects zero objects, so the Zariski sequence
   is short exact. The scheme coherent extension theorem makes its middle term
   coherent. Step 1 now gives coherence of the original middle term on each chart.
4. Zero has the affine formula B tensor_R 0 = 0, and the zero module is generated
   by the empty set. An isomorphism restricts to isomorphisms on every chart;
   transport the same finite-module presentation along it. Applying its inverse
   proves the converse, giving the displayed equivalence. -/
theorem coherent_kernel_cokernel_extension
    {S : Scheme.{u}} (Z : AlgebraicSpace S)
    (hln : ∀ T : Z.EtaleSite, IsLocallyNoetherian (Z.etaleForget.obj T)) :
    SheafOfModules.IsFinitePresentation (⊤_ Z.Modules) ∧
    (∀ (F G : Z.Modules) (f : F ⟶ G),
      F.IsFinitePresentation → G.IsFinitePresentation →
      (∀ k : KernelFork f, IsLimit k → k.pt.IsFinitePresentation) ∧
      (∀ c : CokernelCofork f, IsColimit c → c.pt.IsFinitePresentation)) ∧
    (∀ c : ShortComplex Z.Modules, c.ShortExact →
      c.X₁.IsFinitePresentation → c.X₃.IsFinitePresentation → c.X₂.IsFinitePresentation) ∧
    (∀ (F G : Z.Modules) (_e : F ≅ G),
      F.IsFinitePresentation ↔ G.IsFinitePresentation) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
