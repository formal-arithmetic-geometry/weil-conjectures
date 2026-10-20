/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q83
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
public import Mathlib.Algebra.Exact.Basic

import Sheaf.AlgebraicGeometry.ZariskiEtaleTensorSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.StalkFlatTensorPullbackKernels
import Sheaf.AlgebraicGeometry.GlobalSectionsLeftExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-!
# Kernels of quasi-coherent modules on the small étale site

Source: Stacks Project, Descent, Tag 0GNB(3), via Tag 06VE(1),(5)
(blueprint: lem-trf-scheme-etale-quasi-coherent-kernel).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- A kernel of quasi-coherent small étale modules is quasi-coherent. On every étale object,
its canonical inclusion identifies its sections with the kernel of the component map.
Here `smallEtaleModuleRing T` has section ring `Γ(U.left, ⊤)` at `U : T.Etale`.
Source: Stacks Project, Descent, Tag 0GNB(3), and Tag 06VE(1),(5)
(blueprint: lem-trf-scheme-etale-quasi-coherent-kernel).

Proof:
1. By lem-trf-scheme-zariski-etale-quasi-coherent-equivalence, choose quasi-coherent
   Zariski modules F and G representing M and N. Full faithfulness lifts φ to ψ : F → G.
   The morphism formula of lem-trf-zariski-etale-tensor-sections identifies the component
   of ψ_et at U with Γ(U, u^*ψ). Conjugate by the representing isomorphisms at the end.
2. Form the Zariski kernel i : K → F. By lem-weil-pbc-quasi-coherent-module-kernel,
   K is quasi-coherent; the same Zariski/étale equivalence makes K_et quasi-coherent.
3. For every étale u : U → T, étaleness implies flatness of each stalk map
   (def-weil-etale-morphism, def-weil-flat-morphism). The tensor pullback of
   lem-pc-module-pullback-adjunction acts by 1 tensor u^{-1}ψ; this is additive on
   local tensors. Its specified object and map formulas meet the hypotheses of
   lem-sc-stalk-flat-tensor-pullback-kernels, so u^*i is a kernel of u^*ψ.
   By lem-sc-global-sections-left-exact, Γ(U, u^*i) is a kernel of Γ(U, u^*ψ).
   Only preservation of kernels is needed, not preservation of epimorphisms.
4. The same tensor-sections formula identifies the component of i_et with Γ(U, u^*i).
   Thus i_et is sectionwise injective and has image exactly the component kernel.
   By lem-weil-pbc-module-sheaves-limits-sectionwise, these are the categorical kernel
   sections. Their bijections commute with restrictions because i_et does; the inverse
   bijections commute by uniqueness of preimages. Hence K_et is isomorphic to the
   categorical kernel of ψ_et. Transport quasi-coherence across this isomorphism and
   across the isomorphisms representing M and N. The same sectionwise-limit result
   gives the asserted injectivity and exactness for the canonical inclusion of ker φ. -/
theorem isQuasicoherent_smallEtale_kernel (T : Scheme.{u})
    {M N : ringedSiteModules.{u} (smallEtaleModuleRing T)}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) :
    (kernel φ).IsQuasicoherent ∧
      ∀ U : T.Etale,
        Function.Injective ((kernel.ι φ).val.app (op U)) ∧
          Function.Exact ((kernel.ι φ).val.app (op U)) (φ.val.app (op U)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
