/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.Paper.GaloisPartitionModules
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Limits.HasLimits
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Sheaf.AlgebraicGeometry.LocalSystemTensorMonodromy
import Sheaf.AlgebraicGeometry.TorsionLocalSystemMonodromy

/-!
# Tensor closure for a fixed Galois partition

Source: ILO, Travaux de Gabber, Expose XVII, 7.2.3--7.2.5, Definitions 7.3.2--7.3.3,
and Propositions 11.2.1 and 11.3.4; the tensor-filtration consequence used in Lemma 7.6.11
(blueprint: lem-per-galois-partition-tensor-closure).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme

/-- Ordinary tensor preserves the weakly constructible class of the same Galois partition.
The factors may have arbitrary module values and neither factor is assumed flat.
Source: ILO XVII, 7.2.3--7.2.5, Definitions 7.3.2--7.3.3, Propositions 11.2.1(i),(vii),(x),(xi)
and 11.3.4, the tensor-filtration consequence used in Lemma 7.6.11
(blueprint: lem-per-galois-partition-tensor-closure).

Proof:
1. Fix a stratum S with cover V. Exact constant-coefficient inverse image commutes with
ordinary tensor (lem-pe-constant-left-module-inverse-image and
lem-weil-pbc-ringed-topoi-module-pullback-tensor). Restrict the two filtered-colimit
presentations to S; the cover V is kept fixed.
2. Choose a geometric point of V. The exact, colimit-preserving monodromy equivalence
of lem-per-torsion-local-system-monodromy identifies finite-filtered terms with discrete
Pi-modules having finite Pi-stable filtrations whose quotients have trivial H-action,
where Pi = pi_1(S) and H is the image of pi_1(V). The coefficient algebra is killed by l,
so torsion local systems are closed under the ambient extensions in these filtrations.
3. By lem-per-local-system-tensor-monodromy, the tensor of two such terms has monodromy
U tensor_A W with diagonal action. Set T_k to the sum of the images of U_a tensor W_b
for a+b <= k. These submodules are Pi-stable, start at zero, and exhaust the tensor.
For h in H the identity
(h-1)(u tensor w) = (hu-u) tensor hw + u tensor (hw-w)
places the difference in T_(a+b-1). Pure tensors generate each image, so H acts trivially
on each successive quotient. Only images are used, never injectivity after tensoring
(def-weil-pbc-module-tensor-product). A zero-length factor filtration gives zero tensor.
4. Transport this filtration back through the exact monodromy equivalence. Its quotients
pull back to constants on V and hence are locally constant on S, witnessed by V itself
(lem-per-torsion-local-system-monodromy). Thus each tensor term is finite-filtered.
5. Ordinary sheaf tensor preserves colimits in each variable
(lem-weil-pbc-sheaf-tensor-closed and lem-pc-sites-module-sheafification-tensor).
The product of the two small filtered categories is again small and filtered,
coordinatewise. The restricted tensor is therefore the filtered colimit of the tensor
terms in step 4, giving precisely the presentation required for membership.
6. Apply this on every stratum. Empty X uses the empty partition and a vacuous condition.
Arbitrary constant modules, zero modules and zero-length filtrations are allowed.
No flatness assumption enters the convolution image filtration. -/
theorem GaloisPartition.modules_tensor
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A] [Algebra (ZMod l) A]
    (P : GaloisPartition X)
    (E G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hE : P.modules A E) (hG : P.modules A G) :
    P.modules A (E ⊗ G) := by
  sorry

end AlgebraicGeometry.Scheme
