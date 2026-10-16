/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Sheaf.AlgebraicGeometry.ConstructibleAbelianSheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Data.ZMod.Basic

import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.TensorPullback
import WeilConjectures.Mathlib.RingTheory.Extension.Presentation.Submersive
import WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.LinearAlgebra.SemilinearFrobenius
public import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Sheaf
import Sheaf.AlgebraicGeometry.EtaleStratifiedFinite
import Sheaf.AlgebraicGeometry.Sites.InverseImageRepresentable
import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Sheaf.AlgebraicGeometry.FiniteEtaleYonedaLocalTrivializations
import Sheaf.AlgebraicGeometry.FiniteLocalAbelianForget
import WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Fixed points of Frobenius-semilinear vector-bundle endomorphisms

Source: Stacks Project, More on Étale Cohomology, Tag 0GKU,
lemma-frobenius-linear-on-vb, Noetherian specialization
(blueprint: lem-weil-pbc-frobenius-vector-bundle-kernel).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option autoImplicit false

/-- A Frobenius-semilinear endomorphism of a finite locally free module has zero
cokernel after subtracting the identity, and its fixed-point sheaf is constructible.
The sectionwise lift uses the transported additive structure; scalar multiplication
is written explicitly by lowering both sections and lifting their product.
Source: Stacks Project, Tag 0GKU (Noetherian specialization).
(blueprint: lem-weil-pbc-frobenius-vector-bundle-kernel)

Proof:
1. Choose finitely many affine trivializing charts, with independently varying finite
ranks. Local Noetherianness gives quasi-separatedness. On a chart, write F as a matrix
applied to p-th powers of the coordinates; tensor pullback preserves the free basis.
2. For a target vector b, adjoin solutions of b_i + x_i - sum_j c_ij x_j^p = 0.
The Jacobian is the identity, so the square-Jacobian criterion makes this cover étale.
3. Lang's semilinear surjectivity over algebraically closed residue fields makes every
geometric fibre nonempty. These solution covers prove local surjectivity, hence the
abelian sheaf cokernel vanishes. Lift the calculations sectionwise along ULift.
4. At b = 0 the same affine étale scheme represents the kernel: its coordinate tuples
are exactly fixed sections, naturally under restriction, and the affine identifications glue.
5. Stratify each chart into finitely many constructible locally closed subschemes over
which this representing scheme is finite étale. Inverse image of a represented sheaf
is represented by its base change, compatibly with the abelian underlying set sheaf.
6. Finite étale Yoneda trivializations and the finite-local-abelian-forget comparison
make the abelian kernel finite locally constant on each stratum.
7. Refine all chart stratifications to one finite global partition. Inverse-image
composition and base change of covering families transport the local trivializations;
inverse image preserves constant finite abelian sheaves. This is precisely the finite
abelian stratum definition of constructibility. The empty scheme uses the empty
partition; rank zero uses the identity solution cover and the zero kernel. -/
theorem frobenius_vectorBundle_kernel_constructible
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u})
    [S.Over (Spec (.of (ULift.{u} (ZMod p))))] [CompactSpace S] [IsLocallyNoetherian S]
    (E : S.Modules) [E.IsFiniteLocallyFree]
    (F : (sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Modules.etaleTensorSectionsSheaf E) ⟶
      (sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Modules.etaleTensorSectionsSheaf E))
    (hF : ∀ (U : S.Etaleᵒᵖ) (a : ULift.{u + 1} Γ(U.unop.left, ⊤))
        (e : ULift.{u + 1} Γ((Modules.tensorPullback U.unop.hom).obj E, ⊤)),
      F.hom.app U (ULift.up (a.down • e.down)) =
        ULift.up (a.down ^ p • (@id Γ((Modules.tensorPullback U.unop.hom).obj E, ⊤)
          (F.hom.app U e).down))) :
    IsZero (cokernel (F - 𝟙 _)) ∧
      IsConstructibleAbelianSheaf (kernel (F - 𝟙 _)) := by
  sorry

end AlgebraicGeometry.Scheme
