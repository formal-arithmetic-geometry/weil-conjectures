module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackQCoh
import Mathlib.RingTheory.Flat.Basic

/-!
# Flat pullback of sections supported on a locally principal closed subset

Source: Stacks Project, Properties, Tag 07ZP (2)--(3), and Divisors, Tag 080F;
the affine flat-tensor kernel argument in the DAG proof
(blueprint: lem-trf-supported-kernel-flat-pullback).

The supported submodule is the actual kernel of restriction to the open complement.
Affine extension of scalars uses Mathlib's `C ⊗[A] M` convention; tensor symmetry
identifies it with the node's `M ⊗[A] C`, sending `c ⊗ m` to `m ⊗ c`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

/-- The subsheaf of sections supported on `D`, constructed as the kernel of restriction.
Source: Stacks Project, Properties, Tag 07ZP, proof of (3)
(blueprint: lem-trf-supported-kernel-flat-pullback). -/
noncomputable def supportedSectionsKernel {X : Scheme.{u}} (D : Closeds X) (H : X.Modules) :
    X.Modules :=
  kernel ((restrictAdjunction (Scheme.Opens.ι D.compl)).unit.app H)

/-- The inclusion of the actual restriction kernel into the original module.
Source: Stacks Project, Properties, Tag 07ZP, proof of (3)
(blueprint: lem-trf-supported-kernel-flat-pullback). -/
noncomputable def supportedSectionsKernelι {X : Scheme.{u}} (D : Closeds X) (H : X.Modules) :
    supportedSectionsKernel D H ⟶ H :=
  kernel.ι ((restrictAdjunction (Scheme.Opens.ι D.compl)).unit.app H)

/-- Supported-section kernels are quasi-coherent and commute with flat pullback,
including the canonical affine tensor formulas.
Source: Stacks Project, Properties, Tag 07ZP (2)--(3); Divisors, Tag 080F;
Schemes, Tags 01I9 and 01IA; Algebra, Tags 00HB and 00HD
(blueprint: lem-trf-supported-kernel-flat-pullback).

Proof: On an affine neighbourhood with support V(a), apply
lem-trf-locally-principal-supported-kernel and
lem-trf-supported-sections-quasi-coherent. The complement is a principal affine open,
and the restriction kernel consists exactly of elements killed by some power of a.
These neighbourhoods cover P, so their quasi-coherence proves quasi-coherence of K.
By lem-pc-ringed-space-tensor-pullback-qcoh, u*H and u*K are quasi-coherent.
The local ring homomorphisms of u identify the inverse-image support on every affine
W with V(a_C). Apply the same supported-section calculation on W to obtain
quasi-coherence of L and its description by a_C-power torsion.
Use lem-weil-pbc-module-pullback-affine-sections on H and K: its unit formula gives
the two C-linear bijections, and naturality gives the square with the tensor of inclusion.
By lem-weil-pbc-flat-morphism-affine-criterion, C is A-flat. Tensoring the inclusion
of Gamma_a(M) is injective by lem-weil-pbc-flat-tensor-exact. Every element of its
image is killed by a common power: expand as a finite sum of pure tensors and add
the exponents killing their first factors; for the empty sum the exponent is zero.
Conversely, if a_C^n kills a tensor, flat tensor exactness applied to
0 -> ker(a^n : M -> M) -> M -> M lifts it from that kernel tensored with C.
This kernel lies in Gamma_a(M), proving the reverse image containment; n = 0 gives zero.
C-linearity of the second bijection identifies this torsion with L(W).
The affine opens W cover Q. Kernel sections vanish locally and hence globally;
local preimages of a supported section agree by injectivity and glue by the sheaf axiom.
This proves the image equality on all opens, as well as the stated affine formulas. -/
theorem supportedSectionsKernel_flatPullback
    {Q P : Scheme.{u}} (u : Q ⟶ P) [Flat u] (D : Closeds P)
    (hD : ∀ x : P, ∃ (V : P.affineOpens) (a : Γ(P, V.1)),
      x ∈ V.1 ∧ V.1 ⊓ D.compl = P.basicOpen a)
    (H : P.Modules) (hH : H.IsQuasicoherent) :
    (supportedSectionsKernel D H).IsQuasicoherent ∧
    (supportedSectionsKernel (D.preimage u.base.hom.continuous)
      ((tensorPullback u).obj H)).IsQuasicoherent ∧
    (∀ (V : P.Opens) (s : Γ(H, V)),
      (∃ t : Γ(supportedSectionsKernel D H, V),
        (supportedSectionsKernelι D H).app V t = s) ↔
      H.presheaf.map (homOfLE (inf_le_left : V ⊓ D.compl ≤ V)).op s = 0) ∧
    (∀ (W : Q.Opens),
      Function.Injective (((tensorPullback u).map (supportedSectionsKernelι D H)).app W) ∧
      Set.range (((tensorPullback u).map (supportedSectionsKernelι D H)).app W) =
        Set.range ((supportedSectionsKernelι (D.preimage u.base.hom.continuous)
          ((tensorPullback u).obj H)).app W) ∧
      ∀ s : Γ((tensorPullback u).obj H, W),
        (∃ t : Γ(supportedSectionsKernel (D.preimage u.base.hom.continuous)
            ((tensorPullback u).obj H), W),
          (supportedSectionsKernelι (D.preimage u.base.hom.continuous)
            ((tensorPullback u).obj H)).app W t = s) ↔
        ((tensorPullback u).obj H).presheaf.map
          (homOfLE (inf_le_left : W ⊓ (u ⁻¹ᵁ D.compl) ≤ W)).op s = 0) ∧
    ∀ (V : P.affineOpens) (W : Q.affineOpens) (e : W.1 ≤ u ⁻¹ᵁ V.1)
        (a : Γ(P, V.1)), V.1 ⊓ D.compl = P.basicOpen a →
      (∀ s : Γ(H, V.1),
        (∃ t : Γ(supportedSectionsKernel D H, V.1),
          (supportedSectionsKernelι D H).app V.1 t = s) ↔
        ∃ n : ℕ, a ^ n • s = 0) ∧
      ∃ (cK : (ModuleCat.extendScalars (u.appLE V.1 W.1 e).hom).obj
          (ModuleCat.of Γ(P, V.1) Γ(supportedSectionsKernel D H, V.1)) ≃ₗ[Γ(Q, W.1)]
          Γ((tensorPullback u).obj (supportedSectionsKernel D H), W.1))
        (cH : (ModuleCat.extendScalars (u.appLE V.1 W.1 e).hom).obj
          (ModuleCat.of Γ(P, V.1) Γ(H, V.1)) ≃ₗ[Γ(Q, W.1)] Γ((tensorPullback u).obj H, W.1)),
        (∀ (s : Γ(supportedSectionsKernel D H, V.1)) (c : Γ(Q, W.1)),
          cK (c ⊗ₜ[Γ(P, V.1), (u.appLE V.1 W.1 e).hom] s) =
            c • ((tensorPullback u).obj (supportedSectionsKernel D H)).presheaf.map
              (homOfLE e).op
              (((tensorPullbackSectionAdjunction u).unit.app
                (supportedSectionsKernel D H)).app V.1 s)) ∧
        (∀ (s : Γ(H, V.1)) (c : Γ(Q, W.1)),
          cH (c ⊗ₜ[Γ(P, V.1), (u.appLE V.1 W.1 e).hom] s) =
            c • ((tensorPullback u).obj H).presheaf.map (homOfLE e).op
              (((tensorPullbackSectionAdjunction u).unit.app H).app V.1 s)) ∧
        (∀ t : (ModuleCat.extendScalars (u.appLE V.1 W.1 e).hom).obj
            (ModuleCat.of Γ(P, V.1) Γ(supportedSectionsKernel D H, V.1)),
          ((tensorPullback u).map (supportedSectionsKernelι D H)).app W.1 (cK t) =
            cH ((ModuleCat.extendScalars (u.appLE V.1 W.1 e).hom).map
              ((supportedSectionsKernelι D H).val.app (op V.1)) t)) ∧
        Function.Injective ((ModuleCat.extendScalars (u.appLE V.1 W.1 e).hom).map
          ((supportedSectionsKernelι D H).val.app (op V.1))) ∧
        (∀ t : (ModuleCat.extendScalars (u.appLE V.1 W.1 e).hom).obj
            (ModuleCat.of Γ(P, V.1) Γ(H, V.1)),
          t ∈ Set.range ((ModuleCat.extendScalars (u.appLE V.1 W.1 e).hom).map
            ((supportedSectionsKernelι D H).val.app (op V.1))) ↔
          ∃ n : ℕ, (u.appLE V.1 W.1 e).hom a ^ n • t = 0) ∧
        (∀ t : (ModuleCat.extendScalars (u.appLE V.1 W.1 e).hom).obj
            (ModuleCat.of Γ(P, V.1) Γ(H, V.1)),
          (∃ n : ℕ, (u.appLE V.1 W.1 e).hom a ^ n • t = 0) ↔
          cH t ∈ Set.range ((supportedSectionsKernelι (D.preimage u.base.hom.continuous)
            ((tensorPullback u).obj H)).app W.1)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
