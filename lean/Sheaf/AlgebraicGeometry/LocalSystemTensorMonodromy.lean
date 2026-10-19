/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q67
-/
module

public import Sheaf.AlgebraicGeometry.TorsionLocalSystemMonodromy
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Map
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar
import Sheaf.ConstructibleSheaf.GaloisCoverModuleDescent
import Sheaf.ConstructibleSheaf.GaloisDescentMonodromyTensor

/-! # Tensor comparison for arbitrary torsion local systems

Source: ILO, Travaux de Gabber, Exposé XVII, 7.2.1--7.2.4, pp. 301--302;
Stacks Project, Tags 03EL and 0GMW (blueprint: lem-per-local-system-tensor-monodromy).
The constant-coefficient module sheaf encoding and its ordinary sheafified tensor
are the ones used by the recorded monodromy equivalence. No finite-stalk or
finite-generation restriction is imposed.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme

/-- The actual module-valued geometric stalk, with its existing maps.
Source: ILO XVII 7.2.3 (blueprint: lem-per-local-system-tensor-monodromy). -/
noncomputable abbrev torsionLocalSystemFiber {S : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (R : Type (u + 1)) [CommRing R] :=
  (pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} R)

/-- Monodromy on the actual stalk, conjugated by the specified stalk identification.
This is a real linear map, not an independently chosen action.
Source: ILO XVII 7.2.3 (blueprint: lem-per-local-system-tensor-monodromy). -/
noncomputable def torsionLocalSystemStalkAction {S : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] {s : Spec (.of Ω) ⟶ S}
    {R : Type (u + 1)} [CommRing R] (E : TorsionLocalSystemStalkEquivalence R s)
    (L : IndFiniteEtaleModules.{u} S R) (g : Aut (FiniteEtale.fiber s)) :
    (torsionLocalSystemFiber s R).obj L.obj →ₗ[R]
      (torsionLocalSystemFiber s R).obj L.obj :=
  (E.stalkIso.inv.app L ≫ ModuleCat.ofHom ((E.equivalence.functor.obj L).obj.ρ g) ≫
    E.stalkIso.hom.app L).hom

/-- The canonical tensor-of-sections map into the underlying tensor sheaf.
It is the tensorator of the right adjoint of sheafification, hence includes the
canonical map from the objectwise tensor to its sheafification.
Source: Stacks 0GMW (blueprint: lem-per-local-system-tensor-monodromy). -/
noncomputable def torsionLocalSystemTensorSections {S : Scheme.{u}}
    {R : Type (u + 1)} [CommRing R]
    (L M : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    L.obj ⊗ M.obj ⟶ (L ⊗ M).obj :=
  (sheafificationAdjunction S.smallEtaleTopology
    (ModuleCat.{u + 1} R)).rightAdjointLaxMonoidal.μ L M

/-- Tensor closure and the natural equivariant stalk comparison, with the inverse
normalized on germs of sections. The parameter E is any geometric-stalk equivalence
with the finite-cover germ normalization of the recorded monodromy theorem.
Source: ILO XVII 7.2.1--7.2.4, pp. 301--302; Stacks 03EL and 0GMW
(blueprint: lem-per-local-system-tensor-monodromy).

Proof:
1. For each stalk, compactness of the profinite group makes every orbit finite.
The spans of finite unions of orbits form a small directed system of finitely
 generated invariant submodules, with union the entire stalk. No finiteness of R
or of its underlying modules is used (lem-per-torsion-local-system-monodromy).
2. Transport these submodules to local systems by the monodromy equivalence.
Its ambient exactness makes their inclusion maps monic, and its colimit clause
identifies their ambient colimits with L and M. Each term is locally constant
of finite type by the finite-generation clause of that same theorem.
3. For each pair of terms, trivialize their direct sum on a connected finite
étale Galois cover. This trivializes both summands; no common cover for all
terms or for the original two local systems is chosen.
4. Tensor of constant module sheaves is constant by
lem-pc-sites-module-sheafification-tensor. Constant-scalar inverse image and
ringed-topos pullback commute with tensor by lem-pe-constant-left-module-inverse-image
and lem-weil-pbc-ringed-topoi-module-pullback-tensor. Thus this pair's tensor
is constant on that cover; finite-cover descent makes it a local system on S.
5. Sheaf tensor preserves colimits separately (lem-weil-pbc-sheaf-tensor-closed).
Its agreement with tensor over the constant ring sheaf is Tag 0GMW. Express
L tensor M as the iterated colimit of the pairwise tensors. The monodromy
ambient-colimit clause makes this a local system.
6. Apply lem-pod-etale-stalk-tensor-scalar and the sheafification comparison.
The resulting inverse maps a tensor of section germs to their tensor's germ.
7. On a finite Galois cover trivializing a pair, use
lem-per-galois-cover-module-descent and lem-per-galois-descent-monodromy-tensor:
the fibre action on its tensor is diagonal. The pure-germ formula identifies
this descent comparison with that of step 6 on pure tensors. For arbitrary
stalk elements choose finite-generated invariant terms containing them;
naturality and the equivariant inclusion maps pass the equality to L and M.
Pure tensors generate, giving equivariance on every tensor. Finite intersections
of the factors' open stabilizers fix each finite tensor sum, so its diagonal
stabilizer is open. Naturality of the inverse follows from the stalk comparison. -/
theorem local_system_tensor_monodromy
    (S : Scheme.{u}) [IsNoetherian S] [ConnectedSpace S]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (R : Type (u + 1)) [CommRing R] (n : ℕ) (hn : 0 < n) (hR : (n : R) = 0) :
    ∃ E : TorsionLocalSystemStalkEquivalence R s,
      ∃ h : ∀ L M : IndFiniteEtaleModules.{u} S R,
        IsIndFiniteEtaleModule (L.obj ⊗ M.obj),
      ∃ e : ∀ L M : IndFiniteEtaleModules.{u} S R,
          (torsionLocalSystemFiber s R).obj (L.obj ⊗ M.obj) ≅
            (torsionLocalSystemFiber s R).obj L.obj ⊗
              (torsionLocalSystemFiber s R).obj M.obj,
        (∀ (L L' M M' : IndFiniteEtaleModules.{u} S R) (f : L ⟶ L')
              (g : M ⟶ M'),
            (torsionLocalSystemFiber s R).map (f.hom ⊗ₘ g.hom) ≫
                (e L' M').hom =
              (e L M).hom ≫
                ((torsionLocalSystemFiber s R).map f.hom ⊗ₘ
                  (torsionLocalSystemFiber s R).map g.hom)) ∧
        (∀ (L M : IndFiniteEtaleModules.{u} S R) (U : S.Etale)
              (a : (pointSmallEtale s).fiber.obj U)
              (x : L.obj.obj.obj (op U)) (y : M.obj.obj.obj (op U)),
            (e L M).inv.hom
                ((((pointSmallEtale s).toPresheafFiber U a L.obj.obj).hom x) ⊗ₜ[R]
                  (((pointSmallEtale s).toPresheafFiber U a M.obj.obj).hom y)) =
              ((pointSmallEtale s).toPresheafFiber U a (L.obj ⊗ M.obj).obj).hom
                (((torsionLocalSystemTensorSections L.obj M.obj).app (op U)).hom
                  (x ⊗ₜ[R] y))) ∧
        (∀ (L M : IndFiniteEtaleModules.{u} S R)
              (g : Aut (FiniteEtale.fiber s))
              (z : (torsionLocalSystemFiber s R).obj (L.obj ⊗ M.obj)),
            (e L M).hom.hom
                (torsionLocalSystemStalkAction E ⟨L.obj ⊗ M.obj, h L M⟩ g z) =
              TensorProduct.map (torsionLocalSystemStalkAction E L g)
                (torsionLocalSystemStalkAction E M g) ((e L M).hom.hom z)) := by
  sorry

end AlgebraicGeometry.Scheme
