/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange

/-!
# Descent of subobjects along finite families of weakly étale maps, as a kernel

Let `Λ` be a commutative condensed ring, `S` a scheme, `M` a module object over `Λ_S` and
`f_k : V_k ⟶ S` a finite family of weakly étale morphisms. Suppose given, for each `k`, a
morphism `π_k : f_k^* M ⟶ Q_k` (think of the cokernel of a subobject `F_k ⊆ f_k^* M`) such that
on fibre products `P_{jk} = V_j ×_S V_k` (given by cartesian squares `p₁ ≫ f_j = p₂ ≫ f_k`) the
pullbacks of `π_j` and of `π_k` agree up to an isomorphism, through the canonical identification
`p₁^* f_j^* M ≅ p₂^* f_k^* M`. Then the kernel
```
K = ker (M ⟶ ∏_k f_{k*} Q_k)
```
of the adjoints of the `π_k` satisfies `f_j^* K = ker π_j` for every `j`
(`ProEtale.CondensedRing.exists_iso_upperStar_kernel_kernelDescentMap`). In other words,
compatible subobjects of the pullbacks `f_k^* M` descend to a subobject of `M`, without any
gluing theory.

The proof uses weakly étale base change `f_j^* f_{k*} ≅ p₁_* p₂^*`
(`ProEtale.CondensedRing.isIso_lowerStarBaseChange_of_isPullback`) and that the pullback along
`p₁ : V_j ×_S V_j ⟶ V_j` is faithful, `p₁` having the diagonal as a section.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section KernelDescent

variable {S : Scheme.{u}} {ι : Type u} [Finite ι] {V : ι → Scheme.{u}} (f : ∀ k, V k ⟶ S)
  (M : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
  {Q : ∀ k, Mod (Sheaf (ProEt.topology (V k)) Ab.{u + 1}) (condensedRingObj Λ (V k))}
  (π : ∀ k, (f k)^*⟦Λ⟧.obj M ⟶ Q k) {P : ι → ι → Scheme.{u}} {p₁ : ∀ j k, P j k ⟶ V j}
  {p₂ : ∀ j k, P j k ⟶ V k} (hP : ∀ j k, IsPullback (p₁ j k) (p₂ j k) (f j) (f k))
  (ψ : ∀ j k, (p₁ j k)^*⟦Λ⟧.obj (Q j) ≅ (p₂ j k)^*⟦Λ⟧.obj (Q k))

end KernelDescent

end AlgebraicGeometry.ProEtale.CondensedRing
