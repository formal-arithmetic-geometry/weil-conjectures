/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import Sheaf.Algebra.Category.ModuleCat.Sheaf.HomFinitePresentationKernel
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree

/-! # Internal Hom kernel models from a specified local presentation -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace AlgebraicGeometry.Scheme.Modules

/-- A specified presentation on V gives a finite-sum Hom kernel on that same open.
Source: Stacks Project, Modules, Lemmas 01CO (1), 01CQ, and the proof of 01CP;
Sites, Modules, Lemma 0E8H for restriction of internal Hom.
(blueprint: lem-weil-pbc-coherent-hom-local-kernel-from-presentation).

Proof:
The cokernel projection followed by e.hom is an epimorphism b with kernel equal
to the image of a. Thus a, b, and the map from G.over V to zero form a right
exact sequence. Identify the finite biproducts of the restricted unit with free
modules on ULift (Fin m) and ULift (Fin n). Apply the left exact precomposition
sequence homObj_precomposition_exact to this presentation and F.over V.
The isomorphisms homObjFreeIso identify its two free-source Hom objects with
finite biproducts of F.over V, reindexed by Fin n and Fin m. The resulting map
between these biproducts is alpha. The first map is monic and its image is the
kernel of alpha, so the kernel universal property gives an isomorphism from
Hom(G.over V, F.over V) to that kernel. Use overHomObjIso to identify the source
with (homObj G F).over V. Finally apply the equivalence overEquiv V: its natural
isomorphism overFunctorEquiv identifies over-restriction with scheme restriction,
and it preserves kernels and finite biproducts. Transport alpha and the kernel
isomorphism through this equivalence. This gives the required map on F.restrict V.ι
and the claimed isomorphism. Each construction uses a universal property valid
also for empty biproducts; no coherence assumption on either G or F is used. -/
theorem homObj_locally_kernel_of_local_presentation
    (X : Scheme.{u}) (G F : X.Modules) (V : X.Opens) (m n : ℕ)
    (a : (⨁ fun _ : Fin m ↦ (SheafOfModules.unit X.ringCatSheaf).over V) ⟶
      (⨁ fun _ : Fin n ↦ (SheafOfModules.unit X.ringCatSheaf).over V))
    (e : (cokernel a) ≅ G.over V) :
    ∃ (α : (⨁ fun _ : Fin n ↦ F.restrict V.ι) ⟶
      (⨁ fun _ : Fin m ↦ F.restrict V.ι)),
      Nonempty ((restrictFunctor V.ι).obj
        (SheafOfModules.homObj (R := X.sheaf) G F) ≅ kernel α) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
