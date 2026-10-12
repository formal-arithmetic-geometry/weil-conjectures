/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # Local finite free presentations of coherent modules -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace AlgebraicGeometry.Scheme.Modules

/-- A coherent source has a finite free cokernel presentation near each point.
Source: Stacks Project, Modules, Lemma 01BW (lemma-coherent-finite-presentation).
(blueprint: lem-weil-pbc-coherent-local-finite-presentation).

Proof:
Finite type gives an open neighbourhood W of x and an epimorphism from a finite
free module to G.over W. Reindex its finite basis by ULift (Fin n). The kernel
is of finite type by the second condition of RingedSpace.IsCoherent. Choose a
smaller neighbourhood V of x and an epimorphism from a free module with basis
ULift (Fin m) to the restriction of this kernel. Restriction to a smaller open
preserves epimorphisms and kernels: stalks are unchanged at points of that open.
Compose this second epimorphism with the restricted kernel inclusion to obtain
a map a between the two finite free modules on V. Its image is the kernel of
the first epimorphism restricted to V, so that epimorphism is a cokernel of a
in the abelian category of module sheaves. Cokernel uniqueness gives the stated
isomorphism. Identify the finite free modules with the finite biproducts of the
restricted unit; the empty basis gives the zero object, so ranks zero are allowed. -/
theorem coherent_local_finite_presentation
    (X : Scheme.{u}) (G : X.Modules)
    (hG : RingedSpace.IsCoherent X.toRingedSpace G) (x : X) :
    ∃ (V : X.Opens), x ∈ V ∧ ∃ (m n : ℕ)
      (a : (⨁ fun _ : Fin m ↦ (SheafOfModules.unit X.ringCatSheaf).over V) ⟶
        (⨁ fun _ : Fin n ↦ (SheafOfModules.unit X.ringCatSheaf).over V)),
      Nonempty ((cokernel a) ≅ G.over V) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
