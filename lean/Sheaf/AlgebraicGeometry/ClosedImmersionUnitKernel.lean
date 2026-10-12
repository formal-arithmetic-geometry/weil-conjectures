/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Abelian.Images
import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
import Sheaf.AlgebraicGeometry.ClosedPushforwardStalks
import Sheaf.AlgebraicGeometry.Modules.TensorPullbackStalk
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct

/-!
# Kernel of the closed immersion pullback unit

Source: Stacks Project, Morphisms of Spaces, Lemma 04CJ (1), and Modules,
Lemma 08KS (blueprint: lem-weil-pbc-closed-immersion-unit-kernel).
-/

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
/-- The geometric part of the closed immersion quotient theorem: the unit is epi
and the multiplication image is its kernel.

Source: Stacks Project, Morphisms of Spaces, Lemma 04CJ (1), with the stalkwise
argument of Modules, Lemma 08KS
(blueprint: lem-weil-pbc-closed-immersion-unit-kernel).

Proof: outside the closed image the pushforward stalk vanishes. On an open
neighbourhood disjoint from that image the ideal is the whole structure sheaf,
so multiplication by its unit makes JF equal to F. At x = i(z), the local ring
map R = O_{Y,x} → S = O_{Z,z} is surjective with kernel K = J_x. The pullback and
closed-pushforward stalk identifications make the unit M → M ⊗_R S, m ↦ m ⊗ 1.
Identify S with R/K. The map M/KM → M ⊗_R R/K is invertible: its inverse sends
m ⊗ r̄ to rm modulo KM; changing the lift of r̄ adds an element of KM, and the
balanced tensor relations preserve this formula. Thus the unit is surjective
with kernel KM. Stalks preserve tensor products and images, so the stalk of
the multiplication image is KM. Stalks preserve kernels and detect exactness
and local surjectivity. The induced map from the multiplication image to the
kernel is an isomorphism on stalks and hence an isomorphism of sheaves;
transporting the kernel universal property along it gives the required limit
fork. The stalk formula is for the canonical adjunction of
Tag 0096. Any other adjunction between these same functors differs by a natural
automorphism of the left adjoint, so its unit is the canonical unit followed by
the pushforward of an isomorphism. Postcomposition with an isomorphism preserves
the kernel fork and the epi property; hence the chosen adjunction in the
statement has these same properties. Therefore the unit is epi and the
multiplication-image inclusion has the universal property of its kernel. -/
theorem closedImmersion_unit_kernel {Y Z : Scheme.{w}} (i : Z ⟶ Y)
    [IsClosedImmersion i] :
    let adj : tensorPullback i ⊣ pushforward i :=
      Classical.choice (nonempty_tensorPullbackAdjunction i)
    let J : Y.IdealSheafData := i.ker
    let μ : ∀ F : Y.Modules, J.toModules ⊗ F ⟶ F := fun F =>
      J.toModulesι ▷ F ≫ (λ_ F).hom
    ∀ F : Y.Modules,
      Epi (adj.unit.app F) ∧
        (∃ w : image.ι (μ F) ≫ adj.unit.app F = 0,
          Nonempty (IsLimit (KernelFork.ofι (image.ι (μ F)) w))) := by
  sorry
end
end AlgebraicGeometry.Scheme.Modules
