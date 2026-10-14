/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons

/-! # Tensor pairing for the coefficient-degree comparisons

Source: Stacks Project, Tags 01CD and 09MS.
(blueprint: lem-sc-boundary-coefficient-tensor-product).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section

/-- Move the ideal factor to the left and multiply the two tensor degrees.
Source: Stacks Project, Tag 09MS, ideal coefficient tensor multiplication.
(blueprint: lem-sc-boundary-coefficient-tensor-product). -/
def boundaryIdealTensorProduct {X : Scheme.{u}} (J L : X.Modules) (a b : ℕ) :
    L.tensorPow a ⊗ (J ⊗ L.tensorPow b) ⟶ J ⊗ L.tensorPow (a + b) :=
  (α_ _ _ _).inv ≫ (β_ _ _).hom ▷ _ ≫ (α_ _ _ _).hom ≫
    J ◁ (L.tensorPowAddIso a b).inv

/-- The coefficient comparison repartitions a product into its coefficient and section blocks.
This involves only tensor comparisons on Z, with no kernel, square-zero hypothesis, or lift.

Source: Stacks Project, Tag 01CD (pullback of tensor products), and Tag 09MS,
coherent-equation-ses (tensor powers of the ideal coefficient).
(blueprint: lem-sc-boundary-coefficient-tensor-product).
Proof: Expand boundaryIdealTensorProduct and the coefficient-degree comparisons.
The latter first group the L factors into blocks of n, move the first block into
J tensor L^n, and pull back the remaining blocks. Naturality of the pullback
comparison moves the associators and braiding through pullback. Induction on n
in boundaryPullbackPowIso and on e in tensorPowMulIso identifies the remaining
blocks with the section-degree comparison. Associator coherence and the symmetry
interchanging the two L blocks identify the two products; this symmetry acts
trivially on tensor powers of the invertible L, as is checked on a local generator.
At exponent zero the triangle identities give the same equality with unitors.
Evaluating on q tensor s and using the inverse right unitor at source degree zero
gives the displayed equality. This is local on Z, so the generator calculation
on trivializing opens glues by separation. Empty opens and zero sections obey the
same tensor identities. -/
theorem boundaryCoefficientDegreeIso_tensor_product {X Z : Scheme.{u}} (j : Z ⟶ X)
    (L : X.Modules) [L.IsInvertible] (n e : ℕ) (V : Z.Opens)
    (q : Γ((tensorPullback j).obj (L.tensorPow (n * (e + 1))), V))
    (s : Γ((tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow (n * (0 + 1))), V)) :
    let a := n * (e + 1)
    let b := n * (0 + 1)
    let c := n * ((e + 1) + 1)
    let m := boundaryIdealTensorProduct j.ker.toModules L a b ≫
      j.ker.toModules ◁ (eqToHom (by
        dsimp [a, b, c]
        congr 1
        simp only [Nat.mul_add, Nat.mul_one]) : L.tensorPow (a + b) ⟶ L.tensorPow c)
    (boundaryCoefficientDegreeIso j L n (e + 1)).hom.app V
        (((tensorPullback j).map m).app V
          ((boundaryPullbackTensorIso j (L.tensorPow a)
            (j.ker.toModules ⊗ L.tensorPow b)).inv.app V (tmulSection q s))) =
      tmulSection
        ((ρ_ ((tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n))).hom.app V
          ((boundaryCoefficientDegreeIso j L n 0).hom.app V s))
        ((boundarySectionDegreeIso j L n e).hom.app V q) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
