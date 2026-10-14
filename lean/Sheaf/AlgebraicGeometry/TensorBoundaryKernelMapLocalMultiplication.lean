/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.AlgebraicGeometry.TensorBoundaryKernelMapNaturality

/-! # Local tensor multiplication under the canonical kernel comparisons

Source: Stacks Project, Tag 09MS, coherent-equation-ses and its ideal coefficient.
(blueprint: lem-sc-tensor-boundary-kernel-map-local-multiplication).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section

/-- In a local lift of a homogeneous quotient section, the transported
kernel map is ordinary tensor multiplication after the kernel inclusion.
There is no graded presentation, ring action or degree projection in this statement.

Source: Stacks Project, Tag 09MS, coherent-equation-ses and the identification
of its ideal coefficient over Z; Modules, Tag 08KS, the closed-immersion quotient.
(blueprint: lem-sc-tensor-boundary-kernel-map-local-multiplication).
Proof: It suffices by sheaf separation to work on an open trivializing L, and
then on a refinement lifting the restricted quotient section. Write ell^r for
the recursively parenthesized tensor of a local generator ell in degree r;
ell^0 is the tensor unit section. The inclusion equation in
boundaryIdealKernelIso identifies a degree-n kernel section y with r ell^n
for a section r of J. Write t=a ell^(n(e+1)). The map in the conclusion has
source and target kernel comparisons made of three factors. The first factor,
the inverse ideal-kernel isomorphism, sends y to r ell^n by its inclusion
equation. The second, the annihilated-module adjunction unit, sends this to
the class of r ell^n over Z. The third, boundaryCoefficientDegreeIso at zero,
sends it to the same coefficient tensored with the degree-zero unit.
Tensoring by x changes this to the class of ar times the coefficient tensor
ell^(n(e+1)). Inverting the three target factors gives ar ell^(n(e+2)).
For the tensor identifications, induction on each exponent in
boundaryPullbackPowIso sends ell^q to the tensor of q copies of the image
of ell: the zero case is pullbackObjUnitIso, and the successor case is
boundaryPullbackTensorIso followed by the induction hypothesis. Induction
on e in tensorPowMulIso and its associators identifies blocks of n copies
with n(e+1) copies. The same inductions in boundaryCoefficientDegreeIso
leave the J factor fixed and repartition the L factors. Thus every displayed
factor sends the stated generator tensor to the stated generator tensor,
with the right and left unitors at exponent zero. This proves equality
with the tensorPowAddIso product on the right. A change of lift changes a
by an element of J; its product with r vanishes since J^2=0. The local
equalities agree on overlaps and give the asserted equality on U, including
n=0, e=0, the zero section, the zero ideal and the empty open. -/
theorem tensorBoundaryKernelMap_local_multiplication {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n e : ℕ)
    (x : 𝟙_ Z.Modules ⟶ (((tensorPullback j).obj L).tensorPow n).tensorPow (e + 1))
    (U : X.Opens) (t : Γ(L.tensorPow (n * (e + 1)), U))
    (ht : (tensorGradedUnit j (L.tensorPow (n * (e + 1)))).app U t =
      ((pushforward j).obj ((tensorPullback j).obj (L.tensorPow (n * (e + 1))))).val.map
        (homOfLE le_top).op
          ((x ≫ (boundarySectionDegreeIso j L n e).inv).app ⊤ (1 : Γ(Z, ⊤))))
    (y : Γ(kernel (tensorGradedUnit j (L.tensorPow (n * (0 + 1)))), U)) :
    let F : Z.Modules := (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n)
    (kernel.ι (tensorGradedUnit j (L.tensorPow (n * ((e + 1) + 1))))).app U
        ((tensorBoundaryKernelMap j L hI n 0 (e + 1) (F ◁ x)).app U y) =
      (eqToHom (by congr 1; simp only [Nat.mul_add, Nat.mul_one, Nat.zero_add]) :
        L.tensorPow (n * (e + 1) + n * (0 + 1)) ⟶
          L.tensorPow (n * ((e + 1) + 1))).app U
        ((L.tensorPowAddIso (n * (e + 1)) (n * (0 + 1))).inv.app U
          (tmulSection t
            ((kernel.ι (tensorGradedUnit j (L.tensorPow (n * (0 + 1))))).app U y))) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
