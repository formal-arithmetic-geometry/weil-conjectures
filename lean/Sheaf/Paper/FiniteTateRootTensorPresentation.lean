/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import Sheaf.Paper.FiniteTateSiteDescentDefinitions
public import Sheaf.AlgebraicGeometry.FiniteRootSiteComparison

/-! # Fixed-scalar presentation of the finite root projection

Source: Stacks Project, Tags 03CY, 03EK and 03PK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.Scheme

-- Pin the existing coefficient-size instances to avoid an unconstrained maximum universe.
local instance (T : Scheme.{u}) :
    HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} T
local instance (T : Scheme.{u}) :
    HasSheafify (ProEt.topology T) CommRingCat.{u + 1} :=
  integralCoefficientRingSheafify.{u, u} T
local instance (T : Scheme.{u}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} T
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (n : ℕ)

/-- The root projection identifies the first finite coefficient twist with the
fixed-scalar extension of the finite roots module, retaining its tensor formula.
Source: Stacks 03CY, 03EK and 03PK; the first step of
`lem-amb-finite-tate-normalized-comparisons`.
(blueprint: lem-amb-finite-tate-root-tensor-presentation).

Proof: map the global unit hypothesis to each stalk, and lower the annihilation
identity along `ULift.down`. Apply `ambTateRootProjectionReduction` at this base
and level. Restrict its theta to constant coefficients. Identify restriction of
`ambTateFiniteRoots` with `finiteRootProTensor`: both represent balanced maps from
A and the finite root module. On constants their balancing maps agree, since maps
from Z/l^(r+1) are unique. Locally every section of a constant scalar sheaf is a
constant, so the fixed and sheaf-ring balancing relations agree after sheafification.
The two induced tensor maps are inverse on all pure tensors, hence inverse globally.
Reassociation `j_pure` at the integral scalar 1 and `theta_pure` give the asserted
formula. No chosen primitive root or infinite-root lift is needed, and the argument
applies to the empty scheme and every annihilated coefficient quotient. -/
theorem finite_tate_root_tensor_presentation (T : Scheme.{u})
    (hT : IsUnit (l : Γ(T, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) :
    ∃ e : finiteTateProSheaf l E n T 1 ≅
      finiteRootProTensor (finiteTateCoefficient l E n) (l ^ (r + 1))
        (pow_pos (Fact.out : l.Prime).pos _) hA T,
      ∀ (W : T.ProEtᵒᵖ) (a : finiteTateCoefficient l E n)
        (x : (purTwistZlOne T l).obj.obj W),
        e.hom.hom.app W (finiteTateProGenerator l E n T W a x) =
          finiteRootProGenerator (finiteTateCoefficient l E n) (l ^ (r + 1))
            (pow_pos (Fact.out : l.Prime).pos _) hA T W a
            ((limit.π (proEtaleRootsOfUnityTower T l (Fact.out : l.Prime))
              (op r)).hom.app W x) := by sorry

end AlgebraicGeometry.Scheme
