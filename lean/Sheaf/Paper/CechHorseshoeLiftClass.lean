/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.ModuleCechComparison

/-! # The local correction in a horseshoe Cech double complex

Source: Stacks Project, Cohomology, Tag 01EQ (total-complex calculation),
and Tag 0B8S (local lifts).
(blueprint: lem-sc-cech-horseshoe-lift-class).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- The images of the local difference cocycle and the global horseshoe cycle agree
in total homology. This is a calculation about alpha and beta, without a cohomology
boundary or a canonical comparison map.
Source: Stacks Project, Cohomology, Tag 01EQ, double-complex proof, and Tag 0B8S.
(blueprint: lem-sc-cech-horseshoe-lift-class).

Proof:
1. On each U_i, aug_B(x_i) minus the restriction of b maps under beta^0 to zero:
the augmentation square, the local lift equation and beta^0(b) = aug_C(q) give this.
Since alpha^0 is a kernel on sections, it lifts uniquely to t_i in IA^0(U_i).
2. On each pairwise intersection, naturality and the augmentation square for alpha
show that the Cech differential of (t_i) is the image of z under aug_A. Cancellation
of the two restrictions of b removes b. Monicity of alpha^0 verifies the equality.
3. The resolution differential of t_i equals minus a restricted to U_i. Apply alpha^1:
d(aug_B(x_i)) = 0 and d(b) = alpha^1(a); then cancel alpha^1, which is monic.
4. Regard (t_i) as the (0,0) summand of the total complex. Its total differential is
beta_A(iCycles z) minus alpha_A(iCycles a), since both signs leaving (0,0) are +1.
A total coboundary has zero homology class, so H(beta_A)[z] = H(alpha_A)[a].
Empty intersections and an empty indexing type cause no exceptions: products and
sectionwise kernel arguments still apply, and all empty products are zero modules. -/
theorem cech_horseshoe_lift_class (X : Scheme.{u})
    (S : ShortComplex X.Modules)
    (IA : InjectiveResolution S.X₁) (IB : InjectiveResolution S.X₂)
    (IC : InjectiveResolution S.X₃)
    (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex)
    (hαβ : α ≫ β = 0)
    (hιA : IA.ι ≫ α = (CochainComplex.single₀ X.Modules).map S.f ≫ IB.ι)
    (hιB : IB.ι ≫ β = (CochainComplex.single₀ X.Modules).map S.g ≫ IC.ι)
    (hrows : ∀ k : ℕ, ((ShortComplex.mk α β hαβ).map
      (HomologicalComplex.eval X.Modules (ComplexShape.up ℕ) k)).ShortExact)
    {ι : Type u} (U : ι → X.Opens)
    (q : S.X₃.val.obj (op ⊤)) (x : ∀ i : ι, S.X₂.val.obj (op (U i)))
    (hx : ∀ i : ι, S.g.val.app (op (U i)) (x i) =
      S.X₃.val.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op q)
    (b : (IB.cocomplex.X 0).val.obj (op ⊤))
    (a : (RingedSpace.globalSectionsComplex IA).cycles 1)
    (hb : (β.f 0).val.app (op ⊤) b = (IC.ι.f 0).val.app (op ⊤) q)
    (ha : (α.f 1).val.app (op ⊤)
      ((RingedSpace.globalSectionsComplex IA).iCycles 1 a) =
        (IB.cocomplex.d 0 1).val.app (op ⊤) b)
    (z : ((cechComplexFunctor U).obj S.X₁.presheafModuleCat).cycles 1)
    (hz : ∀ y : Fin 2 → ι,
      S.f.val.app (op (∏ᶜ fun k : Fin 2 ↦ U (y k)))
        ((Pi.π (fun w : Fin 2 → ι ↦
          S.X₁.presheafModuleCat.obj (op (∏ᶜ fun k : Fin 2 ↦ U (w k)))) y)
          (((cechComplexFunctor U).obj S.X₁.presheafModuleCat).iCycles 1 z)) =
        S.X₂.val.presheaf.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 1).op (x (y 1)) -
          S.X₂.val.presheaf.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 0).op (x (y 0))) :
    HomologicalComplex.homologyMap (moduleCechBeta U IA) 1
      (((cechComplexFunctor U).obj S.X₁.presheafModuleCat).homologyπ 1 z) =
        HomologicalComplex.homologyMap (moduleCechAlpha U IA) 1
          ((RingedSpace.globalSectionsComplex IA).homologyπ 1 a) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
