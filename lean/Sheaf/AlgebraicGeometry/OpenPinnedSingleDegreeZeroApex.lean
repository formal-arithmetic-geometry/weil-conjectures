/- Copyright (c) 2026 The SHEAF contributors. -/
module
public import Sheaf.AlgebraicGeometry.PinnedSingleBaseChangeShift

/-! # Invariance of the pinned single comparison under an isomorphic apex
Source: Stacks Project, Tags 08HY and 08IB.
(blueprint: lem-pc-open-pinned-single-degree-zero-apex). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry

/-- Changing only the apex of a commutative square by an isomorphism preserves the
pinned single-complex comparison. This statement has no open-restriction data.
Source: Stacks Project, Tags 08HY and 08IB.
(blueprint: lem-pc-open-pinned-single-degree-zero-apex).
Proof: transport tensor pullback along the apex isomorphism, using uniqueness of
left adjoints to the composite pushforward. Tensor pullback along an isomorphism
is an exact equivalence. Its single-complex comparison is therefore invertible.
Derive the pushforward composition comparison and combine it with this single
comparison to construct v. Transpose base change under the pinned derived
adjunctions. The composition comparisons are pinned to the same counits; their
associativity identifies both transposes. The counit factorization equation then
identifies the final single tensor comparisons. Naturality assembles these
component equalities into the displayed functor isomorphism. No flatness,
properness or nonemptiness assumptions enter. -/
theorem open_pinned_single_degree_zero_apex
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X S Z P T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (j : Z ⟶ X) (r : Z ⟶ T) (p : P ⟶ X) (q : P ⟶ T)
    (h : j ≫ f = r ≫ g) (hP : p ≫ f = q ≫ g)
    (e : Z ≅ P) (hj : e.hom ≫ p = j) (hr : e.hom ≫ q = r) :
    ∃ v : singleDegreeBaseChangeTarget.{u, w} j r 0 ≅
        singleDegreeBaseChangeTarget.{u, w} p q 0,
      ∀ M : X.Modules,
        singleDegreeBaseChangeComposite f g j r h 0 M ≫ v.hom.app M =
          singleDegreeBaseChangeComposite f g p q hP 0 M := by sorry

end AlgebraicGeometry
