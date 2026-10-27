/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PointTateFiberComparisonData

/-! # Normalized signed section generators at the geometric point

Source: coefficient comparison lemma, steps 1--3.
(blueprint: lem-pur-point-tate-normalized-section-generators).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] AlgebraicGeometry.Scheme.residueLisseAlgebraHasDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ChangeOfRings TensorProduct
namespace WeilConjectures.PointTateFiber

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]

/-- The prescribed roots give generators of all integral section lines, compatible with
positive finite reduction and the canonical signed scalar maps.

Source: the coefficient comparison lemma, steps 1--3; Deligne, Weil I (2.2),
pp. 280--281, and Weil II (1.1.3), p. 150.
(blueprint: lem-pur-point-tate-normalized-section-generators).

Proof: define the root tuple by evaluating the given section at each tower level.
The limit equations imply compatibility of successive roots. Apply
`point_tate_root_coordinates` at every coefficient field with this tuple. Its
normalized completed basis has image of one equal to the given section: project
to every root level, use its root formula on one, and use injectivity of Spec's
section identification, then the universal property of the inverse limit.
The integral coordinate in degree one is therefore the prescribed root tensor.
Tensor recursion identifies every nonnegative coordinate with positiveGenerator,
including the coefficient unit in degree zero. In negative degree take the dual
coordinate; its evaluation on the corresponding positive generator is one.
The final section clause of root coordinates makes a ↦ a times this generator
bijective. For finite reduction, use the zero and degree-one formulas of
signedTwistReduction_comparison and induct on tensor powers. For scalar extension,
the root tensor formula and tensor recursion preserve the positive generators.
The normalized evaluation formula preserves negative generators as well, since
on the target positive basis a functional is determined by its value on one.
All generators in this argument use the same initial root section. -/
theorem normalizedSectionGenerators (hl : l ≠ D.p)
    (e : (purTwistZlOne (Spec (.of D.k)) l).obj.obj (finalObject D))
    (he : ∀ r : ℕ, IsPrimitiveRoot
      (rootValue D (l ^ (r + 1))
        ((limit.π (proEtaleRootsOfUnityTower (Spec (.of D.k)) l Fact.out) (op r)).hom.app
          (finalObject D) e)) (l ^ (r + 1))) :
    ∃ (g : ∀ (F : Type u) [Field F] [Algebra (Padic l) F]
        [FiniteDimensional (Padic l) F] (m : ℤ), integral D l F m),
    (∀ (F : Type u) [Field F] [Algebra (Padic l) F]
        [FiniteDimensional (Padic l) F] (r : ℕ),
      g F (r : ℤ) = positiveGenerator D l F e r) ∧
    (∀ (F : Type u) [Field F] [Algebra (Padic l) F]
        [FiniteDimensional (Padic l) F] (r : ℕ),
      integralEvaluate D l F r (g F (Int.negSucc r))
        (positiveGenerator D l F e (r + 1)) = 1) ∧
    (∀ (F : Type u) [Field F] [Algebra (Padic l) F]
        [FiniteDimensional (Padic l) F] (n r : ℕ),
      (reduction D l F hl n (r : ℤ)).val.app (finalObject D) (g F (r : ℤ)) =
        finiteTateProPowerGenerator l F n (Spec (.of D.k)) (finalObject D) 1 r
          (fun _ ↦ e)) ∧
    (∀ (F : Type u) [Field F] [Algebra (Padic l) F]
        [FiniteDimensional (Padic l) F] (L : Type u) [Field L] [Algebra (Padic l) L]
        [FiniteDimensional (Padic l) L] (ι : F →ₐ[Padic l] L) (m : ℤ),
      (scalarMap D l F hl L ι m).val.app (finalObject D) (g F m) = g L m) := by sorry

end WeilConjectures.PointTateFiber
