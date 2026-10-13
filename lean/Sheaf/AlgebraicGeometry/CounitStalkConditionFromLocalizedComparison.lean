/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition

/-! # Stalk condition of the universal pullback counit

Source: Stacks Project, perfect.tex, equation-bc preceding Tag 0DJ8.
(blueprint: lem-pc-counit-stalk-condition-from-localized-comparison).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange

/-- The localized tensor comparison on the original complex suffices for the
coordinate-independent stalk condition of its universal pullback counit.

Source: Stacks Project, perfect.tex, equation-bc preceding Tag 0DJ8.
Proof: fix K-flat coordinates c for the counit and a point z. The representing
identity of c identifies its chain map, after localization, with the universal
pullback counit on the original complex G. Exactness of stalks transports the
representative isomorphisms c.e and c.e' to cohomology isomorphisms. The universal
left-derived counit equations in cohomologyModel identify the source comparison
computed on c.P with that computed on G, by functoriality of derived scalar
extension and the isomorphism c.e. The degreewise tensorStalkIso identifies the
ordinary scalar-extension target with the stalk of tensorPullback G. Naturality
of these identifications and c.represents show that stalkComparison c is the
localizedComparison for G conjugated by these source and target isomorphisms.
Thus its invertibility follows from the hypothesis for every z and i. This
argument uses only the canonical maps, and applies also to acyclic or unbounded G.
(blueprint: lem-pc-counit-stalk-condition-from-localized-comparison). -/
theorem counit_stalkCondition_of_localizedComparison
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (h : ∀ z : X',
      letI := leftAlgebra f g' z
      letI := rightAlgebra f f' g g' sq z
      letI := (tensorMap f f' g g' sq z).toAlgebra
      letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
      letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
      ∀ i : ℤ, IsIso ((cohomologyModel f f' g g' sq z G).localizedComparison i)) :
    StalkCondition f f' g g' sq (DerivedCategory.Q.obj G)
      (DerivedCategory.Q.obj
        (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj G))
      ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj G)) := by sorry

end AlgebraicGeometry.SingleComplexBaseChange
