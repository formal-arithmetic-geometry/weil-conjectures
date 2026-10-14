/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.AlgebraicGeometry.RelativeMVMaps
public import Sheaf.AlgebraicGeometry.MayerVietorisImageChainData
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Algebra.Homology.KFlatClosure
import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-! # Derived transposition of a specified cone square -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Transpose a specified cone-square through derived pullback/direct image.
This is independent of open covers and of base-change comparison maps.
Source: Stacks Project, Cohomology, Tags 06YI and 06YJ (K-flat computations),
079W (derived adjunction), and Derived Categories, Tag 014P (cone formulas).
(blueprint: lem-pc-derived-pullback-cone-square-transposition).

Proof: Choose a K-flat resolution Q -> B. Represent the composite of Q(t)
with the inverse localized resolution by a right fraction out of A. Refine
its denominator until the resulting square commutes in the homotopy category,
then replace its source by a K-flat resolution P. This yields a homotopy
square from P -> Q to A -> B whose vertical maps are quasi-isomorphisms.
Its specified cone comparison is a quasi-isomorphism by the cone triangle.
The two replacement vertices and their cone are K-flat. Precompose alpha and
beta with the replacement and compose its square homotopy with H. Use the
underived tensor-pullback/direct-image adjunction to transpose these two chain
maps and the degree-minus-one cochain of H. The adjunction is additive and commutes with
differentials, so its
transpose is a homotopy H' for the resulting square. Termwise tensor pullback
commutes with mapping cones. Hence transposing the two-component formula for
mapOfHomotopy H gives exactly mapOfHomotopy H', including its sign. The K-flat
counit identifies the localized two source complexes and cone with Lg* Q(A),
Lg* Q(B) and Lg* Q(Cone t), giving d1,d2,d3. The canonical derived adjunction
is obtained from this underived adjunction and the left-derived counit and
right-derived unit. Its homEquiv therefore identifies each localized chain
transpose with the displayed transpose of Q(alpha) eta, Q(beta) eta, and the
specified cone map followed by eta. The cone comparison for the additive
direct-image functor accounts for its inverse in the third formula. Comparing
with relativeMVAdj uses uniqueness with those pinned units and counits.
The construction permits arbitrary complexes and homotopies, without bounds,
flatness of g or K-injectivity of A',B'. Zero complexes and the zero homotopy
are covered by the same additive construction. -/
theorem derivedPullback_cone_square_transposition
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {S S' : Scheme.{u}} (g : S' ⟶ S)
    (A B : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
    (A' B' : CochainComplex (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ)
    (t : A ⟶ B) (t' : A' ⟶ B') :
    let G := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
    let F := G.mapHomologicalComplex (.up ℤ)
    let η := schemeMVDirectImageLocalization g
    let adj := relativeMVAdj g
    ∀ (α : A ⟶ F.obj A') (β : B ⟶ F.obj B')
      (H : Homotopy (t ≫ β) (α ≫ F.map t')),
    ∃ (C D : CochainComplex
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ)
      (s : C ⟶ D) (a : C ⟶ A') (b : D ⟶ B')
      (H' : Homotopy (s ≫ b) (a ≫ t'))
      (d₁ : DerivedCategory.Q.obj C ≅ (derivedPullback g).obj (DerivedCategory.Q.obj A))
      (d₂ : DerivedCategory.Q.obj D ≅ (derivedPullback g).obj (DerivedCategory.Q.obj B))
      (d₃ : DerivedCategory.Q.obj (CochainComplex.mappingCone s) ≅
        (derivedPullback g).obj (DerivedCategory.Q.obj (CochainComplex.mappingCone t))),
      DerivedCategory.Q.map a =
        d₁.hom ≫ (adj.homEquiv _ _).symm (DerivedCategory.Q.map α ≫ η.app A') ∧
      DerivedCategory.Q.map b =
        d₂.hom ≫ (adj.homEquiv _ _).symm (DerivedCategory.Q.map β ≫ η.app B') ∧
      DerivedCategory.Q.map (CochainComplex.mappingCone.mapOfHomotopy H') =
        d₃.hom ≫ (adj.homEquiv _ _).symm
          (DerivedCategory.Q.map (CochainComplex.mappingCone.mapOfHomotopy H ≫
            (CochainComplex.mappingCone.mapHomologicalComplexIso t' G).inv) ≫
              η.app (CochainComplex.mappingCone t')) := by sorry

end AlgebraicGeometry
