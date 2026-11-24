/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.ExactRestrictionComposition
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.SecSmoothPurity.CochainCoefficientArrows

/-! # Definition interface for simultaneous strict coefficient comparisons

The data of a diagram of coefficient rings indexed by three coefficient rows and an inverse
sequence, together with the scalar-extension functors along a common geometric morphism.

## Implementation details

The product index records coefficient changes and all inverse-sequence arrows.
Semilinear arrows are written in their scalar-extension adjoint form. Thus they
are arbitrary chain maps out of scalar extension, including zero maps, rather
than only the scalar-extension units. All tensors are the existing sheafified
module tensor and its signed direct-sum total complex.

## References

* Stacks 03EL, 07A4
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local irreducible] SheafOfModules.cochainModulesMonoidal
attribute [local irreducible] CategoryTheory.CochainPullback.extensionAdjunction
attribute [local irreducible] CategoryTheory.CochainPullback.extensionFunctor
set_option maxErrors 1
universe w uC vC uD vD
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace CategoryTheory.CochainPullback.StrictCoefficient

/-- Three coefficient rows and an inverse sequence, with all iterated arrows. -/
abbrev Index := Fin 3 × ℕᵒᵖ

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The signed direct-sum total tensor product of two complexes. -/
noncomputable def total {R : Sheaf J CommRingCat.{w}} (P Q : Complex R) : Complex R := by
  let : ∀ (I₁ I₂ : Type w), HasColimitsOfShape (Discrete I₂)
      (PresheafOfModules.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj) :=
    fun _ _ ↦ PresheafOfModules.hasColimitsOfShape _ _
  let : HasCoproducts.{0} (Modules R) := fun I ↦ by
    let : HasColimitsOfShape (Discrete I) (PresheafOfModules.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj) :=
      PresheafOfModules.hasColimitsOfShape _ _
    exact
      SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf _ _
  let : HasFiniteCoproducts (Modules R) :=
    hasFiniteCoproducts_of_hasCoproducts (C := Modules R)
  exact P ⊗ Q

/-- The tensor product of two maps of complexes, as a map of total complexes. -/
abbrev totalMap {R : Sheaf J CommRingCat.{w}} {P Q P' Q' : Complex R}
    (f : P ⟶ P') (g : Q ⟶ Q') : total P Q ⟶ total P' Q' := by
  let : ∀ (I₁ I₂ : Type w), HasColimitsOfShape (Discrete I₂)
      (PresheafOfModules.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj) :=
    fun _ _ ↦ PresheafOfModules.hasColimitsOfShape _ _
  let : HasCoproducts.{0} (Modules R) := fun I ↦ by
    let : HasColimitsOfShape (Discrete I) (PresheafOfModules.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj) :=
      PresheafOfModules.hasColimitsOfShape _ _
    exact
      SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf _ _
  let : HasFiniteCoproducts (Modules R) :=
    hasFiniteCoproducts_of_hasCoproducts (C := Modules R)
  exact f ⊗ₘ g

/-- A diagram of coefficient rings on two sites indexed by `Index`, related by algebraic
inverse images along one geometric morphism, together with the scalar-extension functors `L`
(identified with change of rings after inverse image by `hobj` and `hmap`) and their right
adjoints `V`. -/
structure Diagram where
  R : Index ⥤ Sheaf J CommRingCat.{w}
  S : Index ⥤ Sheaf K CommRingCat.{w}
  RI : Index ⥤ Sheaf K CommRingCat.{w}
  phi : RI ⟶ S
  inverse : Sheaf J (Type w) ⥤ Sheaf K (Type w)
  direct : Sheaf K (Type w) ⥤ Sheaf J (Type w)
  adj : inverse ⊣ direct
  finiteLimits : PreservesFiniteLimits inverse
  algebraic : ∀ i : Index, SheafOfModules.AlgebraicInverseImage inverse (R.obj i) (RI.obj i)
  graph : ∀ {i j : Index} (t : i ⟶ j),
    inverse.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map (R.map t)) ≫
        (algebraic j).ringUnderlying.hom =
      (algebraic i).ringUnderlying.hom ≫
        (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map (RI.map t)
  L : ∀ i : Index, Modules (R.obj i) ⥤ Modules (S.obj i)
  hobj : ∀ (i : Index) (M : Modules (R.obj i)),
    (L i).obj M = SheafOfModules.changeOfRings (phi.app i) ((algebraic i).modules.obj M)
  hmap : ∀ (i : Index) {M N : Modules (R.obj i)} (f : M ⟶ N),
    (L i).map f = eqToHom (hobj i M) ≫
      SheafOfModules.changeOfRingsHom (phi.app i) ((algebraic i).modules.obj M)
        ((algebraic i).modules.map f) ≫ eqToHom (hobj i N).symm
  V : ∀ i : Index, Modules (S.obj i) ⥤ Modules (R.obj i)
  moduleAdj : ∀ i : Index, L i ⊣ V i
  additive : ∀ i : Index, (L i).Additive

attribute [instance] Diagram.additive

variable (d : Diagram (J := J) (K := K))

variable {d}

end CategoryTheory.CochainPullback.StrictCoefficient
