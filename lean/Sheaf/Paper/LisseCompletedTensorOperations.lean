/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B6
-/
module

public import Sheaf.Paper.LisseCompletedSystemData

/-! # Normalized tensor operations on completed lisse modules. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CompletedLisse
variable (l : ℕ) [Fact l.Prime]

/-- The tensor pullbacks and scalar extensions, with their canonical ambient-module
identity/composition maps. Reconstruction is the counit mate of reduction.
Source: BS 6.8.4(1),(4), Weil II (1.1.1) d)
(blueprint: lem-per-lisse-completed-tensor-operations). -/
structure TensorOperations (c : ∀ P : Base.{u} l, Comparison l P) where
  operation {P Q : Base.{u} l} (a : Arrow l P Q) :
    Operation l a (c P) (c Q)
  integralId (P : Base.{u} l) : (operation (identity l P)).modules.integral ≅ 𝟭 _
  rationalId (P : Base.{u} l) : (operation (identity l P)).modules.rational ≅ 𝟭 _
  integralId_normalization (P : Base.{u} l) (M : Integral l P) :
    (operation (identity l P)).modules.integralUnit l M ≫
      (proEtaleSheafDirectImage (𝟙 P.X) AddCommGrpCat.{u + 1}).map
        ((integralForget l P).map ((integralId P).hom.app M).hom) ≫
      (lowerStarId AddCommGrpCat.{u + 1} P.X).hom.app ((integralForget l P).obj M.obj) = 𝟙 _
  rationalId_normalization (P : Base.{u} l) (M : Rational l P) :
    (operation (identity l P)).modules.rationalUnit l M ≫
      (proEtaleSheafDirectImage (𝟙 P.X) AddCommGrpCat.{u + 1}).map
        ((rationalForget l P).map ((rationalId P).hom.app M).hom) ≫
      (lowerStarId AddCommGrpCat.{u + 1} P.X).hom.app ((rationalForget l P).obj M.obj) = 𝟙 _
  integralComp {P Q S : Base.{u} l} (a : Arrow l P Q) (b : Arrow l Q S) :
    (operation a).modules.integral ⋙ (operation b).modules.integral ≅
      (operation (composite l a b)).modules.integral
  rationalComp {P Q S : Base.{u} l} (a : Arrow l P Q) (b : Arrow l Q S) :
    (operation a).modules.rational ⋙ (operation b).modules.rational ≅
      (operation (composite l a b)).modules.rational
  integralComp_normalization {P Q S : Base.{u} l}
      (a : Arrow l P Q) (b : Arrow l Q S) (M : Integral l P) :
    (operation a).modules.integralUnit l M ≫
      (proEtaleSheafDirectImage a.scheme AddCommGrpCat.{u + 1}).map
        ((operation b).modules.integralUnit l ((operation a).modules.integral.obj M)) ≫
      (lowerStarComp AddCommGrpCat.{u + 1} b.scheme a.scheme).hom.app
        ((integralForget l S).obj
          ((operation b).modules.integral.obj ((operation a).modules.integral.obj M)).obj) ≫
      (proEtaleSheafDirectImage (b.scheme ≫ a.scheme) AddCommGrpCat.{u + 1}).map
        ((integralForget l S).map ((integralComp a b).hom.app M).hom) =
      (operation (composite l a b)).modules.integralUnit l M
  rationalComp_normalization {P Q S : Base.{u} l}
      (a : Arrow l P Q) (b : Arrow l Q S) (M : Rational l P) :
    (operation a).modules.rationalUnit l M ≫
      (proEtaleSheafDirectImage a.scheme AddCommGrpCat.{u + 1}).map
        ((operation b).modules.rationalUnit l ((operation a).modules.rational.obj M)) ≫
      (lowerStarComp AddCommGrpCat.{u + 1} b.scheme a.scheme).hom.app
        ((rationalForget l S).obj
          ((operation b).modules.rational.obj ((operation a).modules.rational.obj M)).obj) ≫
      (proEtaleSheafDirectImage (b.scheme ≫ a.scheme) AddCommGrpCat.{u + 1}).map
        ((rationalForget l S).map ((rationalComp a b).hom.app M).hom) =
      (operation (composite l a b)).modules.rationalUnit l M
  reconstruction_mate {P Q : Base.{u} l} (a : Arrow l P Q) (F : Systems l P) :
    (c Q).equivalence.functor.map ((operation a).reconstruction.hom.app F) ≫
        (c Q).equivalence.counitIso.hom.app ((operation a).etale.functor.obj F) =
      (operation a).reduction.hom.app ((c P).equivalence.inverse.obj F) ≫
        (operation a).etale.functor.map ((c P).equivalence.counitIso.hom.app F)

/-- Tensor pullback and finite extension admit the normalized reduction, reconstruction
and localization comparisons, together with the canonical tensor identity/composition maps.
Source: Bhatt--Scholze, Proposition 6.8.4(1),(4) and Weil II (1.1.1) d)
(blueprint: lem-per-lisse-completed-tensor-operations).

Proof: Define the continuous-coefficient homomorphisms by coefficient inclusion and
precomposition on sections. Define the completed-ring map by transport through the
coefficient isomorphisms; the residue and localization equations follow on sections.
Take the sheafified tensor pullback, left adjoint to the specified ringed direct image.
On a local basis it preserves finite freeness; restrict it to the lisse subcategories.
At finite level apply the stated etale inverse image and scalar extension, reindexed by
the ramification ceiling. The quotient coefficient maps give its transitions, and send
x to 1 tensor x. These towers are normalized and finite free by the same local bases.
The site-comparison adjunction mate identifies these maps with proEtaleUnit.
Reduction commutes with these tensor operations: on generators the comparison sends
b tensor x to bar(b) tensor bar(x). A compatible local basis proves invertibility.
The inverse-limit map is the map induced by those residue projections, and is invertible
on that basis. Projection uniqueness gives its normalization and the counit-mate equation;
indeed both sides have the same composite with every residue projection after applying
the adjunction unit. No preservation of arbitrary inverse limits is asserted.
Define raw rational extension by its pure-tensor formula. The balancing relations,
additivity and functor laws follow from coefficient linearity. Localizing the integral
tensor comparison gives the rational comparison and its displayed normalization.
Finally use the canonical tensor isomorphisms b tensor x ↦ bx and
c tensor (b tensor x) ↦ cb tensor x for identity and composition. Their composites with
the specified adjunction units agree on all generators, yielding the four normalization
fields, also for mixed operations and ramified extensions. These computations include
zero modules and empty schemes. No coherence maps on the tower or raw categories are
chosen here: those are obtained separately by categorical full faithfulness. -/
theorem completed_tensor_operations (c : ∀ P : Base.{u} l, Comparison l P) :
    Nonempty (TensorOperations l c) := by sorry

end AlgebraicGeometry.ProEtale.CompletedLisse
