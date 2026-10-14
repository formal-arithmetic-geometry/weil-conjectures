/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedMateEvaluation
public import Sheaf.AlgebraicGeometry.TensorCoefficientComparison
public import Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
import Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComposition

/-! # Composition of tensor coefficient single-pullback comparisons
Source: Stacks Project, Tag 0D5S.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
universe v
open CategoryTheory
namespace AlgebraicGeometry
noncomputable section

variable [∀ Y : Scheme.{v},
  HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]

/-- The single-complex coefficient morphism of a commuting triangle.
It uses the fixed ordinary-to-tensor identification, without inverting the
single-pullback map. Source: Stacks Project, Tags 0096 and 0D5S.
(blueprint: def-sc-tensor-single-coefficient-map) -/
@[irreducible]
def tensorSingleCoefficientMap {A B X : Scheme.{v}}
    (q : A ⟶ X) (q1 : B ⟶ X) (a : B ⟶ A) (h : a ≫ q = q1)
    (L : X.Modules) :
    (derivedPullback a).obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings A.toRingedSpace)) 0).obj
        ((Scheme.Modules.tensorPullback q).obj L)) ⟶
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings B.toRingedSpace)) 0).obj
          ((Scheme.Modules.tensorPullback q1).obj L) :=
  Scheme.Modules.canonicalSinglePullbackMap a ((Scheme.Modules.tensorPullback q).obj L) ≫
    (DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings B.toRingedSpace)) 0).map
        (Scheme.Modules.tensorCoefficientComparison q q1 a h L).hom

/-- Defining equation of the single-complex coefficient morphism.
Source: Stacks Project, Tags 0096 and 0D5S.
(blueprint: def-sc-tensor-single-coefficient-map) -/
theorem tensorSingleCoefficientMap_eq {A B X : Scheme.{v}}
    (q : A ⟶ X) (q1 : B ⟶ X) (a : B ⟶ A) (h : a ≫ q = q1)
    (L : X.Modules) :
    tensorSingleCoefficientMap q q1 a h L =
      Scheme.Modules.canonicalSinglePullbackMap a ((Scheme.Modules.tensorPullback q).obj L) ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings B.toRingedSpace)) 0).map
            (Scheme.Modules.tensorCoefficientComparison q q1 a h L).hom := by
  delta tensorSingleCoefficientMap
  rfl

/-- Coefficient comparisons compose, before any direct image or base-change mate.
Source: Stacks Project, Tag 0D5S; step 3 of
lem-sc-picard-coefficient-transpose-pasting.
(blueprint: lem-sc-tensor-single-pullback-composition)

Proof: Apply canonicalSinglePullbackComposition to b,a and the module
q tensor-pullback L. Naturality of the single-pullback comparison moves the
single embedding of d1 through the b comparison. The remaining underived
identity says pullbackComp(b,a), transport along hab, and d3 equal the
pullback of d1 followed by d2. Transpose that identity under the composed
ordinary pullback adjunctions and the selected tensor adjunctions. The
leftAdjointUniq counit identities cancel the ordinary-to-tensor comparisons.
The definition of each c as the conjugate of pushforwardComp then reduces
the equality to associativity of pushforward composition, with transports
along h1,h2,h3. These transports agree by hab and proof irrelevance.
Injectivity of the adjunction equivalences proves the underived identity;
map it by the single functor and substitute in the derived composition
formula. No single comparison is inverted. Thus zero modules, identity
morphisms and empty schemes require no special hypotheses. -/
theorem tensorSinglePullback_composition
    {A B C X : Scheme.{v}} (q : A ⟶ X) (q1 : B ⟶ X) (q2 : C ⟶ X)
    (a : B ⟶ A) (b : C ⟶ B) (a' : C ⟶ A)
    (h1 : a ≫ q = q1) (h2 : b ≫ q1 = q2) (h3 : a' ≫ q = q2)
    (hab : b ≫ a = a') (L : X.Modules) :
  let d1 := Scheme.Modules.tensorCoefficientComparison q q1 a h1 L
  let d2 := Scheme.Modules.tensorCoefficientComparison q1 q2 b h2 L
  let d3 := Scheme.Modules.tensorCoefficientComparison q q2 a' h3 L
  let M := (Scheme.Modules.tensorPullback q).obj L
  let N := (Scheme.Modules.tensorPullback q1).obj L
  let K := (DerivedCategory.singleFunctor
    (SheafOfModules.{v} (moduleRings A.toRingedSpace)) 0).obj M
  (derivedPullback b).map (Scheme.Modules.canonicalSinglePullbackMap a M ≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings B.toRingedSpace)) 0).map d1.hom) ≫
    Scheme.Modules.canonicalSinglePullbackMap b N ≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings C.toRingedSpace)) 0).map d2.hom =
  (canonicalDerivedPullbackComposition b a ≪≫
    eqToIso (congrArg (fun r ↦ derivedPullback r) hab)).hom.app K ≫
      (Scheme.Modules.canonicalSinglePullbackMap a' M ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings C.toRingedSpace)) 0).map d3.hom) := by sorry

/-- Composition API for the fixed single-complex coefficient morphisms.
Source: Stacks Project, Tag 0D5S.
(blueprint: lem-sc-tensor-single-pullback-composition)
Proof: unfold only the coefficient-morphism wrapper and apply the recorded
coefficient composition theorem. The generic schemes stay as parameters. -/
theorem tensorSingleCoefficientMap_composition
    {A B C X : Scheme.{v}} (q : A ⟶ X) (q1 : B ⟶ X) (q2 : C ⟶ X)
    (a : B ⟶ A) (b : C ⟶ B) (a' : C ⟶ A)
    (h1 : a ≫ q = q1) (h2 : b ≫ q1 = q2) (h3 : a' ≫ q = q2)
    (hab : b ≫ a = a') (L : X.Modules) :
    (derivedPullback b).map (tensorSingleCoefficientMap q q1 a h1 L) ≫
      tensorSingleCoefficientMap q1 q2 b h2 L =
    (canonicalDerivedPullbackComposition b a ≪≫
      eqToIso (congrArg (fun r ↦ derivedPullback r) hab)).hom.app
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings A.toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback q).obj L)) ≫
      tensorSingleCoefficientMap q q2 a' h3 L := by
  delta tensorSingleCoefficientMap
  exact tensorSinglePullback_composition q q1 q2 a b a' h1 h2 h3 hab L

end
end AlgebraicGeometry
