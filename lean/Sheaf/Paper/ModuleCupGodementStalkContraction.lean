/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Sheaf.Paper.ModuleCupGodementModel
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Algebra.Homology.Homotopy

/-! # Exactness of Godement models -/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace AlgebraicTopology Simplicial
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Each stalk of the actual Godement model has a contracting augmented complex.
Source: Stacks Project, Tag 0FKR, Lemma 20.30.1 (0FKS).
(blueprint: lem-sc-module-cup-godement-stalk-contraction)
Proof: fix x. Project T(H) to the skyscraper of H_x, apply the module stalk
functor at x, and then apply skyscraperStalkEval. This defines e_H:(T(H))_x to H_x.
The product germ unit followed by e_H is the identity, by the stalk-skyscraper
adjunction. Evaluation is natural in H, so for every inner unit-insertion face
e_H commutes with it with its index shifted down by one. For the outer face,
evaluation following insertion is the identity. Transport these equations
through the term equalities of ModuleCupGodementModel. Alternating the cofaces
then gives d h+h d=id in positive degrees. In degree zero it gives
h d=id-a r, where r is e_F after the degree-zero identifications. Also r a=id
and r is a chain map to F_x[0]. Set all maps in negative degrees to zero.
These equations supply a homotopy between a r and the identity, and the
identity r a supplies the other homotopy, thus a homotopy equivalence whose
forward map is the stalk augmentation. No global exactness or flasqueness
is assumed, and the assertion at a point is unused for the empty scheme. -/
theorem moduleCup_godement_stalk_contraction (X : Scheme.{u}) (F : X.Modules)
    (A : CosimplicialObject X.Modules)
    (a : (CochainComplex.singleFunctor X.Modules 0).obj F ⟶
      (((alternatingCofaceMapComplex X.Modules).obj A).extend
        ComplexShape.embeddingUpNat))
    (h : ModuleCupGodementModel X F A a) (x : X) :
    HomologicalComplex.homotopyEquivalences
      (ModuleCat.{u} (X.presheaf.stalk x)) (.up ℤ)
      (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
        (.up ℤ)).map a) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
