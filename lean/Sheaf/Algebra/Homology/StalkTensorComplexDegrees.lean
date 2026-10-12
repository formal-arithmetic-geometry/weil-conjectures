/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Sheaf.Topology.StalkDirectSums

/-!
# Degreewise stalk tensor comparison

Source: Stacks Project, Cohomology, Tag 06YB, tensor-stalk identification
(blueprint: lem-pc-stalk-tensor-complex-degrees).
-/

@[expose] public section

universe u₁

open CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace AlgebraicGeometry

namespace CochainComplex

variable (X : RingedSpace.{u₁}) (x : X)

set_option hygiene false in
local notation "O" => (sheafCompose (Opens.grothendieckTopology (X : Type u₁))
  (forget₂ CommRingCat.{u₁} RingCat.{u₁})).obj X.sheaf
set_option hygiene false in
local notation "S" => (RingedSpace.moduleStalkFunctor X x).mapHomologicalComplex (.up ℤ)

noncomputable local instance stalkTensorDegreesMonoidal :
    MonoidalCategory (SheafOfModules.{u₁} O) :=
  SheafOfModules.monoidalCategory X.sheaf

/-- Source: Stacks Project, Cohomology, Tag 06YB, tensor-stalk identification,
first two steps (blueprint: lem-pc-stalk-tensor-complex-degrees).

Proof: express the degree as the coproduct indexed by pairs `(p,q)` with `p+q=n`.
The canonical stalk/direct-sum comparison of Tag 009E identifies its stalk with
that coproduct of stalks. If its scalar ring is presented as a RingCat stalk,
identify it with the CommRingCat stalk by the canonical ring map on germs. Represent
scalars on a neighborhood to check that the two scalar actions agree, and transport
the linear equivalence along this identification. For smaller-universe diagonal
indices, lift the index type and reindex the coproduct along the lift equivalence.
Identify the algebraic direct sum with the categorical coproduct using
`ModuleCat.coprodIsoDirectSum`. Apply the tensor comparison to every summand and
use the universal property of the coproduct to obtain an isomorphism. Its value
on each injection is the displayed formula; no differential is involved. -/
theorem exists_stalk_tensor_degree_iso
    (φ : ∀ A B : SheafOfModules.{u₁} O,
      (RingedSpace.moduleStalkFunctor X x).obj (A ⊗ B) ≅
        (RingedSpace.moduleStalkFunctor X x).obj A ⊗
          (RingedSpace.moduleStalkFunctor X x).obj B) :
    ∃ e : ∀ (F K : CochainComplex (SheafOfModules.{u₁} O) ℤ) (n : ℤ),
      ((S).obj (mapBifunctor F K (curriedTensor _))).X n ≅
        (mapBifunctor ((S).obj F) ((S).obj K) (curriedTensor _)).X n,
      ∀ (F K : CochainComplex (SheafOfModules.{u₁} O) ℤ)
        (p q n : ℤ) (h : ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) (p, q) = n),
        (RingedSpace.moduleStalkFunctor X x).map
            (HomologicalComplex.ιMapBifunctor F K (curriedTensor _) (.up ℤ) p q n h) ≫
          (e F K n).hom =
        (φ (F.X p) (K.X q)).hom ≫ HomologicalComplex.ιMapBifunctor
          ((S).obj F) ((S).obj K) (curriedTensor _) (.up ℤ) p q n h := by
  sorry

end CochainComplex
