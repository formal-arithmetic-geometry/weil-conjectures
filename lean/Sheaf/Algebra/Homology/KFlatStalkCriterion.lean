/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.Additive

/-!
# K-flatness detected on stalks

Source: Stacks Project, Cohomology, Lemma 06YB, label `lemma-check-K-flat-stalks`
(blueprint: lem-pc-kflat-stalk-criterion).
-/

@[expose] public section

universe v

open CategoryTheory MonoidalCategory TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

/-- (blueprint: lem-pc-kflat-stalk-criterion) A complex of sheaves of modules on a
ringed space is K-flat precisely when every stalk complex is K-flat over its
stalk ring (Stacks, Cohomology, Lemma 06YB).

Proof, forward: for an acyclic stalk complex, take its termwise skyscraper
complex (`lem-pc-skyscraper-complex`). K-flatness makes its total tensor with
`K` acyclic. Exactness can be checked on stalks
(`lem-weil-pbc-module-stalk-exact`, `def-pc-acyclic-complex-modules`), and the
stalk of the total tensor is the total tensor of stalks
(`lem-pc-stalk-tensor-complex`).

Proof, reverse: an acyclic sheaf complex has acyclic stalk complexes by
`lem-weil-pbc-module-stalk-exact`. K-flatness at every stalk and the tensor
identification show that the total tensor is acyclic at every stalk; stalkwise
exactness then gives its acyclicity, as required by `def-pc-kflat-complex`. -/
theorem isKFlat_iff_stalk_isKFlat (X : RingedSpace.{v})
    (K : CochainComplex (SheafOfModules.{v}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{v} RingCat.{v})).obj X.sheaf)) ℤ) :
    K.IsKFlat ↔ ∀ x : X,
      ∀ F : CochainComplex (ModuleCat.{v} (X.presheaf.stalk x)) ℤ,
        F.Acyclic →
          (CochainComplex.mapBifunctor F
            (((moduleStalkFunctor X x).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K) (curriedTensor _)).Acyclic :=
  sorry

end AlgebraicGeometry.RingedSpace
