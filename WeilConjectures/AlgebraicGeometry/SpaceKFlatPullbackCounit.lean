/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpaceDerivedTensorPullback
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic

/-! # The derived pullback counit on flat K-flat complexes

Source: Stacks Project, sites-cohomology.tex, Lemma 06YY (derived-base-change),
including its computation on flat-term K-flat complexes.
(blueprint: lem-sfb-space-kflat-pullback-counit).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical derived tensor pullback is computed by a flat-term K-flat complex.
Source: Stacks Project, sites-cohomology.tex, Lemma 06YY (derived-base-change),
using Lemmas 06YS (K-flat-resolution) and 0G7E (pullback-K-flat), transported along
the affine-basis module equivalences of Tag 039Z.
(blueprint: lem-sfb-space-kflat-pullback-counit).

Proof: view the conjugated small-model pullback as the tensor pullback of the
corresponding ringed topoi. Resolve every complex by a flat-term K-flat complex.
A quasi-isomorphism between these complexes remains a quasi-isomorphism under
exact inverse image. Inverse image also preserves flat-term K-flat complexes,
by the K-flat pullback theorem applied before extension of scalars. Tensoring
such a quasi-isomorphism with the target structure sheaf preserves it: its cone
is acyclic and K-flat, and tensoring that cone with any module is acyclic.
Thus these representatives form a resolving class on which ordinary tensor
pullback computes the left derived functor. The resolving-class construction
has invertible counit on each member. Uniqueness of the left derived functor
with its counit identifies that computation with the recorded total left
derived functor, so its canonical counit at P is invertible. Transport through
the affine-basis equivalences preserves this counit and invertibility. No
boundedness or flatness of the morphism is used. -/
theorem smallTensorPullbackComplex_counit_isIso_of_flatKFlat
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [HasDerivedCategory.{w} X.SmallModules]
    [HasDerivedCategory.{w} Y.SmallModules]
    (P : CochainComplex Y.SmallModules ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Y.smallEtaleModelTopology) (R := Y.smallStructureSheaf) P)
    (hflat : ∀ n : ℤ, SheafOfModules.IsFlatOnSite
      (J := Y.smallEtaleModelTopology) (R := Y.smallStructureSheaf) (P.X n)) :
    IsIso (((smallTensorPullbackComplex f).totalLeftDerivedCounit DerivedCategory.Q
      (HomologicalComplex.quasiIso Y.SmallModules (.up ℤ))).app P) := by sorry

end AlgebraicGeometry.AlgebraicSpace
