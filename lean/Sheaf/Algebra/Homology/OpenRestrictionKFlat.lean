/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Topology.Sheaves.Abelian

/-! # K-flatness under restriction to an open localized site

Source: Stacks Project, Tags 06YB and 03DH.
(blueprint: lem-pc-open-localized-restriction-kflat).
-/

@[expose] public section

universe u
open CategoryTheory

namespace CochainComplex

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Restriction of a K-flat complex to the localized open site is K-flat.
Source: Stacks Project, Tag 06YB (`lemma-check-K-flat-stalks`), and Tag 03DH.

Proof: identify the site of opens over U with the site of the open subspace U.
For every point x of U, neighborhoods contained in U are cofinal among neighborhoods
of its image in X. The resulting stalk-ring and stalk-module isomorphisms are natural
in module maps, hence identify the restricted stalk complex with the original one.
By Tag 06YB the original stalk complex is K-flat. Transport tensor, direct sums and
acyclicity through the stalk-ring isomorphism and apply the stalk criterion on U.
Transport back along the equivalence with the localized site to obtain the assertion.
No bounds or termwise-flatness assumptions are used. When U is empty the stalk
criterion is vacuous; the zero complex is included. The zero-map witness only defines
the termwise restriction and adds no mathematical hypothesis.
(blueprint: lem-pc-open-localized-restriction-kflat). -/
theorem open_localized_restriction_isKFlat
    {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (U : TopologicalSpace.Opens X)
    (hzero : (SheafOfModules.overFunctor.{u} ((sheafCompose
      (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U).PreservesZeroMorphisms)
    (P : CochainComplex (SheafOfModules.{u} ((sheafCompose
      (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (hP : IsKFlat (R := R) P) :
    letI := hzero
    IsKFlat (R := R.over U)
      (((SheafOfModules.overFunctor.{u} ((sheafCompose
        (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) := by sorry

end CochainComplex
