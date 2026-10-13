/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.Topology.RingedSpaceModuleCohomology
public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Category.ModuleCat.Colimits

/-! # K-flat complexes under inverse evaluation on a point

Source: Stacks Project, Tags 0B6A, 06YN and 06YC.
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RingedSpace

local instance pointKFlatCommRing (Y : RingedSpace.{u}) :
    CommRing ((moduleRings Y).obj.obj (op ⊤)) :=
  inferInstanceAs (CommRing (Y.presheaf.obj (op ⊤)))

noncomputable local instance pointKFlatColimits
    (Y : RingedSpace.{u}) :
    HasColimitsOfSize.{0, 0} (ModuleCat.{u} ((moduleRings Y).obj.obj (op ⊤))) :=
  hasColimitsOfSizeShrink.{0, 0, u} _

/-- Inverse evaluation on a one-point ringed space takes ordinary module K-flat
complexes to K-flat sheaf complexes.
Source: Stacks Project, Section 20.44, Tag 0B6A (the one-point identification),
Definition 06YN and Lemma 06YC.
(blueprint: lem-sc-point-inverse-evaluation-kflat)

Proof: every open of the point is either empty orthe whole space. The empty-open
section module of a sheaf is zero. Consequently evaluation of the sheaf tensor at
the whole space is the ordinary tensor product of its section modules: sheafifying
the sectionwise tensor does not alter the whole-space sections, since every cover
of the whole point contains the whole point. This identification is natural in
both modules. Evaluation is an exact equivalence and preserves coproducts, so
termwise evaluation identifies the total sheaf tensor with the total module tensor
and preserves and reflects acyclicity. The given natural isomorphism identifies
e.functor with evaluation. For an acyclic sheaf complex F, its evaluated complex
is acyclic. The counit of e identifies evaluation of e.inverse(K) with K. Ordinary
K-flatness of K therefore makes the evaluated tensor F tensor e.inverse(K)
acyclic, and reflection of acyclicity proves the claim. The equivalence between
preservation of quasi-isomorphisms and acyclic tensors follows from mapping cones
(or HomotopyCategory.kFlat_iff_preserves_acyclic). This argument includes the zero
ring, the zero complex and all unbounded complexes. -/
theorem pointInverseEvaluation_isKFlat
    (Y : RingedSpace.{u}) [Unique Y]
    (e : SheafOfModules.{u} (moduleRings Y) ≌
      ModuleCat.{u} ((moduleRings Y).obj.obj (op ⊤)))
    (he : Nonempty (e.functor ≅ globalSectionsFunctor Y))
    [e.inverse.Additive]
    (K : CochainComplex (ModuleCat.{u} ((moduleRings Y).obj.obj (op ⊤))) ℤ)
    (hK : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat K) :
    CochainComplex.IsKFlat (R := Y.sheaf)
      ((e.inverse.mapHomologicalComplex (.up ℤ)).obj K) := by sorry

end AlgebraicGeometry.RingedSpace
