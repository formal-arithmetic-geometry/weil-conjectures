/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentAlgebra
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Limits
public import WeilConjectures.Mathlib.Algebra.Category.Ring.Limits
public import WeilConjectures.CategoryTheory.CochainCoefficientUniverseTransport
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Commutative algebra sheaves on an algebraic space

Source: Stacks Project, Properties of Spaces, Tags 03G7 and 03LZ; Modules on Sites,
Section 03EK; Limits of Spaces, Tags 082A and 086Z
(blueprint: def-sfb-space-comm-algebra-sheaf).

The commutative structure sheaf, the algebra sheaves (its under category) and their
underlying modules are those of `WeilConjectures.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentAlgebra`
(blueprint: def-sfb-space-quasi-coherent-algebra). This module adds the underlying-module
functor, chart evaluation into ordinary algebras, embedded ideals, and the additive
sheafification instances on the full small etale site.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Additive sheafification exists in the original section universe and is left exact.
Source: Stacks, Sites, comparison lemma 039Z; Properties of Spaces, Tag 03ED
(blueprint: def-sfb-space-comm-algebra-sheaf).
Proof: refine a scheme atlas by affine opens. Affine etale charts have a u-small
skeleton, since etale algebras are finitely presented. Every chart has an affine open
cover and overlaps have affine refinements. The comparison lemma identifies sheaves
with sheaves on that small basis. The two plus constructions on the basis have u-small
values and preserve finite limits. Transport their adjunction to the full etale site. -/
@[instance] theorem etaleAlgebraModulesHasSheafify
    {S : Scheme.{u}} (X : AlgebraicSpace S) :
    HasSheafify X.etaleTopology AddCommGrpCat.{u} := by
  sorry

/-- Additive sheafification inverts precisely the locally bijective maps.
Source: Stacks, Sites, Tag 039Z and sheafification
(blueprint: def-sfb-space-comm-algebra-sheaf).
Proof: on the small affine etale basis the plus unit is locally bijective, and two
plus constructions turn every locally bijective map into an isomorphism. Conversely
local injectivity and local surjectivity follow from the locally bijective units and
an isomorphism of sheafifications. The basis comparison preserves these local tests. -/
@[instance] theorem etaleAlgebraModulesWEqualsLocallyBijective
    {S : Scheme.{u}} (X : AlgebraicSpace S) :
    X.etaleTopology.WEqualsLocallyBijective AddCommGrpCat.{u} := by
  sorry

/-- The underlying-module functor of def-sfb-space-quasi-coherent-algebra: algebra morphisms
give the same section maps on the underlying O_X-modules.
Source: Stacks, Modules on Sites, Section 03EK
(blueprint: def-sfb-space-comm-algebra-sheaf). -/
def algebraModuleFunctor {S : Scheme.{u}} (X : AlgebraicSpace S) :
    X.CommAlgebraSheaf ⥤ X.Modules where
  obj := CommAlgebraSheaf.toModule
  map := fun {A B} f ↦
    { val := PresheafOfModules.homMk
        (Functor.whiskerRight f.right.hom
          (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat))
        (by
          intro U r a
          change A.right.obj.obj U at a
          change X.commStructureSheaf.obj.obj U at r
          change (f.right.hom.app U).hom ((A.hom.hom.app U).hom r * a) =
            (B.hom.hom.app U).hom r * (f.right.hom.app U).hom a
          rw [map_mul]
          congr 1
          exact congrArg (fun t ↦ t.hom.app U r) (Under.w f)) }

/-- Affine-chart sections as commutative algebras: the under category of the section ring.
This is the usual category of R-algebras, with the scalar map carried explicitly.
Source: Stacks, Limits of Spaces, Tags 082A and 086Z
(blueprint: def-sfb-space-comm-algebra-sheaf). -/
def algebraEvaluation {S : Scheme.{u}} (X : AlgebraicSpace S) (U : X.EtaleSite) :
    X.CommAlgebraSheaf ⥤ Under (X.commStructureSheaf.obj.obj (op U)) where
  obj A := Under.mk (A.hom.hom.app (op U))
  map f := Under.homMk (f.right.hom.app (op U))
    (congrArg (fun t ↦ t.hom.app (op U)) (Under.w f))

/-- An embedded ideal sheaf in an algebra is a module monomorphism whose section images
are ideals on every object. Its source is already a sheaf, so ideal membership is local.
Source: Stacks, Modules on Sites, ideals; Limits of Spaces, Tags 082A and 086Z
(blueprint: def-sfb-space-comm-algebra-sheaf). -/
def IsAlgebraIdeal {S : Scheme.{u}} {X : AlgebraicSpace S} {A : X.CommAlgebraSheaf}
    {I : X.Modules} (i : I ⟶ A.toModule) : Prop :=
  Mono i ∧ ∀ U : X.EtaleSite, ∃ J : Ideal (A.right.obj.obj (op U)),
    (J : Set (A.right.obj.obj (op U))) = Set.range (i.val.app (op U))

end AlgebraicGeometry.AlgebraicSpace
