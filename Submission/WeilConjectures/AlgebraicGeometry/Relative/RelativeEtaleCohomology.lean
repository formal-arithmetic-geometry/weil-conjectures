/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionTransfer
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import Mathlib.CategoryTheory.Abelian.Injective.Ext

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Relative étale cohomology in an injective-resolution model

Source: Stacks Project, Cohomology on Sites, Tag 03AJ, relative refinement; compare
Cohomology, Tags 0G71 and 0G78 (blueprint: def-amb-relative-etale-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The shifted cone map associated to a strictly commuting restriction square.
Source: Stacks Project, Tag 0G78, mapping-fibre functoriality
(blueprint: def-amb-relative-etale-cohomology). -/
noncomputable def relativeFiberMap
    {A B A' B' : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r : A ⟶ B) (r' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : a ≫ r' = r ≫ b) :
    (CochainComplex.mappingCone r)⟦(-1 : ℤ)⟧ ⟶
      (CochainComplex.mappingCone r')⟦(-1 : ℤ)⟧ :=
  (CategoryTheory.shiftFunctor _ (-1 : ℤ)).map
    (HomologicalComplex.homotopyCofiber.mapArrowHom r r'
      (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) (Arrow.homMk a b h))

end AlgebraicGeometry.Etale
