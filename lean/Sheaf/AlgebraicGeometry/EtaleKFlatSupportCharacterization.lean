/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.AlgebraicGeometry.EtaleKFlatSupportData
public import Sheaf.AlgebraicGeometry.FlatSupportChainDiagram

/-!
# K-flat comparison of actual ordinary etale support sequences

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Locality, expanded by the agent-written
support diagram; Stacks Tags 03DB, 03ER, 06YU, 07A4, 0FPI, 0152 and 014A
(blueprint: lem-pur-etale-kflat-support-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] HomologicalComplex.monoidalCategoryStruct CategoryTheory.catToReflQuiver
universe u uC vC uD vD w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.KFlatSupportComparison

attribute [local instance 20000] sheafBraidedCategory
attribute [local irreducible] Sheaf.monoidalCategory

variable {A B : Type (u + 1)} [CommRing A] [CommRing B]
  {Z P U : Scheme.{u}}

section
variable {C : Type uC} {D : Type uD} [Category.{w + 1} C] [Category.{w + 1} D]
  [Abelian C] [Abelian D] [IsGrothendieckAbelian.{w + 1} C]
  [IsGrothendieckAbelian.{w + 1} D] [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalClosed C] [MonoidalClosed D] [MonoidalPreadditive C]
  [MonoidalPreadditive D] [BraidedCategory C] [BraidedCategory D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive] [F.IsLeftAdjoint] [F.Monoidal]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rightMap_spec_general (adj : F ⊣ G) (Q I J : CochainComplex C ℤ)
    (a : Q ⊗ I ⟶ J) (h : OpenSupport.Diagram adj Q I J a) :
    IsTotalAdjunct adj Q I J a (OpenSupport.rightMap adj Q I J a) := by
  intro p q n hpq
  exact h.2.1 p q n hpq

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [IsGrothendieckAbelian.{w + 1} D] [MonoidalClosed D]
  [MonoidalPreadditive D] [BraidedCategory D] [F.IsLeftAdjoint] in
private theorem totalAdjunct_unique (adj : F ⊣ G) (Q I J : CochainComplex C ℤ)
    (a : Q ⊗ I ⟶ J)
    {v v' : Q ⊗ ((G.mapHomologicalComplex (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj I)) ⟶
      (G.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj J)}
    (hv : IsTotalAdjunct adj Q I J a v) (hv' : IsTotalAdjunct adj Q I J a v') :
    v = v' := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  simpa only [HomologicalComplex.ιTensorObj] using
    (hv p q n hpq).trans (hv' p q n hpq).symm
end

variable [Finite A] (j : U ⟶ P) [IsOpenImmersion j]
    (Q I J : Complex A P) (a : Q ⊗ I ⟶ J)
    (v : Q ⊗ (pushComplex A j).obj ((pullComplex A j).obj I) ⟶
      (pushComplex A j).obj ((pullComplex A j).obj J))
/-- Equality to the canonical quotient map is exactly its total-summand characterization.
Source: Stacks 07A4, the ordinary tensor/pullback adjunction; total coproduct extensionality
(blueprint: lem-pur-etale-kflat-support-characterization).

Proof: the flat support chain diagram computes the canonical map on each summand.
Maps from a total coproduct are determined by their summand composites. Hence any map
with these composites equals the canonical map, and the converse follows by substitution. -/
theorem support_rightMap_iff (hQ : ∀ n : ℤ, ObjectProperty.flat (Q.X n)) :
    IsRightMap j Q I J a v ↔
    HEq v (OpenSupport.rightMap
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j) Q I J a) := by
  have hc := rightMap_spec_general
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j) Q I J a
    (flatSupportChainDiagram A j Q I J (fun n ↦ (hQ n).2) a)
  constructor
  · intro h
    exact heq_of_eq (totalAdjunct_unique _ Q I J a h hc)
  · intro h
    exact (eq_of_heq h) ▸ hc

end AlgebraicGeometry.Etale.KFlatSupportComparison
