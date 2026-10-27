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
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] HomologicalComplex.monoidalCategoryStruct CategoryTheory.catToReflQuiver
universe u uC vC uD vD w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.KFlatSupportComparison


attribute [local instance 20000] sheafBraidedCategory
attribute [local irreducible] Sheaf.monoidalCategory

variable {A B : Type (u + 1)} [CommRing A] [CommRing B]
  {Z P U : Scheme.{u}}


/-- Tensor a short complex by the supplied monoidal functor.
Source: Stacks 012Z (blueprint: def-pur-etale-kflat-support-rows). -/
abbrev tensorRow {C : Type*} [Category C] [Preadditive C]
    [MonoidalCategory C] [MonoidalPreadditive C] (Q : C) (S : ShortComplex C) :=
  S.map (tensorLeft Q)
/-- Tensor the three components of a short-complex map.
Source: Stacks 012Z, 093X (blueprint: def-pur-etale-kflat-support-rows). -/
def tensorRowMap {C : Type*} [Category C] [Preadditive C]
    [MonoidalCategory C] [MonoidalPreadditive C] (Q : C)
    {S T : ShortComplex C} (f : S ⟶ T) : tensorRow Q S ⟶ tensorRow Q T :=
  (tensorLeft Q).mapShortComplex.map f

/-- Object and arrow assignments to short complexes, used to state diagram naturality.
Source: Stacks 012Z (blueprint: def-pur-etale-kflat-support-rows). -/
structure RowFamily (C D : Type*) [Category C] [Category D] [HasZeroMorphisms D] where
  obj : C → ShortComplex D
  map : ∀ {I I' : C}, (I ⟶ I') → (obj I ⟶ obj I')

section
variable (A : Type (u + 1)) [CommRing A] {Z P U : Scheme.{u}}
  (i : Z ⟶ P) [IsClosedImmersion i] (j : U ⟶ P) [IsOpenImmersion j]
  (hij : Set.range i.base = (Set.range j.base)ᶜ)
/-- The actual support row and its functorial maps.
Source: Stacks 012Z, 093X (blueprint: def-pur-etale-kflat-support-rows). -/
def supportSequenceFamily : RowFamily (Complex A P) (Complex A P) where
  obj I := etaleSupportSequence A i j hij I
  map f := etaleSupportSequenceMap A i j hij f

/-- Naturality of a family of characterized arrows between two short-complex functors. -/
def DiagramNatural {C D : Type*} [Category C] [Category D] [HasZeroMorphisms D]
    (S T : RowFamily C D)
    (R : ∀ I : C, (S.obj I ⟶ T.obj I) → Prop) (I : C)
    (m : S.obj I ⟶ T.obj I) : Prop :=
  ∀ (I' : C) (f : I ⟶ I') (m' : S.obj I' ⟶ T.obj I'),
    R I' m' → S.map f ≫ m' = m ≫ T.map f

variable (Q : Complex A P) (F : Complex A P ⥤ Complex A P)
/-- The actual support row tensored by Q.
Source: Stacks 012Z, 093X (blueprint: def-pur-etale-kflat-support-rows). -/
def topSequenceFamily : RowFamily (Complex A P) (Complex A P) where
  obj I := tensorRow Q (etaleSupportSequence A i j hij I)
  map f := tensorRowMap Q (etaleSupportSequenceMap A i j hij f)

/-- The actual support row of the functorial replacement.
Source: Stacks 012Z, 093X (blueprint: def-pur-etale-kflat-support-rows). -/
def bottomSequenceFamily : RowFamily (Complex A P) (Complex A P) where
  obj I := etaleSupportSequence A i j hij
    (F.obj (Q ⊗ I))
  map f := etaleSupportSequenceMap A i j hij
    (F.map ((tensorLeft Q).map f))

end


/-- The prescribed middle and total-adjunct quotient components.
Source: Stacks 012Z, 093X (blueprint: def-pur-etale-kflat-support-rows). -/
def IsComparison (A : Type (u + 1)) [CommRing A]
    {Z P U : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i]
    (j : U ⟶ P) [IsOpenImmersion j] (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (Q : Complex A P) (F : Complex A P ⥤ Complex A P) (η : 𝟭 _ ⟶ F)
    (I : Complex A P)
    (m : (topSequenceFamily A i j hij Q).obj I ⟶
      (bottomSequenceFamily A i j hij Q F).obj I) : Prop :=
  HEq m.τ₂ (η.app (Q ⊗ I)) ∧
  HEq m.τ₃ (OpenSupport.rightMap
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j)
    Q I (F.obj (Q ⊗ I)) (η.app (Q ⊗ I)))


end AlgebraicGeometry.Etale.KFlatSupportComparison
