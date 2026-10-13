/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.RightAdjointTensorCompatibleExactStructures
import all Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonTriangle

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

private theorem exists_shift_square_generic
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (F G : C ⥤ D) [F.CommShift ℤ] [G.CommShift ℤ]
    (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]
    (A B : C) (n : ℤ) (h : Nonempty (B ≅ A⟦n⟧)) :
    ∃ (eF : F.obj B ≅ (F.obj A)⟦n⟧) (eG : G.obj B ≅ (G.obj A)⟦n⟧),
      (τ.app B) ≫ eG.hom = eF.hom ≫ (τ.app A)⟦n⟧' := by
  obtain ⟨i⟩ := h
  let eF : F.obj B ≅ (F.obj A)⟦n⟧ :=
    F.mapIso i ≪≫ (F.commShiftIso n).app A
  let eG : G.obj B ≅ (G.obj A)⟦n⟧ :=
    G.mapIso i ≪≫ (G.commShiftIso n).app A
  refine ⟨eF, eG, ?_⟩
  dsimp [eF, eG]
  rw [← τ.naturality_assoc]
  rw [← NatTrans.shift_app_comm τ n A]
  simp only [Category.assoc]

/-- Shift square for the pinned right-adjoint tensor comparison.
Source: Stacks Project, Tag 0A9U, triangulated-subcategory argument, and
equation (48.8.0.1). This proof expands the comparison compatibility used there.
(blueprint: lem-sc-right-adjoint-tensor-comparison-shift).

Proof. Put E = c(O_Y) and F(K) = Lf*(K) tensor E. Compute derived pullback and
this tensor on K-flat representatives. Shifting these representatives gives
F(K[n]) isomorphic to F(K)[n]; tensoring a cone gives the cone of the tensored
map, so F is exact. Restrict derived direct image to the quasi-coherent full
subcategory. Its shift comparison transports through adj to a comparison
c(K[n]) isomorphic to c(K)[n]: apply adj to Hom(Rf*(M), K[n]), move the shift
using exactness of Rf*, and apply adj again. Yoneda supplies the comparison.
The right adjoint of an exact functor is exact for this comparison.

The projection map is the a-mate of inverse monoidal comparison followed by
the pullback counit. The hypothesis hτ identifies τ with the adj-mate of its
inverse followed by tensoring the adj-counit at O_Y and the right unitor.
Compute this composite on shifted K-flat representatives. Moving the shift
through the tensor and pullback comparisons, use naturality of the counits
and the adjunction triangle identities to obtain the same composite for K,
shifted by n. Thus τ commutes with the constructed shift comparisons. Transport
these structures along the comparison isomorphisms for the specified monoidal
structure and adjunctions; the construction does not require canonical choices.

Given an isomorphism B.obj to A.obj[n], lift it to the quasi-coherent full
subcategory. Compose its images under F and c with their shift comparisons to
obtain eF and ec. Naturality of τ for this isomorphism, followed by its shift
compatibility, gives exactly the displayed equality. This includes n = 0 and
negative n and never cancels or assumes invertibility of a component of τ. -/
theorem rightAdjointTensorComparison_shift
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (hRf : ∀ E : schemeDerivedQCohCategory Z,
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E.obj))
    (hO : schemeDerivedQCohProperty Y (𝟙_ (schemeDerivedCategory Y)))
    (hTensor : ∀ (K : schemeDerivedQCohCategory Y) (E : schemeDerivedQCohCategory Z),
      schemeDerivedQCohProperty Z (((derivedPullback f).obj K.obj) ⊗ E.obj))
    [Functor.Monoidal (derivedPullback f)]
    (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (c : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory Z)
    (adj : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty Z).ι ⋙ schemeDerivedDirectImage f) hRf ⊣ c)
    (τ : (schemeDerivedQCohProperty Z).lift
      ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback f ⋙
        tensorRight (c.obj ⟨𝟙_ _, hO⟩).obj)
      (fun K ↦ hTensor K (c.obj ⟨𝟙_ _, hO⟩))
      ⟶ c)
    (hτ : ∀ K : schemeDerivedQCohCategory Y,
      ∃ pf : (schemeDerivedDirectImage f).obj
            (((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj) ≅
          K.obj ⊗ (schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj,
        pf.inv = (a.homEquiv _ _)
          ((Functor.Monoidal.μIso (derivedPullback f) K.obj
            ((schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj)).inv ≫
            (derivedPullback f).obj K.obj ◁ a.counit.app (c.obj ⟨𝟙_ _, hO⟩).obj) ∧
        τ.app K = ((adj.homEquiv
          ⟨((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj,
            hTensor K (c.obj ⟨𝟙_ _, hO⟩)⟩ K)
          (ObjectProperty.homMk (pf.hom ≫
            K.obj ◁ (adj.counit.app ⟨𝟙_ _, hO⟩).hom ≫ (ρ_ K.obj).hom)))) :
    (∀ (A : schemeDerivedQCohCategory Y) (n : ℤ)
      (B : schemeDerivedQCohCategory Y), Nonempty (B.obj ≅ A.obj⟦n⟧) →
      ∃ (eF : ((derivedPullback f).obj B.obj ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj) ≅
          (((derivedPullback f).obj A.obj ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj)⟦n⟧))
        (ec : (c.obj B).obj ≅ (c.obj A).obj⟦n⟧),
        (τ.app B).hom ≫ ec.hom =
          eF.hom ≫ (shiftFunctor (schemeDerivedCategory Z) n).map (τ.app A).hom) := by
  classical
  let : (schemeDerivedQCohProperty Y).IsStableUnderShift ℤ := qc_stable Y
  let F := (schemeDerivedQCohProperty Z).lift
    ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback f ⋙
      tensorRight (c.obj ⟨𝟙_ _, hO⟩).obj)
    (fun K ↦ hTensor K (c.obj ⟨𝟙_ _, hO⟩)) ⋙ (schemeDerivedQCohProperty Z).ι
  let G := c ⋙ (schemeDerivedQCohProperty Z).ι
  let t : F ⟶ G := Functor.whiskerRight τ (schemeDerivedQCohProperty Z).ι
  obtain ⟨sF, sG, ht, _⟩ :=
    rightAdjointTensor_compatibleExactStructures f hRf hO hTensor a c adj τ hτ
  let := sF
  let := sG
  let : NatTrans.CommShift t ℤ := ht
  intro A n B ⟨e⟩
  let I := (schemeDerivedQCohProperty Y).ι
  let i : B ≅ A⟦n⟧ := ObjectProperty.isoMk (schemeDerivedQCohProperty Y)
    (e ≪≫ ((I.commShiftIso n).app A).symm)
  exact exists_shift_square_generic F G t A B n ⟨i⟩

end AlgebraicGeometry
