/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Compatible exact structures for the pinned right-adjoint tensor comparison

This isolates the geometric shift and exactness construction from the formal construction
of triangle diagrams. Source: Stacks Project, Tags 0A9U and 0A9S.
(blueprint: lem-sc-right-adjoint-tensor-compatible-exact-structures).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

/-- Compatible shift structures and exactness for the two ambient-valued comparison functors.
Source: Stacks Project, Tag 0A9U, triangulated-subcategory assertion and equation (48.8.0.1).
(blueprint: lem-sc-right-adjoint-tensor-compatible-exact-structures).

Proof. Let E = c(O_Y). Resolve the input by K-flat complexes. Termwise pullback followed
by tensor with a K-flat representative of E commutes with shifts, including their zero
and addition coherences, and carries the mapping cone of a map to its mapping cone.
Localization gives a shift structure on F and preservation of all distinguished triangles
whose vertices have quasi-coherent cohomology. Compute Rf* using injective resolutions;
its shift comparisons are coherent and its restriction to D_QCoh is exact. Quasi-coherent
cohomology is closed under shifts and extensions, so this restriction is an exact functor
of triangulated categories. Transport its shifts through adj by the Hom adjunction and
Yoneda. The right adjoint of this exact functor is exact with those shifts. Compose with
the exact ambient inclusion to obtain the asserted structure on G.

The pinned formula identifies the component of the comparison with the adj-mate of the
projection isomorphism followed by tensoring the adj-counit at O_Y and the right unitor.
On K-flat representatives, move translation through pullback and tensor in this formula.
Naturality of both counits and the adjunction triangle identities identify the resulting
map with the translate of the unshifted component. This gives the CommShift equation.
The same computation respects zero and addition of shifts. Transport along the monoidal
and adjunction comparison isomorphisms for the specified choices a and adj; uniqueness
of adjunction mates preserves the component formula. Thus the exact shift structures
can be chosen simultaneously with shift compatibility of the specified transformation.
No component is cancelled or assumed invertible; the argument also covers E = 0 and
zero triangles. The input shift-stability instance is propositional, so it changes no
choice of the standard full-subcategory shift. -/
theorem rightAdjointTensor_compatibleExactStructures
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    [(schemeDerivedQCohProperty Y).IsStableUnderShift ℤ]
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
    let F := (schemeDerivedQCohProperty Z).lift
      ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback f ⋙
        tensorRight (c.obj ⟨𝟙_ _, hO⟩).obj)
      (fun K ↦ hTensor K (c.obj ⟨𝟙_ _, hO⟩)) ⋙ (schemeDerivedQCohProperty Z).ι
    let G := c ⋙ (schemeDerivedQCohProperty Z).ι
    ∃ (sF : F.CommShift ℤ) (sG : G.CommShift ℤ),
      letI := sF
      letI := sG
      NatTrans.CommShift (Functor.whiskerRight τ (schemeDerivedQCohProperty Z).ι) ℤ ∧
      ∀ S : Pretriangulated.Triangle (schemeDerivedQCohCategory Y),
        (schemeDerivedQCohProperty Y).ι.mapTriangle.obj S ∈
          Pretriangulated.distinguishedTriangles →
        F.mapTriangle.obj S ∈ Pretriangulated.distinguishedTriangles ∧
        G.mapTriangle.obj S ∈ Pretriangulated.distinguishedTriangles := by sorry

end AlgebraicGeometry
