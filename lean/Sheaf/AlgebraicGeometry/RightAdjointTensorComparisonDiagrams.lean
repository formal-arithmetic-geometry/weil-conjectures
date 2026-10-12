/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Shift and triangle diagrams for the pinned tensor comparison

Source: Stacks Project, Tag 0A9U and equation (48.8.0.1).
(blueprint: lem-sc-right-adjoint-tensor-comparison-diagrams).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

/-- The pinned tensor comparison admits compatible shift squares and distinguished
triangle diagrams, before any component is assumed invertible.
Source: Stacks Project, Tag 0A9U, triangulated-subcategory assertion in the proof;
equation (48.8.0.1) for the comparison.
(blueprint: lem-sc-right-adjoint-tensor-comparison-diagrams).

Proof. Write E = c(O_Y). The source is the lift of Lf*(-) tensor E.
K-flat representatives give its shift comparison and take a triangle with
quasi-coherent vertices to a distinguished triangle in D(O_Z). The restricted
Rf* is exact. Give its right adjoint c the transported shift comparison: under
Hom(Rf*M,K[n]) = Hom(M,c(K[n])), identify this with Hom(M,c(K)[n])
using the shift comparison of Rf* and the adjunction. Yoneda defines the comparison.
The right-adjoint exactness theorem then makes the image of each distinguished
triangle distinguished. These constructions use the specified adjunction, so
also cover a right adjoint presented by an isomorphic functor.

The projection map is the pullback-adjunction mate of inverse mu followed by the
pullback counit. Taking its inverse, composing the right-adjoint counit and the
right unitor, and taking the second mate gives the displayed component of tau.
Naturality of mates and the counit triangle identities identify its shifted
component with that component conjugated by the source and target shift
comparisons. If an adjunction or monoidal structure is presented differently,
transport these comparisons along its comparison isomorphisms; canonical choices
are not assumed in the statement. For B isomorphic to A[n], compose the shift
comparisons with the images of this isomorphism to obtain eF and ec.

For an ambient triangle T with the specified quasi-coherent vertices, transport
its arrows to A,B,C and regard it as a triangle in the full subcategory.
Apply the source and target exact functors. Naturality gives the first two
squares; the shift compatibility just established gives the third square,
including the connecting arrow. Thus tau induces a triangle morphism m.
Its three components, expressed through the vertex identifications eF_i and
ec_i, are precisely the three displayed conjugation formulas. No component
is required to be an isomorphism, and no preservation of coproducts is used. -/
theorem rightAdjointTensorComparison_diagrams
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
          eF.hom ≫ (shiftFunctor (schemeDerivedCategory Z) n).map (τ.app A).hom) ∧
    (∀ (A B C : schemeDerivedQCohCategory Y)
      (T : Pretriangulated.Triangle (schemeDerivedCategory Y)),
      T ∈ Pretriangulated.distinguishedTriangles →
      Nonempty (T.obj₁ ≅ A.obj) → Nonempty (T.obj₂ ≅ B.obj) →
      Nonempty (T.obj₃ ≅ C.obj) →
      ∃ (T₁ T₂ : Pretriangulated.Triangle (schemeDerivedCategory Z)) (m : T₁ ⟶ T₂),
        T₁ ∈ Pretriangulated.distinguishedTriangles ∧
        T₂ ∈ Pretriangulated.distinguishedTriangles ∧
        ∃ (eF₁ : T₁.obj₁ ≅ ((derivedPullback f).obj A.obj ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj))
          (ec₁ : T₂.obj₁ ≅ (c.obj A).obj)
          (eF₂ : T₁.obj₂ ≅ ((derivedPullback f).obj B.obj ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj))
          (ec₂ : T₂.obj₂ ≅ (c.obj B).obj)
          (eF₃ : T₁.obj₃ ≅ ((derivedPullback f).obj C.obj ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj))
          (ec₃ : T₂.obj₃ ≅ (c.obj C).obj),
          m.hom₁ = eF₁.hom ≫ (τ.app A).hom ≫ ec₁.inv ∧
          m.hom₂ = eF₂.hom ≫ (τ.app B).hom ≫ ec₂.inv ∧
          m.hom₃ = eF₃.hom ≫ (τ.app C).hom ≫ ec₃.inv) := by sorry

end AlgebraicGeometry
