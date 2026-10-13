/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Sheaf.AlgebraicGeometry.DerivedCategory

/-! # Exact shifts for a pinned projection followed by a counit

Source: Stacks Project, Tags 0A9U and 0A9S, equation-compare-with-pullback.
(blueprint: lem-sc-pinned-projection-counit-exact-shift).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

/-- Exact shifts making a projection isomorphism followed by tensoring a fixed map to
O_Y compatible with translation. This assertion involves no right adjoint to Rf_*.
Source: Stacks Project, Tags 0A9U and 0A9S, equation-compare-with-pullback.
(blueprint: lem-sc-pinned-projection-counit-exact-shift).

Proof. Fix E and ε : Rf_*E → O_Y. On K-flat representatives the functor
K ↦ Lf*K tensor E takes a cone to the cone of the tensored pullback map.
Translation of complexes supplies its zero and addition coherences. Direct image
on K-injective representatives also commutes with translation and mapping cones.
Quasi-coherent cohomology is stable under translations and extensions, so both
constructions restrict to the stated quasi-coherent functors Q and R.
For the specified monoidal structure on Lf*, use the tensorator and the identification
K[n] ≅ K tensor O_Y[n] to transport the pullback translation comparison. The
associativity and unit equations of the tensorator give the addition and zero
coherences. Transport the direct-image comparison across a by adjunction mates;
the unit and counit triangle identities give its compatible translation comparison.
These transported comparisons preserve distinguished triangles: on representative
complexes they identify the images with the mapping-cone triangles just described.
Expand the inverse projection component as the a-mate of the inverse tensorator
followed by Lf*K tensor the a-counit at E. Move translation through these factors.
The transported comparisons, counit naturality, and the adjunction triangle
identities identify the shifted component with the translation of the original.
Invert this equality using pf. Tensoring ε is natural in the shifted first variable;
the right unitor has the same translation comparison. Compose these three
compatibility equations to obtain the equation for ν. Its assumed component
formula transfers the equation to the specified ν. No ν component is cancelled:
ε = 0, E = 0, and zero triangles satisfy the same argument. -/
theorem pinnedProjectionCounit_exactShift
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    [(schemeDerivedQCohProperty Y).IsTriangulated]
    [(schemeDerivedQCohProperty Z).IsTriangulated]
    (hRf : ∀ E : schemeDerivedQCohCategory Z,
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E.obj))
    (hO : schemeDerivedQCohProperty Y (𝟙_ (schemeDerivedCategory Y)))
    (E : schemeDerivedQCohCategory Z)
    (hTensor : ∀ K : schemeDerivedQCohCategory Y,
      schemeDerivedQCohProperty Z (((derivedPullback f).obj K.obj) ⊗ E.obj))
    [Functor.Monoidal (derivedPullback f)]
    (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (ε : (⟨(schemeDerivedDirectImage f).obj E.obj, hRf E⟩ :
      schemeDerivedQCohCategory Y) ⟶ ⟨𝟙_ _, hO⟩)
    (ν : (schemeDerivedQCohProperty Z).lift
      ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback f ⋙ tensorRight E.obj)
      hTensor ⋙ (schemeDerivedQCohProperty Y).lift
        ((schemeDerivedQCohProperty Z).ι ⋙ schemeDerivedDirectImage f) hRf ⟶
      𝟭 (schemeDerivedQCohCategory Y))
    (hν : ∀ K : schemeDerivedQCohCategory Y,
      ∃ pf : (schemeDerivedDirectImage f).obj
            (((derivedPullback f).obj K.obj) ⊗ E.obj) ≅
          K.obj ⊗ (schemeDerivedDirectImage f).obj E.obj,
        pf.inv = (a.homEquiv _ _)
          ((Functor.Monoidal.μIso (derivedPullback f) K.obj
            ((schemeDerivedDirectImage f).obj E.obj)).inv ≫
            (derivedPullback f).obj K.obj ◁ a.counit.app E.obj) ∧
        (ν.app K).hom = pf.hom ≫ K.obj ◁ ε.hom ≫ (ρ_ K.obj).hom) :
    let Q := (schemeDerivedQCohProperty Z).lift
      ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback f ⋙ tensorRight E.obj) hTensor
    let R := (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty Z).ι ⋙ schemeDerivedDirectImage f) hRf
    ∃ (sQ : Q.CommShift ℤ) (sR : R.CommShift ℤ),
      letI := sQ
      letI := sR
      Q.IsTriangulated ∧ R.IsTriangulated ∧ NatTrans.CommShift ν ℤ := by sorry

end AlgebraicGeometry
