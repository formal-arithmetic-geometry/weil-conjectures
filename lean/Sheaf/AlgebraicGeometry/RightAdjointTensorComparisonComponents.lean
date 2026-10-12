module
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
/-- The pinned projection family has a natural right-adjoint mate.
Source: Stacks Project, Tag 0A9U; naturality of the monoidal comparison,
counits, and adjunction hom equivalences.
Proof: expand the displayed component and use naturality of the monoidal
comparison, both counits, the right unitor, and adjunction hom equivalence.
(blueprint: lem-sc-right-adjoint-tensor-comparison-components) -/
theorem rightAdjointTensorComparison_components
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
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
    (pf : ∀ K : schemeDerivedQCohCategory Y,
      (schemeDerivedDirectImage f).obj
          (((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj) ≅
        K.obj ⊗ (schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj)
    (hpf : ∀ K, (pf K).inv = (a.homEquiv _ _)
          ((Functor.Monoidal.μIso (derivedPullback f) K.obj
            ((schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj)).inv ≫
            (derivedPullback f).obj K.obj ◁ a.counit.app (c.obj ⟨𝟙_ _, hO⟩).obj)) :
    let F := (schemeDerivedQCohProperty Z).lift
      ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback f ⋙
        tensorRight (c.obj ⟨𝟙_ _, hO⟩).obj)
      (fun K ↦ hTensor K (c.obj ⟨𝟙_ _, hO⟩))
    ∃ τ : F ⟶ c, ∀ K,
      τ.app K = ((adj.homEquiv
          ⟨((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj,
            hTensor K (c.obj ⟨𝟙_ _, hO⟩)⟩ K)
          (ObjectProperty.homMk ((pf K).hom ≫
            K.obj ◁ (adj.counit.app ⟨𝟙_ _, hO⟩).hom ≫ (ρ_ K.obj).hom))) := by sorry
end AlgebraicGeometry
