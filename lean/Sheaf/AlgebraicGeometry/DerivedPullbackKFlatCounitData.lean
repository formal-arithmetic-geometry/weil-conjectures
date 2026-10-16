module

public import Sheaf.AlgebraicGeometry.DerivedPullback
import Sheaf.AlgebraicGeometry.DerivedPullbackShiftedUnitIsoData
public import Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

@[expose] public section
set_option autoImplicit false
set_option linter.unusedVariables false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry

/-- K-flat counit data for derived pullback.

Source: Stacks Project, Tag 06YJ, Lemma 20.27.1. The derived pullback is
computed on K-flat complexes; the shifted structure-sheaf comparison is
constructed from the monoidal unit and the counit. The construction is
independent of the later cone morphism.
(blueprint: lem-sc-derived-pullback-kflat-counit-data).
-/
theorem exists_derivedPullback_kFlat_counit_data
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    [(Scheme.Modules.tensorPullback f).Additive] :
    ∃ e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧,
      ∃ ε : DerivedCategory.Qh ⋙ derivedPullback f ⟶
          (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            (DerivedCategory.Qh : HomotopyCategory
              (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
              schemeDerivedCategory Z),
    ∀ P : CochainComplex
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
          CochainComplex.IsAcyclicTensorKFlat (R := Y.sheaf) P →
          IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) := by
  obtain ⟨e⟩ := exists_derivedPullback_shifted_unit_iso f
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
      E, hE, hEmap, hEadd, ε, hε⟩ :=
    Classical.choose_spec (exists_derivedPullback f)
  have hE' : E = Scheme.Modules.tensorPullback f :=
    CategoryTheory.Functor.ext hE (fun _ _ a ↦ hEmap a)
  subst E
  exact ⟨e, ε, hε.2.2⟩

end AlgebraicGeometry
