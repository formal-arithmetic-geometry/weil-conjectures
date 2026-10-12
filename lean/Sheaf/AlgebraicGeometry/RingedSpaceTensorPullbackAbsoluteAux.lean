module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import Sheaf.Algebra.Homology.KFlatPullback
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Sheaf.Algebra.Homology.DerivedChangeOfRings
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass

@[expose] public section

universe u wX wY
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.RingedSpace

/-- The K-flat resolving-class construction supplies the derived comparison for the
concrete tensor pullback.  The proof follows Tags 06YJ, 079W and 06XN: resolve by
K-flat complexes, use preservation of quasi-isomorphisms under inverse image and
change of rings, and apply `leftDerived_from_resolvingClass` to the resulting
functor. (blueprint: q3-ringed-space-tensor-pullback-left-derived)

Proof: choose a K-flat resolution of every complex. Inverse image preserves these
resolutions, and derived change of rings preserves quasi-isomorphisms between the
resulting K-flat complexes. Applying the resolving-class construction to the concrete
tensor pullback gives the displayed derived functor and its K-flat comparison. -/
theorem exists_tensorPullback_leftDerived
    {X Y : RingedSpace.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y))]
    (g : X ⟶ Y)
    (P : SheafOfModules.{u} (moduleRings Y) ⥤ SheafOfModules.{u} (moduleRings X))
    (h : ∀ M : SheafOfModules.{u} (moduleRings Y),
      P.obj M = SheafOfModules.changeOfRings.{u, u, u}
        (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
        (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M))
    (hm : ∀ {M N : SheafOfModules.{u} (moduleRings Y)} (a : M ⟶ N),
      P.map a = eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom.{u, u, u}
        (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
        (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M)
        (TopCat.Sheaf.inverseImageModuleMap g.hom.base Y.sheaf M a) ≫
        eqToHom (h N).symm)
    [P.Additive] :
    ∃ (L : DerivedCategory (SheafOfModules.{u} (moduleRings Y)) ⥤
        DerivedCategory (SheafOfModules.{u} (moduleRings X)))
      (ε : DerivedCategory.Qh ⋙ L ⟶
        P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
      L.IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings Y))
          (ComplexShape.up ℤ)) ∧
      (∀ K : CochainComplex (SheafOfModules.{u} (moduleRings Y)) ℤ,
        K.IsKFlat → IsIso
          (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))) := by
  sorry

/-- Absoluteness of a K-flat derived comparison: the right Kan extension over the
cofinal K-flat resolution category is essentially constant, hence every postcomposition
functor preserves its comparison.  This is the absolute-resolution argument of
Stacks Tags 06XN and 05SE. (blueprint: q3-ringed-space-tensor-pullback-absolute-postcomposition)

Proof: the K-flat resolution category is cofinal and all transition maps are sent to
isomorphisms by the comparison. Its right Kan extension is therefore essentially
constant, so the limiting cone is absolute and remains a left derived comparison after
postcomposition by any functor. -/
theorem leftDerived_tensorPullback_absolute
    {X Y : RingedSpace.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y))]
    (g : X ⟶ Y)
    (P : SheafOfModules.{u} (moduleRings Y) ⥤ SheafOfModules.{u} (moduleRings X))
    (h : ∀ M : SheafOfModules.{u} (moduleRings Y),
      P.obj M = SheafOfModules.changeOfRings.{u, u, u}
        (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
        (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M))
    (hm : ∀ {M N : SheafOfModules.{u} (moduleRings Y)} (a : M ⟶ N),
      P.map a = eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom.{u, u, u}
        (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
        (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M)
        (TopCat.Sheaf.inverseImageModuleMap g.hom.base Y.sheaf M a) ≫
        eqToHom (h N).symm)
    [P.Additive]
    (L : DerivedCategory (SheafOfModules.{u} (moduleRings Y)) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings X)))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hL : L.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings Y))
        (ComplexShape.up ℤ)))
    (hK : ∀ K : CochainComplex (SheafOfModules.{u} (moduleRings Y)) ℤ,
      K.IsKFlat → IsIso
        (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))) :
    ∀ H : DerivedCategory (SheafOfModules.{u} (moduleRings X)) ⥤
        DerivedCategory (SheafOfModules.{u} (moduleRings Y)),
      (L ⋙ H).IsLeftDerivedFunctor
        ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight ε H)
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings Y))
          (ComplexShape.up ℤ)) := by
  sorry

end AlgebraicGeometry.RingedSpace
