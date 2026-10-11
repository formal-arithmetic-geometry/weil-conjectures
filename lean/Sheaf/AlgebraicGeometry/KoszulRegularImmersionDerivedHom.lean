module

public import Sheaf.AlgebraicGeometry.LocallyRankedExteriorComplex
public import Sheaf.RingTheory.KoszulRegularSequence
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Derived Hom for a Koszul-regular closed immersion

Source: Stacks Project, Duality for Schemes, Tag 0BQZ
(blueprint: lem-sc-koszul-regular-immersion-derived-hom).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The derived internal Hom of the pushed-forward structure sheaf of a
Koszul-regular closed immersion is the pushforward of the shifted top exterior
power of the dual conormal sheaf.

Source: Stacks Project, Duality for Schemes, Tag 0BQZ, lemma-regular-immersion-ext
(blueprint: lem-sc-koszul-regular-immersion-derived-hom).

The proof uses the local finite-free Koszul model, the affine dual-Koszul
calculation, and restriction of derived internal Hom to opens.  The local
isomorphisms agree under localization and changes of regular generators; their
cohomology-sheaf identifications therefore glue, and the truncation of the
resulting object gives the displayed global isomorphism.
-/
theorem koszulRegularImmersion_derivedInternalHom
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (hregular : ∀ z : Z, ∃ U : Y.affineOpens, i z ∈ U.1 ∧
      ∃ (n : ℕ) (f : Fin n → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f)
    (r : LocallyConstant Z ℕ)
    (hr : ∀ z : Z, r z = Module.finrank (Z.presheaf.stalk z)
      ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules))) :
    Nonempty
      ((derivedInternalHom (Opens.grothendieckTopology Y)
          Y.toRingedSpace.sheaf).obj
        (op ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
            ((Scheme.Modules.pushforward i).obj
              (SheafOfModules.unit Z.ringCatSheaf))),
          (DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
            (SheafOfModules.unit Y.ringCatSheaf)) ≅
        (DerivedCategory.Q.obj
          (((Scheme.Modules.pushforward i).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
            (Scheme.Modules.locallyRankedExteriorComplex
              (SheafOfModules.homObj (R := Z.sheaf)
                ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
                (SheafOfModules.unit Z.ringCatSheaf)) r)))) := by
  sorry

end AlgebraicGeometry
