module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Sheaf.AlgebraicGeometry.Morphisms.PuncturedSectionsComplex
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-! The comparison maps underlying the flasque resolution computation.

Source: Stacks Project, Tags 09T2 and 0A6T.
(blueprint: new-punctured-flasque-resolution-comparison).
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The comparison maps from cohomology to the sections homology and back.
Source: Stacks Project, Tags 09T2 and 0A6T; acyclic-resolution comparison.
(blueprint: new-punctured-flasque-resolution-comparison).
-/
theorem punctured_flasque_resolution_comparison_maps
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (W : (Spec (.of R)).Opens)
    (I : InjectiveResolution (ModuleCat.of R R : ModuleCat.{u} R)) (n : ℕ) :
    ∃ f : Modules.H (X := W.toScheme)
        (SheafOfModules.unit W.toScheme.ringCatSheaf) n →+
        ((puncturedSectionsComplex R W I.cocomplex).homology n).carrier,
      ∃ g : ((puncturedSectionsComplex R W I.cocomplex).homology n).carrier →+
        Modules.H (X := W.toScheme)
          (SheafOfModules.unit W.toScheme.ringCatSheaf) n,
      (Function.LeftInverse g f) ∧ (Function.RightInverse g f) := by
  sorry

end AlgebraicGeometry.Scheme
