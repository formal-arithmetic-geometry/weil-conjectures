module
public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Sheaf.Paper.StrictHenselizationLocalStructure
public import Sheaf.RingTheory.StrictHenselizationNoetherian
public import Mathlib.RingTheory.RegularLocalRing.Defs
@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme
/-- Noetherianity of the canonical strict henselization over a regular affine ring.
Source: Stacks Project, Tag 06LJ, applied to the local ring at the geometric point.
The proof identifies the coordinate-ring colimit with the ring strict henselization.
(blueprint: lem-sbc-strict-hensel-regular-divisor-quotient-noetherian)
-/
theorem strictHenselizationRing_noetherian_of_regular
    (R : CommRingCat.{u}) [IsRegularRing R]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY) :
    IsNoetherianRing (strictHenselizationRing barY) := by
  sorry
end AlgebraicGeometry.Scheme
