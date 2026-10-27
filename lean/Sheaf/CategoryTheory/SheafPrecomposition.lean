module

public import Sheaf.CategoryTheory.SiteCoveringAxioms

/-! # Precomposition preserving coefficient sheaves

Source: `WeilConjectures/CategoryTheory/Sites/PullbackIsoOfLocallyGenerated.lean`,
the precomposition functor in lines 16–19, with only coefficient-sheaf preservation
(blueprint: def-sf-sheaf-precomposition).
-/

@[expose] public section

set_option autoImplicit false

universe uC vC uD vD uA vA

namespace CategoryTheory.Sheaf

/-- Precomposition on sheaves, assuming exactly preservation of coefficient sheaves.
Its underlying presheaf is `P.op ⋙ H.obj`, and its action on arrows is whiskering.
No continuity on set sheaves, monoidal structure, or sheafification is required.

Source: `WeilConjectures/CategoryTheory/Sites/PullbackIsoOfLocallyGenerated.lean`,
lines 16–19, the functor `P_*` used in the local generators and relations criterion
(blueprint: def-sf-sheaf-precomposition). -/
def precompositionOfSheafPreservation
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {A : Type uA} [Category.{vA} A]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (P : C ⥤ D) (hP : ∀ H : Sheaf K A, Presheaf.IsSheaf J (P.op ⋙ H.obj)) :
    Sheaf K A ⥤ Sheaf J A :=
  ObjectProperty.lift _
    (sheafToPresheaf K A ⋙ (Functor.whiskeringLeft _ _ A).obj P.op) hP

end CategoryTheory.Sheaf
