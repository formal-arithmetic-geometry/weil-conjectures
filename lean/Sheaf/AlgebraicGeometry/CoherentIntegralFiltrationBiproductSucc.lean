module

public import Sheaf.AlgebraicGeometry.CoherentIntegralFiltration
public import Mathlib.AlgebraicGeometry.Noetherian

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A coherent filtration extends across a coherent split biproduct, with the
new summand supplying the final integral-ideal quotient witness.
Source: Stacks Project, Tag 01YF, final paragraph of `lemma-coherent-filter`.
(blueprint: new-coherent-integral-filtration-biproduct-succ)
-/
theorem hasCoherentIntegralFiltration_of_biproduct
    {X : Scheme.{u}} (F A G : X.Modules)
    (hF : HasCoherentIntegralFiltration F)
    (hA : RingedSpace.IsCoherent X.toRingedSpace A)
    (hAw : ∃ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i ∧ IsIntegral Z ∧
      ∃ I : Z.IdealSheafData, I ≠ ⊥ ∧
        RingedSpace.IsCoherent Z.toRingedSpace I.toModules ∧
        Nonempty (A ≅ (pushforward i).obj I.toModules))
    (e : G ≅ F ⊞ A) :
    HasCoherentIntegralFiltration G := by
  sorry

end AlgebraicGeometry.Scheme.Modules
