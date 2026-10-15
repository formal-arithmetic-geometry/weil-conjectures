module
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleModelRingPresentation
import Sheaf.CategoryTheory.ModuleInverseImageAdjunction
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
/-- A canonical adjunction for module inverse image has an invertible underlying unit mate.

This isolates the strict `AsSmall` transport and the module-action comparison from the
uniqueness argument for arbitrary adjunctions.  Its proof follows Tags 03D2 and 03D3:
transport the module pullback adjunction through the two site equivalences and use the
unit-compatible underlying comparison supplied by the model presentation.
(blueprint: new-lem-weil-pbc-proetale-module-canonical-unit) -/
theorem proEtaleModuleInverseImage_canonicalUnitComparison {X Z : Scheme.{u}} (i : Z ⟶ X)
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    ∃ (adj₀ : (proEtaleModuleInverseImage i A ⊣
      (SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange i)
      (J := ProEt.topology X) (K := ProEt.topology Z)
      (S := ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) (R := ((sheafCompose (ProEt.topology Z)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj A)))
      ⟨Functor.whiskerRight
        ((proEtaleSheafAdjunction i CommRingCat.{u + 1}).unit.app A).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩))),
      let S := (sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A
      let R := (sheafCompose (ProEt.topology Z)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj A)
      ∀ M, IsIso (((proEtaleSheafAdjunction i AddCommGrpCat.{u + 1}).homEquiv
        ((SheafOfModules.toSheaf S).obj M)
        ((SheafOfModules.toSheaf R).obj ((proEtaleModuleInverseImage i A).obj M))).symm
          ((SheafOfModules.toSheaf S).map (adj₀.unit.app M))) := by
  sorry
end AlgebraicGeometry.Scheme
