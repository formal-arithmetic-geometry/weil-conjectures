/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonData
public import WeilConjectures.AlgebraicGeometry.FixedScalarEtaleModel
import all WeilConjectures.AlgebraicGeometry.FiniteComparisonModelRealization

/-! # The ordinary comparison square for fixed scalars

## References

* [Stacks Project, Tag 03CY](https://stacks.math.columbia.edu/tag/03CY)
* [Stacks Project, Tag 099R](https://stacks.math.columbia.edu/tag/099R)
* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private def inverseEtaleRealization (X : Scheme.{u})
    (k : Type (u + 1)) [CommRing k] :
    (fixedScalarEtaleSheafEquivalence X k).inverse ≅
      ProEtale.finiteComparisonEtaleModelRealization X k := by
  unfold fixedScalarEtaleSheafEquivalence ProEtale.finiteComparisonEtaleModelRealization
  exact Functor.isoWhiskerRight (CategoryTheory.restrictionIso _ k) _

private def inverseProEtaleRealization (X : Scheme.{u})
    (k : Type (u + 1)) [CommRing k] :
    (fixedScalarProEtaleSheafEquivalence X k).inverse ≅
      ProEtale.finiteComparisonProEtaleModelRealization X k := by
  unfold fixedScalarProEtaleSheafEquivalence ProEtale.finiteComparisonProEtaleModelRealization
  exact Functor.isoWhiskerRight (CategoryTheory.restrictionIso _ k) _

/-- Ordinary inverse image commutes with the explicitly fixed scalar presentation functors.
This concerns sheaves alone, with no derived, bounded, constructible or Tor hypothesis.
(Stacks, Tags 03CY, 099R and 00YV.) -/
theorem fixedScalar_ordinary_comparison (X : Scheme.{u})
    (k : Type (u + 1)) [CommRing k] :
    Nonempty ((fixedScalarEtaleSheafEquivalence X k).functor ⋙
        ProEtale.constructibleComparisonPullback.{u, u} X k ≅
      ProEtale.comparisonUpperStar (ModuleCat.{u + 1} k) X ⋙
        (fixedScalarProEtaleSheafEquivalence X k).functor) := by
  let E := fixedScalarEtaleSheafEquivalence X k
  let G := fixedScalarProEtaleSheafEquivalence X k
  let L := ProEtale.constructibleComparisonPullback.{u, u} X k
  let U := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} k) X
  obtain ⟨a⟩ := ProEtale.finiteComparisonModelPullbackSquare X k
  let h : L ⋙ G.inverse ≅ E.inverse ⋙ U :=
    Functor.isoWhiskerLeft L (inverseProEtaleRealization X k) ≪≫ a ≪≫
      Functor.isoWhiskerRight (inverseEtaleRealization X k).symm U
  let b : (E.functor ⋙ L) ⋙ G.inverse ≅ U :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft E.functor h ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight E.unitIso.symm U ≪≫ Functor.leftUnitor U
  let c : (U ⋙ G.functor) ⋙ G.inverse ≅ U :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft U G.unitIso.symm ≪≫ Functor.rightUnitor U
  exact ⟨((Functor.FullyFaithful.ofFullyFaithful G.inverse).whiskeringRight _).preimageIso
    (b ≪≫ c.symm)⟩

end AlgebraicGeometry.Scheme
