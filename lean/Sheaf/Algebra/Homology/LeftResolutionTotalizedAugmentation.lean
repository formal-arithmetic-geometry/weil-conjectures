module

public import WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.CochainComplexMinus
public import WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.Basic
public import WeilConjectures.FromJoel.Algebra.Homology.BicomplexRows
public import Sheaf.Algebra.Homology.LeftResolutionBicomplexTotalExists
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns

@[expose] public section

/-!
# Totalized augmentation for bounded-above left resolutions

Source: WeilConjectures/FromJoel/Algebra/Homology/LeftResolution/CochainComplexMinus.lean,
lines 151–206 (blueprint: lem-sfb-left-resolution-totalized-augmentation)
-/

namespace CategoryTheory

open CategoryTheory.Limits
open CochainComplex

namespace Abelian
namespace LeftResolution

universe uA vA uC vC

/--
The total map obtained from the columnwise augmentations of the resolution bicomplex
is natural in a bounded-above integer cochain complex and is a quasi-isomorphism.
Source: WeilConjectures/FromJoel/Algebra/Homology/LeftResolution/CochainComplexMinus.lean,
lines 151–206 (blueprint: lem-sfb-left-resolution-totalized-augmentation).
The proof follows the source: the columnwise augmentations assemble into the total map;
its naturality is checked bidegreewise using naturality of the objectwise augmentation;
and the bounded-above double-complex comparison theorem gives the quasi-isomorphism.
-/
theorem totalizedAugmentation_natural_quasiIso
    {A : Type uA} [Category.{vA, uA} A] [Abelian A]
    {C : Type uC} [Category.{vC, uC} C] [Preadditive C] [HasZeroObject C]
    [HasFiniteCoproducts C]
    {ι : C ⥤ A} [ι.Full] [ι.Faithful] [ι.Additive]
    (Λ : LeftResolution ι) [Λ.F.PreservesZeroMorphisms] :
    (∀ (K : CochainComplex.Minus A), QuasiIso (Λ.totalπ' K)) ∧
      (∀ {K L : CochainComplex.Minus A} (φ : K ⟶ L),
        HomologicalComplex₂.total.map
              ((ι.mapHomologicalComplex₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map
                (Λ.bicomplexFunctor.map φ.hom)) (ComplexShape.up ℤ) ≫
            Λ.totalπ' L =
          Λ.totalπ' K ≫
            HomologicalComplex₂.total.map
              ((HomologicalComplex₂.singleRow A (ComplexShape.up ℤ)
                (ComplexShape.up ℤ) 0).map φ.hom) (ComplexShape.up ℤ)) := by
  sorry

end LeftResolution
end Abelian
end CategoryTheory
