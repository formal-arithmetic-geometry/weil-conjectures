module

public import Sheaf.AlgebraicGeometry.SpaceAffineCupMaps

import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.CategoryTheory.DerivedBaseChangeMap
import Sheaf.CategoryTheory.RingedSiteLeraySpectralSequence
import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests
import Sheaf.AlgebraicGeometry.SpaceChartLimitEnlargedSections
import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap

/-! # Affine-base relative cup products and base change

Source: Stacks Project, Cohomology on Sites, Tags 0FPN and 0H9A, and
Cohomology of Algebraic Spaces, Tag 08EX
(blueprint: lem-sfb-space-affine-relative-cup-sections).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The normalized affine edge intertwines global and relative cup products and
arbitrary base change. The three conjuncts are respectively (i), (ii), and (iii).
All cohomology objects are classical right derived functors of module sections
or module direct image. Neither tensor pullback nor base change is assumed exact.

Source: Stacks Project, Tags 0FPN, 0H9A and 08EX
(blueprint: lem-sfb-space-affine-relative-cup-sections).

Proof:
1. Pass to the enlarged etale ringed models and use the chart-limit comparison
for direct images. Quasi-compactness and quasi-separatedness persist under base
change. Tensor products and tensor pullbacks preserve local free presentations,
so all the coefficient modules used in the affine edge theorem are quasi-coherent.
Its injective-resolution normalization identifies theta and theta-prime with the
Leray edges, including after the ordinary coefficient tensor or pullback.
2. Transpose composition of cups under the composite pullback adjunction. Both
transposes are the tensor of the two composite counits. Thus global cup is global
sections of relative cup after the global-sections tensor map. Scalar restriction
from global functions to A does not change the pure-tensor formula. Apply the
cohomology tensor pairing and its edge compatibility, then the augmentation
from derived coefficient tensor to ordinary coefficient tensor. This proves (i).
3. The square exchange is the counit mate of the canonical pullback-square
comparison. Paste with global sections: the mate is the global pullback unit,
followed by the coefficient augmentation. The edge-pullback equation therefore
identifies global cohomology pullback with sections pullback followed by the
ordinary degree-q beta, proving (ii). The scalar/cocycle comparison in beta uses
right exactness and asserts no flatness or invertibility.
4. Transpose the base-change cup square. Substituting the defining mate equation
on each factor reduces both paths to the tensor of the two pulled counits.
Monoidality of pullback composition identifies the square comparisons. Coefficient
augmentations agree on local tensors, sending (b tensor m) tensor (c tensor n)
to bc tensor (m tensor n). On flat K-flat representatives the scalar/cocycle map
sends 1 tensor (z tensor w) to the tensor of 1 tensor z and 1 tensor w.
Changing either cycle by a boundary changes the pairing by a boundary (with the
usual degree-a sign in the second factor). Descent to cohomology and sheafification
therefore give (iii) as an equality of sheaf morphisms, hence on all local sections.
-/
theorem affine_relative_cup_sections
    {A B : Type u} [CommRing A] [CommRing B]
    {Y Y' : Over S} (e : Y.left ≅ Spec (.of A)) (e' : Y'.left ≅ Spec (.of B))
    (g : Y' ⟶ Y) {X X' : AlgebraicSpace S}
    (f : X ⟶ schemeSpace Y) (h : X' ⟶ X) (k : X' ⟶ schemeSpace Y')
    (sq : IsPullback h.hom k.hom f.hom
      ((ObjectProperty.homMk ((Scheme.fppfTopology.over S).yoneda.map g) :
        schemeSpace Y' ⟶ schemeSpace Y).hom))
    (hqc : IsQuasiCompactPresheafMap f.hom.hom)
    (hqs : IsQuasiCompactPresheafMap (diagonalPresheafMap f.hom.hom)) :
    (∀ (M N : X.QCoh) (a b : ℕ)
      (x : (affineBaseModuleCohomology A Y e X f a).obj M)
      (y : (affineBaseModuleCohomology A Y e X f b).obj N),
      (affineCupEdge A Y e X f (a + b)).app (cupTensor X (X.smallModuleRestriction.obj M.obj)
        (X.smallModuleRestriction.obj N.obj))
          (affineGlobalCup A Y e X f (X.smallModuleRestriction.obj M.obj)
            (X.smallModuleRestriction.obj N.obj) a b x y) =
        (affineScalarSections A Y e (schemeSpace Y) (𝟙 _)).map
          (spaceModuleCup f (X.smallModuleRestriction.obj M.obj) (X.smallModuleRestriction.obj
            N.obj) a b)
          (affineSectionTensor A Y e (schemeSpace Y) (𝟙 _) _ _
            ((affineCupEdge A Y e X f a).app (X.smallModuleRestriction.obj M.obj) x)
            ((affineCupEdge A Y e X f b).app (X.smallModuleRestriction.obj N.obj) y))) ∧
    (∀ (M : X.QCoh) (q : ℕ),
      affineCupCohomologyPullback e e' g f h k (ObjectProperty.hom_ext _ sq.w)
        (X.smallModuleRestriction.obj M.obj) q ≫
          (ModuleCat.restrictScalars (spaceAffineRingMap e e' g)).map
            ((affineCupEdge B Y' e' X' k q).app ((smallModuleTensorPullback h).obj
              (X.smallModuleRestriction.obj M.obj))) =
        (affineCupEdge A Y e X f q).app (X.smallModuleRestriction.obj M.obj) ≫
          affineCupSectionPullback e e' g (𝟙 _) _ (𝟙 _)
            ((Category.comp_id _).trans (Category.id_comp _).symm)
            (((smallModuleDirectImage f).rightDerived q).obj (X.smallModuleRestriction.obj M.obj)) ≫
          (ModuleCat.restrictScalars (spaceAffineRingMap e e' g)).map
            ((affineScalarSections B Y' e' (schemeSpace Y') (𝟙 _)).map
              (cupModuleBaseChange f _ h k (ObjectProperty.hom_ext _ sq.w)
                (X.smallModuleRestriction.obj M.obj) q))) ∧
    (∀ (M N : X.QCoh) (a b : ℕ),
      (smallModuleTensorPullback (ObjectProperty.homMk ((Scheme.fppfTopology.over S).yoneda.map g) :
            schemeSpace Y' ⟶ schemeSpace Y)).map (spaceModuleCup f (X.smallModuleRestriction.obj
              M.obj) (X.smallModuleRestriction.obj N.obj) a b) ≫
          cupModuleBaseChange f (ObjectProperty.homMk ((Scheme.fppfTopology.over S).yoneda.map g) :
            schemeSpace Y' ⟶ schemeSpace Y) h k (ObjectProperty.hom_ext _ sq.w)
            (cupTensor X (X.smallModuleRestriction.obj M.obj) (X.smallModuleRestriction.obj N.obj))
              (a + b) =
        (SingleComplex.ordinaryTensor (ObjectProperty.homMk ((Scheme.fppfTopology.over
          S).yoneda.map g) :
            schemeSpace Y' ⟶ schemeSpace Y)
          (((smallModuleDirectImage f).rightDerived a).obj (X.smallModuleRestriction.obj M.obj))
          (((smallModuleDirectImage f).rightDerived b).obj (X.smallModuleRestriction.obj
            N.obj))).hom ≫
          (SheafOfModules.monoidalCategory (schemeSpace Y').smallStructureSheaf).tensorHom
            (cupModuleBaseChange f (ObjectProperty.homMk ((Scheme.fppfTopology.over S).yoneda.map
              g) :
            schemeSpace Y' ⟶ schemeSpace Y) h k (ObjectProperty.hom_ext _ sq.w)
              (X.smallModuleRestriction.obj M.obj) a)
            (cupModuleBaseChange f (ObjectProperty.homMk ((Scheme.fppfTopology.over S).yoneda.map
              g) :
            schemeSpace Y' ⟶ schemeSpace Y) h k (ObjectProperty.hom_ext _ sq.w)
              (X.smallModuleRestriction.obj N.obj) b) ≫
          spaceModuleCup k ((smallModuleTensorPullback h).obj (X.smallModuleRestriction.obj M.obj))
            ((smallModuleTensorPullback h).obj (X.smallModuleRestriction.obj N.obj)) a b ≫
          ((smallModuleDirectImage k).rightDerived (a + b)).map
            (SingleComplex.ordinaryTensor h (X.smallModuleRestriction.obj M.obj)
              (X.smallModuleRestriction.obj N.obj)).inv) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
