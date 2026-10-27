module

public import Sheaf.Paper.ProjectionMateExact
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.CategoryTheory.GlobalModuleAbelianCohomology
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Mathlib.CategoryTheory.Linear.Yoneda
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal
public import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-! # Cocycle and augmentation maps for ringed-site tensor

Source: Stacks Project, Cohomology on Sites, Tags 0B6C and 0FPJ
(blueprint: def-sfb-ringed-site-cohomology-tensor-maps).

The cohomology pairing is fixed on every flat K-flat representative by the
signed total-tensor cocycle formula. The augmentation to ordinary tensor is fixed
on every pair of resolution augmentations. These normalizations determine maps,
rather than permitting a choice of an uncharacterized pairing.

## Main definitions
- `cohomologyPairing`: the signed cocycle-normalized pairing on cohomology sheaves.
- `tensorAugmentation`: the canonical derived-to-ordinary tensor augmentation.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace SheafOfModules.RingedSiteCup

/-- Cohomology sheaves of the existing unbounded derived category.
Source: Stacks Project, Tag 0B6C
(blueprint: def-sfb-ringed-site-cohomology-tensor-maps). -/
abbrev cohomology (X : RingedTensorCorner.{u, w}) (n : ℤ) :=
  DerivedCategory.homologyFunctor X.mateModules n

/-- Modules placed in degree zero in the existing derived category.
Source: Stacks Project, Tag 0B6C
(blueprint: def-sfb-ringed-site-cohomology-tensor-maps). -/
abbrev degreeZero (X : RingedTensorCorner.{u, w}) :=
  DerivedCategory.singleFunctor X.mateModules 0

/-- The canonical identification from complex cohomology to derived cohomology.
Source: Stacks Project, Tag 0B6C, and derived-category localization
(blueprint: def-sfb-ringed-site-cohomology-tensor-maps). -/
def representativeCohomology (X : RingedTensorCorner.{u, w})
    (P : CochainComplex X.mateModules ℤ) (n : ℤ) :
    P.homology n ≅ (cohomology X n).obj (DerivedCategory.Q.obj P) :=
  (DerivedCategory.homologyFunctorFactors X.mateModules n).symm.app P

/-- The cocycle normalization for a cohomology pairing. The lift `z` is unique because
`iCycles` is monic. The second equation descends the pure-tensor cocycle prescription
through the two homology quotients, hence includes its sheafification.
Source: Stacks Project, Tags 0B6C and 0FPJ, signed total tensor
(blueprint: def-sfb-ringed-site-cohomology-tensor-maps). -/
def CohomologyPairingSpec (X : RingedTensorCorner.{u, w}) (b : RingedTensorModel X)
    (U V : X.mateDerived) (p q : ℤ)
    (c : (cohomology X p).obj U ⊗ (cohomology X q).obj V ⟶
      (cohomology X (p + q)).obj (X.tensor.obj (U, V))) : Prop :=
  ∀ (P Q : CochainComplex X.mateModules ℤ) (hP : X.mateFlat P) (hQ : X.mateFlat Q)
    (i : DerivedCategory.Q.obj P ≅ U) (j : DerivedCategory.Q.obj Q ≅ V),
    ∃ z : P.cycles p ⊗ Q.cycles q ⟶
        (CochainComplex.mapBifunctor P Q X.mateTensor).cycles (p + q),
      z ≫ (CochainComplex.mapBifunctor P Q X.mateTensor).iCycles (p + q) =
        (P.iCycles p ⊗ₘ Q.iCycles q) ≫
          HomologicalComplex.ιMapBifunctor P Q X.mateTensor (.up ℤ) p q (p + q) rfl ∧
      ((P.homologyπ p ≫ (representativeCohomology X P p).hom ≫
          (cohomology X p).map i.hom) ⊗ₘ
        (Q.homologyπ q ≫ (representativeCohomology X Q q).hom ≫
          (cohomology X q).map j.hom)) ≫ c =
        z ≫ (CochainComplex.mapBifunctor P Q X.mateTensor).homologyπ (p + q) ≫
          (representativeCohomology X _ (p + q)).hom ≫
          (cohomology X (p + q)).map
            (b.mateRepresentative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) ≫
              X.tensor.map (Prod.mkHom i.hom j.hom))

/-- Existence and uniqueness of the cocycle-normalized pairing used in the definition.
Source: Stacks Project, Tags 0B6C and 0FPJ; K-flat descent, Tag 06YU
(blueprint: def-sfb-ringed-site-cohomology-tensor-maps).

Proof: on flat K-flat representatives, the signed Leibniz formula sends a tensor of
cycles to a cycle of the total tensor. If the first input is a boundary, its tensor
with a cycle is a total boundary. If the second input is a boundary, the same holds
with sign (-1)^p. Tensor is right exact on module sheaves, so the bilinear morphism
on cycles descends uniquely through both homology quotients. This is precisely
sheafification of the local formula [x] tensor [y] maps to [x tensor y]. The maps
commute with maps of representative complexes and their quasi-isomorphisms.
Flat K-flat descent identifies their localization with the derived category, so
the maps extend to U,V. Every U,V has such representatives; the homology quotient
maps and their tensor are epimorphisms, proving uniqueness. -/
theorem cohomologyPairing_existsUnique (X : RingedTensorCorner.{u, w})
    (b : RingedTensorModel X) (U V : X.mateDerived) (p q : ℤ) :
    ∃! c : (cohomology X p).obj U ⊗ (cohomology X q).obj V ⟶
        (cohomology X (p + q)).obj (X.tensor.obj (U, V)),
      CohomologyPairingSpec X b U V p q c := by
  sorry

/-- The pairing κ, selected by its unique cocycle normalization, in all integer degrees.
Source: Stacks Project, Tags 0B6C and 0FPJ
(blueprint: def-sfb-ringed-site-cohomology-tensor-maps). -/
def cohomologyPairing (X : RingedTensorCorner.{u, w}) (b : RingedTensorModel X)
    (U V : X.mateDerived) (p q : ℤ) :
    (cohomology X p).obj U ⊗ (cohomology X q).obj V ⟶
      (cohomology X (p + q)).obj (X.tensor.obj (U, V)) :=
  Classical.choose (cohomologyPairing_existsUnique X b U V p q)

/-- The degree-zero normalization of the tensor of two single complexes.
Source: Stacks Project, Tag 0B6C, ordinary tensor augmentation
(blueprint: def-sfb-ringed-site-cohomology-tensor-maps). -/
def SingleTensorSpec (X : RingedTensorCorner.{u, w}) (F G : X.mateModules)
    (t : CochainComplex.mapBifunctor
      ((CochainComplex.singleFunctor X.mateModules 0).obj F)
      ((CochainComplex.singleFunctor X.mateModules 0).obj G) X.mateTensor ⟶
        (CochainComplex.singleFunctor X.mateModules 0).obj (F ⊗ G)) : Prop :=
  HomologicalComplex.ιMapBifunctor _ _ X.mateTensor (.up ℤ) 0 0 0 rfl ≫ t.f 0 =
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 F).hom ⊗ₘ
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 G).hom) ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (F ⊗ G)).inv

/-- The ordinary tensor identification of degree-zero complexes is uniquely normalized.
Source: Stacks Project, Tag 0B6C
(blueprint: def-sfb-ringed-site-cohomology-tensor-maps).

Proof: the only nonzero tensor summand is the (0,0) summand in degree zero.
Use the single-complex identifications on that summand and the zero map in all
other degrees. Every differential is zero. The coproduct universal property
shows uniqueness, including summands whose factors are zero. -/
theorem singleTensor_existsUnique (X : RingedTensorCorner.{u, w}) (F G : X.mateModules) :
    ∃! t : CochainComplex.mapBifunctor
        ((CochainComplex.singleFunctor X.mateModules 0).obj F)
        ((CochainComplex.singleFunctor X.mateModules 0).obj G) X.mateTensor ⟶
          (CochainComplex.singleFunctor X.mateModules 0).obj (F ⊗ G),
      SingleTensorSpec X F G t := by
  sorry

/-- The uniquely normalized map Tot(F[0] tensor G[0]) to (F tensor G)[0].
Source: Stacks Project, Tag 0B6C
(blueprint: def-sfb-ringed-site-cohomology-tensor-maps). -/
def singleTensor (X : RingedTensorCorner.{u, w}) (F G : X.mateModules) :
    CochainComplex.mapBifunctor
      ((CochainComplex.singleFunctor X.mateModules 0).obj F)
      ((CochainComplex.singleFunctor X.mateModules 0).obj G) X.mateTensor ⟶
        (CochainComplex.singleFunctor X.mateModules 0).obj (F ⊗ G) :=
  Classical.choose (singleTensor_existsUnique X F G)

/-- The augmentation is specified on every flat K-flat resolution of F[0] and G[0].
Source: Stacks Project, Tag 0B6C
(blueprint: def-sfb-ringed-site-cohomology-tensor-maps). -/
def TensorAugmentationSpec (X : RingedTensorCorner.{u, w}) (b : RingedTensorModel X)
    (F G : X.mateModules)
    (t : X.tensor.obj ((degreeZero X).obj F, (degreeZero X).obj G) ⟶
      (degreeZero X).obj (F ⊗ G)) : Prop :=
  ∀ (P Q : CochainComplex X.mateModules ℤ) (hP : X.mateFlat P) (hQ : X.mateFlat Q)
    (i : P ⟶ (CochainComplex.singleFunctor X.mateModules 0).obj F)
    (j : Q ⟶ (CochainComplex.singleFunctor X.mateModules 0).obj G)
    (_hi : QuasiIso i) (_hj : QuasiIso j),
    b.mateRepresentative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) ≫
      X.tensor.map (Prod.mkHom (DerivedCategory.Q.map i) (DerivedCategory.Q.map j)) ≫ t =
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap i j X.mateTensor (.up ℤ) ≫ singleTensor X F G)

/-- The canonical augmentation from derived to ordinary tensor is uniquely determined.
Source: Stacks Project, Tag 0B6C; K-flat tensor descent, Tag 06YU
(blueprint: def-sfb-ringed-site-cohomology-tensor-maps).

Proof: take flat K-flat resolutions P to F[0] and Q to G[0]. Tensor their
augmentations and follow with the ordinary single-tensor map. The comparison
from Q(Tot(P tensor Q)) to the derived tensor is invertible, as are the images
of the two augmentations. Compose with their inverses to get t. Comparison maps
between resolutions commute with these chain maps. The localization property
therefore proves independence and the equation for every pair of resolutions.
The invertible comparison for any one such pair proves uniqueness. -/
theorem tensorAugmentation_existsUnique (X : RingedTensorCorner.{u, w})
    (b : RingedTensorModel X) (F G : X.mateModules) :
    ∃! t : X.tensor.obj ((degreeZero X).obj F, (degreeZero X).obj G) ⟶
        (degreeZero X).obj (F ⊗ G),
      TensorAugmentationSpec X b F G t := by
  sorry

/-- The canonical map F[0] tensor-derived G[0] to (F tensor G)[0].
Source: Stacks Project, Tag 0B6C
(blueprint: def-sfb-ringed-site-cohomology-tensor-maps). -/
def tensorAugmentation (X : RingedTensorCorner.{u, w}) (b : RingedTensorModel X)
    (F G : X.mateModules) :
    X.tensor.obj ((degreeZero X).obj F, (degreeZero X).obj G) ⟶
      (degreeZero X).obj (F ⊗ G) :=
  Classical.choose (tensorAugmentation_existsUnique X b F G)


end SheafOfModules.RingedSiteCup
