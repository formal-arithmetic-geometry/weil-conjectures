module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.SpaceDerivedPullback
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Sheaf.AlgebraicGeometry.SpaceAffineHomComparison
public import Sheaf.AlgebraicGeometry.SpaceModuleDerivedExchange
public import Sheaf.AlgebraicGeometry.SpaceAffineSectionsCompositors
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
import Sheaf.AlgebraicGeometry.SpaceDerivedTensorPullback
import Sheaf.AlgebraicGeometry.SpaceAffineModuleHigherImageVanishing
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-! # Base change of a relatively flat closed structure-sheaf kernel

Source: Stacks Project, Tags 0CTQ and 08IR, with affine vanishing Tag 073H
(blueprint: lem-sfb-space-relative-flat-closed-kernel-base-change).

The three auxiliary maps retain the ordinary regular-function structure map and the
universal derived comparison. The theorem identifies the derived exchange with the
isomorphism between degree-zero closed structure images, rather than choosing an
unspecified isomorphism between those objects.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The existing regular-function structure map, transported to the fixed small models.
Source: Stacks, Tag 03G8; Tags 0CTQ and 08IR, structure-module specialization
(blueprint: lem-sfb-space-relative-flat-closed-kernel-base-change). -/
def relativeClosedKernelSmallStructureMap {B : Scheme.{u}} {X Y : AlgebraicSpace B}
    (f : X ⟶ Y) :
    SheafOfModules.unit Y.smallStructureRings ⟶
      (smallModuleDirectImage f).obj (SheafOfModules.unit X.smallStructureRings) :=
  (smallModuleUnitIso Y).hom ≫
    Y.smallModuleRestriction.map (moduleStructureMap f) ≫
    Y.smallModuleRestriction.map
      ((moduleDirectImage f).map
        (fullModuleSection X (SheafOfModules.unit X.smallStructureRings) (𝟙 _)))

/-- The canonical comparison from an ordinary direct image in degree zero to its
unbounded derived image, induced by the universal right-derived unit.
Source: Stacks, Tags 079V and 073H; Tag 08IR, closed structure-module specialization
(blueprint: lem-sfb-space-relative-flat-closed-kernel-base-change). -/
def relativeClosedKernelDirectImageComparison
    {B : Scheme.{u}} {X Y : AlgebraicSpace B}
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
    (f : X ⟶ Y) (M : X.SmallModules) :
    (DerivedCategory.singleFunctor Y.SmallModules 0).obj ((smallModuleDirectImage f).obj M) ⟶
      (derivedDirectImage f).obj ((DerivedCategory.singleFunctor X.SmallModules 0).obj M) :=
  (DerivedCategory.singleFunctorIsoCompQ Y.SmallModules 0).hom.app _ ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
        (smallModuleDirectImage f) (.up ℤ) 0).inv.app M) ≫
    spaceRightDerivedComplexUnit (smallModuleDirectImage f)
      ((HomologicalComplex.single X.SmallModules (.up ℤ) (0 : ℤ)).obj M) ≫
    (derivedDirectImage f).map
      ((DerivedCategory.singleFunctorIsoCompQ X.SmallModules 0).inv.app M)

/-- The derived structure pullback map, adjoint to the regular-function structure map
followed by its right-derived comparison. On local tensors it is multiplication.
Source: Stacks, Tags 03D7 and 06YY; Tag 08IR, structure-module specialization
(blueprint: lem-sfb-space-relative-flat-closed-kernel-base-change). -/
def relativeClosedKernelDerivedStructureMap
    {B : Scheme.{u}} {X Y : AlgebraicSpace B}
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
    (f : X ⟶ Y) :
    (spaceDerivedPullback f).obj Y.derivedStructure ⟶ X.derivedStructure :=
  ((spaceDerivedAdjunction f).homEquiv _ _).symm
    ((DerivedCategory.singleFunctor Y.SmallModules 0).map
        (relativeClosedKernelSmallStructureMap f) ≫
      relativeClosedKernelDirectImageComparison f (SheafOfModules.unit X.smallStructureRings))

/-- Arbitrary scheme base change of a closed kernel flat over the first product factor,
when the second product factor is flat over the base. The existential isomorphisms are
fixed by equalities to the canonical comparison maps; the final equation identifies the
claimed isomorphism with the counit-mate derived exchange.

Source: Stacks Project, Tags 0CTQ and 08IR, with Tag 073H for closed pushforward
(blueprint: lem-sfb-space-relative-flat-closed-kernel-base-change).

Proof:
1. The fibre-product universal property identifies T with the product of the two
base-changed factors, and identifies W with the inverse image of W0
(lem-trf-space-fibre-products-etale-covers).
2. Apply lem-sfb-space-product-tor-independence (0CTQ) with Z'=W0, B'=S0 and B=S.
Its flatness assumptions are exactly hY and hW, so i0 and q are Tor independent.
3. On any scheme test, W is the same fibre product with W0; hence i is closed.
The affine quotient description of a closed immersion makes both i0 and i affine,
and lem-sfb-space-affine-locality makes i0 quasi-compact and quasi-separated.
4. The structure modules are quasi-coherent by their rank-one free presentations.
Closed pushforward preserves this by lem-sfb-space-closed-immersion-quasi-coherent-modules.
By lem-sfb-space-affine-module-higher-image-vanishing (073H), both canonical
ordinary-to-derived comparisons are isomorphisms: positive cohomology vanishes,
negative cohomology vanishes for a degree-zero resolution, and degree zero is unchanged.
5. The complex O_W0[0] is K-flat: tensoring it with an acyclic complex returns that
complex (def-pc-kflat-complex, def-sfb-space-derived-tensor-pullback).
Ordinary pullback of O is O by b tensor c mapping to b times the pullback of c;
the inverse inserts 1. Thus the displayed canonical derived structure map is invertible.
6. Apply lem-sfb-space-tor-independent-base-change (08IR) to i0, q, i, r and O_W0[0].
Steps 2--4 supply Tor independence, qcqs and quasi-coherence. Its comparison is exactly
moduleDerivedExchange. Conjugate it by the canonical isomorphisms of steps 4--5.
This gives alpha and the displayed equation, without flatness of a, X0/S0 or i0,
and without Noetherian or finiteness hypotheses. -/
theorem relativeFlatClosedKernel_baseChange
    (S0 S : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) (a : S ⟶ S0)
    (X0 Y0 T0 T W0 W : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ))))
    [HasDerivedCategory.{w} T0.SmallModules] [HasDerivedCategory.{w} T.SmallModules]
    [HasDerivedCategory.{w} W0.SmallModules] [HasDerivedCategory.{w} W.SmallModules]
    (x0 : X0 ⟶ schemeSpace S0) (y0 : Y0 ⟶ schemeSpace S0)
    (pX : T0 ⟶ X0) (pY : T0 ⟶ Y0) (hT0 : IsPullback pX pY x0 y0)
    (q : T ⟶ T0) (b : T ⟶ schemeSpace S)
    (hT : IsPullback q b (pX ≫ x0)
      (ObjectProperty.homMk
        ((Scheme.fppfTopology.over (Spec (CommRingCat.of (ULift.{u} ℤ)))).yoneda.map a)))
    (i0 : W0 ⟶ T0)
    (hi0 : IsRepresentableWith (fun _ _ c ↦ IsClosedImmersion c.left) i0.hom.hom)
    (hY : MapIsFlat y0) (hW : MapIsFlat (i0 ≫ pX))
    (r : W ⟶ W0) (i : W ⟶ T) (hWsq : IsPullback r i i0 q) :
    IsRepresentableWith (fun _ _ c ↦ IsClosedImmersion c.left) i.hom.hom ∧
      ∃ (e0 : (DerivedCategory.singleFunctor T0.SmallModules 0).obj
            ((smallModuleDirectImage i0).obj (SheafOfModules.unit W0.smallStructureRings)) ≅
          (derivedDirectImage i0).obj W0.derivedStructure)
        (ei : (DerivedCategory.singleFunctor T.SmallModules 0).obj
            ((smallModuleDirectImage i).obj (SheafOfModules.unit W.smallStructureRings)) ≅
          (derivedDirectImage i).obj W.derivedStructure)
        (er : (spaceDerivedPullback r).obj W0.derivedStructure ≅ W.derivedStructure)
        (alpha : (spaceDerivedPullback q).obj
            ((DerivedCategory.singleFunctor T0.SmallModules 0).obj
              ((smallModuleDirectImage i0).obj (SheafOfModules.unit W0.smallStructureRings))) ≅
          (DerivedCategory.singleFunctor T.SmallModules 0).obj
            ((smallModuleDirectImage i).obj (SheafOfModules.unit W.smallStructureRings))),
        e0.hom = relativeClosedKernelDirectImageComparison i0
            (SheafOfModules.unit W0.smallStructureRings) ∧
        ei.hom = relativeClosedKernelDirectImageComparison i
            (SheafOfModules.unit W.smallStructureRings) ∧
        er.hom = relativeClosedKernelDerivedStructureMap r ∧
        alpha.hom ≫ ei.hom =
          (spaceDerivedPullback q).map e0.hom ≫
            moduleDerivedExchange i0 i q r hWsq.w W0.derivedStructure ≫
            (derivedDirectImage i).map er.hom := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
