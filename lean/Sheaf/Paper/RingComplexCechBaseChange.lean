/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.Paper.RingComplexSemilinearExtension
public import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Paper.RingComplexCechData
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-! # Base change detected by augmented ordered localization models -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry

/-- The normalized scalar-extension map between augmented localization models is a
quasi-isomorphism on every K-flat replacement.
Source: Stacks Project, Tags 099D(c), 0A6R, 0ALZ;
Tag 06YQ for bounded flat complexes.
(blueprint: lem-weil-pbc-ring-complex-cech-base-change)

Proof: choose a finite generating list for I. Its ordered localization complex is
bounded and termwise flat: finite products are finite direct sums, localizations
are flat, and degrees outside the finite range are zero. It is therefore K-flat.
For an augmented derived model isomorphism, choose a common cochain roof and
replace its source by a K-flat resolution. Both legs are quasi-isomorphisms between
K-flat complexes. The existing changeOfRings_kFlat_quasiIso theorem preserves both
legs under the actual scalar-extension functor, so the resulting derived scalar
extension comparison is invertible. The fraction maps (a/g^n) tensor b to
phi(a)b/phi(g)^n identify its scalar extension with the localization complex for
the image list, including the differential and
augmentation. To identify the map, use the universal property of local cohomology:
for an extended localization complex C and any complex T whose localization at
each generator vanishes, composition Hom(T,C) to Hom(T,B[0]) with the augmentation
is bijective. Indeed the cone of C to B[0] is a finite iterated extension of
localization modules, and derived Hom from T into any of these is zero by the
localization/restriction adjunction. This includes their shifts. The scalar
extension of P is supported on the image ideal, because its derived object is
the scalar extension of C, and C becomes contractible after any generator is
inverted (insert or delete that index with its ordered sign). The given
augmentation equation identifies the induced map with the fraction comparison
under the two augmented derived model isomorphisms, by this bijectivity. Hence
it is invertible. K-flatness makes ordinary extension of P compute its derived
extension, so the actual normalized map is a quasi-isomorphism. For the empty
list this is the identity comparison to the ring; localization at zero gives
the zero module and the argument remains valid. -/
theorem ringComplex_cech_baseChange_quasiIso
    (A B : CommRingCat.{u}) [HasDerivedCategory.{w} (RingSiteModules A)]
    [HasDerivedCategory.{w} (RingSiteModules B)] (φ : A →+* B)
    (I : {I : Ideal A // I.FG}) (J : {J : Ideal B // J.FG})
    (h : I.val.map φ = J.val)
    (P : CochainComplex (RingSiteModules A) ℤ)
    (L : CochainComplex (RingSiteModules B) ℤ)
    (εP : P ⟶ ringComplexSingle A) (εL : L ⟶ ringComplexSingle B)
    (hCA : RingComplexHasCechModel A I.val P εP)
    (hCB : RingComplexHasCechModel B J.val L εL)
    (hP : P.IsAcyclicTensorKFlat) (χ : ringComplexExtensionComplex φ P ⟶ L)
    (hε : ∀ x : (P.X 0).val.obj (op ⟨PUnit.unit⟩),
      ringComplexAugmentationValue εL
          ((χ.f 0).val.app (op ⟨PUnit.unit⟩)
            ((toSheafify ⊥ (SheafOfModules.changeOfRingsPresheaf
              (ringSiteMap φ) (P.X 0)).presheaf).app (op ⟨PUnit.unit⟩)
                ((1 : B) ⊗ₜ[A, φ] x))) = φ (ringComplexAugmentationValue εP x)) :
    QuasiIso χ := by sorry

end AlgebraicGeometry
