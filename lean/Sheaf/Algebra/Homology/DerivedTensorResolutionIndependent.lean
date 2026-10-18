/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.Algebra.Homology.DerivedTensor
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Homotopy

import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Sheaf.Algebra.Homology.KFlatClosure
import Sheaf.Algebra.Homology.AcyclicKFlatTensor
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor

/-!
# Resolution independence of the pro-etale derived tensor product

Source: Weil blueprint, sec-smooth-purity/sk-lem-sf-mate, order 1870;
Stacks Project, Cohomology on Sites, Tags 06YT and 06YU
(blueprint: lem-weil-derived-tensor-resolution-independent).

The comparison family is quantified over all K-flat resolutions of the fixed first factor.
Its characterization by chain maps is imposed for every homotopy lift. No direct lift is
assumed to exist, and no K-flat resolution of the second factor is required.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe w

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

variable (Y : Scheme.{w}) (A : Type w) [CommRing A]

/-- The total tensor complex, specialized to the constant ring sheaf on the pro-etale site.
This is precisely `CochainComplex.mapBifunctor` with the sheaf tensor, as in `derivedTensor`.
Source: Stacks Tag 06YU (blueprint: lem-weil-derived-tensor-resolution-independent). -/
def resolutionTensor (K₂ P : CochainComplex
      (SheafOfModules.{w + 1}
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj
            ((constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
              (CommRingCat.of (ULift.{w + 1, w} A))))) ℤ) :
    CochainComplex
      (SheafOfModules.{w + 1}
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj
            ((constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
              (CommRingCat.of (ULift.{w + 1, w} A))))) ℤ :=
  letI := SheafOfModules.monoidalCategory
    ((constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
      (CommRingCat.of (ULift.{w + 1, w} A)))
  CochainComplex.mapBifunctor P K₂ (curriedTensor _)

/-- The ordinary map `α ⊗ 1`, formed by the recorded total tensor construction.
Source: Stacks Tag 06YT (blueprint: lem-weil-derived-tensor-resolution-independent). -/
def resolutionTensorMap (K₂ : CochainComplex
      (SheafOfModules.{w + 1}
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj
            ((constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
              (CommRingCat.of (ULift.{w + 1, w} A))))) ℤ)
    {P P' : CochainComplex
      (SheafOfModules.{w + 1}
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj
            ((constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
              (CommRingCat.of (ULift.{w + 1, w} A))))) ℤ} (α : P ⟶ P') :
    resolutionTensor Y A K₂ P ⟶ resolutionTensor Y A K₂ P' :=
  letI := SheafOfModules.monoidalCategory
    ((constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
      (CommRingCat.of (ULift.{w + 1, w} A)))
  HomologicalComplex.mapBifunctorMap α (𝟙 K₂) (curriedTensor _) (ComplexShape.up ℤ)

/-- The localization of `α ⊗ 1` between the chosen-resolution models `derivedTensor`.
The localization is exactly `HasDerivedCategory.standard`, as in `proEtaleDerivedCategory`.
Source: Stacks Tag 06YU (blueprint: lem-weil-derived-tensor-resolution-independent). -/
def resolutionTensorMapQ (K₁ K₂ : CochainComplex
      (SheafOfModules.{w + 1}
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj
            ((constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
              (CommRingCat.of (ULift.{w + 1, w} A))))) ℤ)
    {P P' : CochainComplex
      (SheafOfModules.{w + 1}
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj
            ((constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
              (CommRingCat.of (ULift.{w + 1, w} A))))) ℤ}
    (q : P ⟶ K₁) (q' : P' ⟶ K₁) (hq : QuasiIso q) (hq' : QuasiIso q')
    (hP : P.IsAcyclicTensorKFlat) (hP' : P'.IsAcyclicTensorKFlat) (α : P ⟶ P') :
    derivedTensor Y A K₁ K₂ P q hq hP ⟶ derivedTensor Y A K₁ K₂ P' q' hq' hP' :=
  letI := HasDerivedCategory.standard
      (SheafOfModules.{w + 1}
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj
            ((constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
              (CommRingCat.of (ULift.{w + 1, w} A)))))
  DerivedCategory.Q.map (resolutionTensorMap Y A K₂ α)

/-- Resolution independence, including the canonical comparison and all its normalizations.
Source: Stacks Tags 06YT and 06YU and the preceding independence paragraph
(blueprint: lem-weil-derived-tensor-resolution-independent).

Proof:
1. A quasi-isomorphism between K-flat complexes has an acyclic K-flat cone, by
   lem-pur-quasi-iso-cone-acyclic and lem-pc-kflat-cone-direct-sum.
2. Tensor the cone with the arbitrary second complex using
   lem-pur-acyclic-kflat-tensor-arbitrary. The tensor/cone isomorphism
   lem-pc-tensor-mapping-cone-iso and the signed swap identify an acyclic cone for
   the tensor map, so that map is a quasi-isomorphism.
   The swap sends x ⊗ y in bidegree (p,q) to (-1)^(p*q) y ⊗ x; its square is
   the identity, and comparing the two differential terms proves it is a chain map.
3. Represent a derived arrow by a right fraction, using
   lem-pc-quasi-isomorphisms-multiplicative-system and lem-pc-right-fraction-representation.
   Tensor first descends to the homotopy category: for a homotopy h in the first factor,
   H(x ⊗ y) = h(x) ⊗ y satisfies dH + Hd = (dh + hd) ⊗ 1, since the second-factor
   differential terms cancel. Thus homotopy-category equations remain valid after tensoring.
   Resolve its middle complex using lem-pc-kflat-resolution. Tensor numerator and denominator
   and invert the latter by Step 2. The common-refinement criterion
   lem-pc-right-fraction-common-refinement, followed by a K-flat resolution of the refinement,
   proves independence of the roof and every auxiliary choice.
4. Identity roofs give identities. A common K-flat refinement of composable roofs gives
   composition, by tensor functoriality and cancellation of the inverted denominators.
5. Apply this functor to Q(q) followed by the inverse of Q(q'). Cancellation proves the
   identity and cocycle laws. A supplied homotopy lift has precisely this image in the
   localization and is a quasi-isomorphism by two-out-of-three. Step 2 gives its tensor
   quasi-isomorphism and Step 4 gives agreement. Common K-flat refinements of any two
   resolutions also prove uniqueness of the comparison family with this agreement property.
   Indeed, choose a K-flat resolution S with quasi-isomorphisms a : S → P and b : S → P'
   whose composites with q and q' are homotopic. Agreement determines both c(S,P) and
   c(S,P'); the cocycle then forces c(P,P') = c(S,P)⁻¹ followed by c(S,P').
   Its objects are exactly the models in def-weil-derived-tensor. -/
theorem derivedTensor_resolution_independent
    (K₁ K₂ : CochainComplex
      (SheafOfModules.{w + 1}
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj
            ((constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
              (CommRingCat.of (ULift.{w + 1, w} A))))) ℤ) :
    (∀ (P P' : CochainComplex
      (SheafOfModules.{w + 1}
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj
            ((constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
              (CommRingCat.of (ULift.{w + 1, w} A))))) ℤ)
      (q : P ⟶ K₁) (q' : P' ⟶ K₁),
      QuasiIso q → QuasiIso q' → P.IsAcyclicTensorKFlat → P'.IsAcyclicTensorKFlat →
      ∀ (α : P ⟶ P'), Homotopy (α ≫ q') q →
        QuasiIso (resolutionTensorMap Y A K₂ α)) ∧
    ∃! c : ∀ (P P' : CochainComplex
      (SheafOfModules.{w + 1}
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj
            ((constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
              (CommRingCat.of (ULift.{w + 1, w} A))))) ℤ)
      (q : P ⟶ K₁) (q' : P' ⟶ K₁)
      (hq : QuasiIso q) (hq' : QuasiIso q') (hP : P.IsAcyclicTensorKFlat) (hP' : P'.IsAcyclicTensorKFlat),
      (derivedTensor Y A K₁ K₂ P q hq hP ≅ derivedTensor Y A K₁ K₂ P' q' hq' hP'),
      (∀ (P P' : CochainComplex
      (SheafOfModules.{w + 1}
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj
            ((constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
              (CommRingCat.of (ULift.{w + 1, w} A))))) ℤ)
        (q : P ⟶ K₁) (q' : P' ⟶ K₁)
        (hq : QuasiIso q) (hq' : QuasiIso q') (hP : P.IsAcyclicTensorKFlat) (hP' : P'.IsAcyclicTensorKFlat)
        (α : P ⟶ P'), Homotopy (α ≫ q') q →
        (c P P' q q' hq hq' hP hP').hom =
          resolutionTensorMapQ Y A K₁ K₂ q q' hq hq' hP hP' α) ∧
      (∀ (P : CochainComplex
      (SheafOfModules.{w + 1}
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj
            ((constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
              (CommRingCat.of (ULift.{w + 1, w} A))))) ℤ)
        (q : P ⟶ K₁) (hq : QuasiIso q) (hP : P.IsAcyclicTensorKFlat),
        c P P q q hq hq hP hP = Iso.refl _) ∧
      (∀ (P P' P'' : CochainComplex
      (SheafOfModules.{w + 1}
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj
            ((constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
              (CommRingCat.of (ULift.{w + 1, w} A))))) ℤ)
        (q : P ⟶ K₁) (q' : P' ⟶ K₁) (q'' : P'' ⟶ K₁)
        (hq : QuasiIso q) (hq' : QuasiIso q') (hq'' : QuasiIso q'')
        (hP : P.IsAcyclicTensorKFlat) (hP' : P'.IsAcyclicTensorKFlat) (hP'' : P''.IsAcyclicTensorKFlat),
        c P P' q q' hq hq' hP hP' ≪≫ c P' P'' q' q'' hq' hq'' hP' hP'' =
          c P P'' q q'' hq hq'' hP hP'') := by
  sorry

end AlgebraicGeometry.Scheme
