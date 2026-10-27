/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Homology.SheafComplexDerivedTensorVanishes
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Topology.InverseImageModule
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.AlgebraicGeometry.PseudoCoherentQCoh
import WeilConjectures.AlgebraicGeometry.AffinePseudoCoherentCriterion
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.RingedSiteRestrictionKFlat
import Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
import Sheaf.AlgebraicGeometry.AffineRelativeTorAmplitudeCriterion
import Sheaf.Algebra.Homology.RingedFlatSingleTensorCohomology
import Mathlib.RingTheory.FiniteType
import WeilConjectures.RingTheory.FiniteFreeResolution
import Mathlib.RingTheory.Flat.Stability
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Relative affine Tor bounds and diagonal finiteness

Source: Stacks Project, Tags 0E2U, 0DHY, 08E7, 00LP and 00HI
(blueprint: lem-trf-affine-relative-tor-diagonal-finiteness).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u wA wR wB wU

open CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry

/-- Forget the structure-sheaf scalars along the actual inverse-image structure map.
Source: Stacks Project, Tag 0DHY, the object in `D(g⁻¹𝒪_V)`
(blueprint: lem-trf-affine-relative-tor-diagonal-finiteness). -/
abbrev affineTorScalarRestriction {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A) :
    SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) ⥤
      SheafOfModules.{u}
        ((sheafCompose (Opens.grothendieckTopology (Spec (.of A)))
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (TopCat.Sheaf.inverseImageRing (Spec.map (CommRingCat.ofHom φ)).base
              (Spec (.of R)).sheaf)) :=
  SheafOfModules.restrictScalars
    ((sheafCompose (Opens.grothendieckTopology (Spec (.of A)))
      (forget₂ CommRingCat.{u} RingCat.{u})).map
        (Scheme.Modules.tensorPullbackRingMap (Spec.map (CommRingCat.ofHom φ))))

/-- The first-projection pullback is the localization of exact termwise scalar extension.
The map is `p₁(a) = a ⊗ 1`, and flatness supplies exactness; no model is chosen.
Source: Stacks Project, Tags 00HI and 06YU
(blueprint: lem-trf-affine-relative-tor-diagonal-finiteness). -/
def affineDiagonalPullback {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wB} (ModuleCat.{u} (A ⊗[R] A))]
    (hflat : (algebraMap A (A ⊗[R] A)).Flat) :
    DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} (A ⊗[R] A)) :=
  have : (ModuleCat.extendScalars (algebraMap A (A ⊗[R] A))).Additive :=
    (ModuleCat.extendRestrictScalarsAdj (algebraMap A (A ⊗[R] A))).left_adjoint_additive
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  (ModuleCat.extendScalars (algebraMap A (A ⊗[R] A))).mapDerivedCategory

/-- A pseudo-coherent affine complex with locally finite inverse-image tests has a
uniform relative Tor interval. The Noetherian tensor square has a pseudo-coherent
cyclic diagonal module; its flat first projection preserves cohomology bounds.
The witness `C` presents `M = Q(C)` and its termwise tilde presents `E`. The last
three comparisons express computation by the flat degree-zero module and natural
scalar-extension cohomology isomorphisms, including their `B`-module structure.

Source: Stacks Project, Tag 0E2U, affine finiteness prerequisites; Tags 08E5, 06Z0,
08E7, 0DHY, 00FN, 00LP, 00HI and 06YU
(blueprint: lem-trf-affine-relative-tor-diagonal-finiteness).

Proof:
1. Pseudo-coherence gives quasi-coherent cohomology (lem-sc-pseudo-coherent-qcoh).
   The affine equivalence (lem-pc-affine-qcoh-derived-equivalence) supplies `C`;
   lem-pc-affine-pseudo-coherent-criterion makes `Q(C)` pseudo-coherent over A.
2. Quasi-compactness of Spec A (lem-weil-pbc-affine-scheme-qcqs) gives a finite
   subcover of the hypothesized neighbourhoods. Take the minimum lower and maximum
   upper bound; for empty Spec A use [0,0]. Resolve over the inverse-image ring by
   lem-pc-kflat-resolution. Restriction is exact and preserves K-flatness by
   lem-sfb-ringed-site-restriction-kflat; tensor restriction is the comparison of
   lem-sfb-localized-site-tensor-restriction. Sheaf separatedness then gives one
   global inverse-image-test interval.
3. lem-trf-affine-relative-tor-amplitude-criterion converts this interval to the
   R-module Tor interval. Testing with R and using the flat-single calculation
   lem-fd-ringed-flat-single-tensor-cohomology gives the same cohomology bounds.
4. Finite algebra generators of A in both factors generate B over R. Thus B is
   Noetherian by lem-weil-pbc-finite-type-algebra-noetherian. Multiplication B to A
   is surjective and 1 generates A over B. Apply
   lem-weil-pbc-finite-free-resolution-noetherian to get its infinite finite-free
   resolution, placed in nonpositive degrees. It makes A[0] pseudo-coherent.
5. lem-weil-pbc-flat-module-base-change makes B flat through p₁. The flat-single
   theorem lem-fd-ringed-flat-single-tensor-cohomology says B[0] is K-flat and
   computes tensor by termwise scalar extension. It gives the natural cohomology
   comparisons. Naturality under multiplication by each element of B gives their
   B-linearity. Tensoring the zero cohomology modules gives vanishing below a. -/
theorem affine_relative_tor_diagonal_finiteness
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [Module.Flat R A] [Algebra.FinitePresentation R A]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wR} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wB} (ModuleCat.{u} (A ⊗[R] A))]
    [HasDerivedCategory.{wU}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ T : (Spec (.of A)).Opens, HasDerivedCategory.{wU}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over T))]
    (E : schemeDerivedCategory (Spec (.of A)))
    (hE : Scheme.IsPseudoCoherent (Spec (.of A)) E)
    (hlocal : ∃ K : CochainComplex
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ,
      Nonempty (DerivedCategory.Q.obj K ≅ E) ∧
      ∀ x : Spec (.of A), ∃ T : (Spec (.of A)).Opens, x ∈ T ∧
        ∃ a b : ℤ, a ≤ b ∧
          ∀ (G : SheafOfModules.{u} (moduleRings (Spec (.of R)).toRingedSpace)) (i : ℤ),
            i < a ∨ b < i → CochainComplex.sheafDerivedTensorVanishes
              ((TopCat.Sheaf.inverseImageRing
                (Spec.map (CommRingCat.ofHom (algebraMap R A))).base
                  (Spec (.of R)).sheaf).over T)
              (((SheafOfModules.overFunctor _ T).mapHomologicalComplex (.up ℤ)).obj
                (((affineTorScalarRestriction (algebraMap R A)).mapHomologicalComplex
                  (.up ℤ)).obj K))
              ((TopCat.Sheaf.inverseImageModule
                (Spec.map (CommRingCat.ofHom (algebraMap R A))).base
                  (Spec (.of R)).sheaf G).over T) i) :
    schemeDerivedQCohProperty (Spec (.of A)) E ∧
    ∃ C : CochainComplex (ModuleCat.{u} A) ℤ,
      Nonempty (DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          _ _ _ _ (tilde.functor (.of A)) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj C) ≅ E) ∧
      ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.IsPseudoCoherent (DerivedCategory.Q.obj C) ∧
        DerivedCategory.torAmplitudeIn (ModuleCat.{u} R) a b
          (DerivedCategory.Q.obj
            (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
              (.up ℤ)).obj C)) ∧
        (∀ i : ℤ, i < a ∨ b < i → IsZero (C.homology i)) ∧
        IsNoetherianRing (A ⊗[R] A) ∧
        (∃ (n : ℕ → ℕ)
          (ε : (Fin (n 0) → A ⊗[R] A) →ₗ[A ⊗[R] A]
            ((ModuleCat.restrictScalars (Algebra.TensorProduct.lmul' R).toRingHom).obj
              (ModuleCat.of A A)))
          (d : ∀ j : ℕ, (Fin (n (j + 1)) → A ⊗[R] A) →ₗ[A ⊗[R] A]
            (Fin (n j) → A ⊗[R] A)),
          Function.Surjective ε ∧ LinearMap.ker ε = LinearMap.range (d 0) ∧
            ∀ j : ℕ, LinearMap.ker (d j) = LinearMap.range (d (j + 1))) ∧
        DerivedCategory.IsPseudoCoherent
          ((DerivedCategory.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj
            ((ModuleCat.restrictScalars (Algebra.TensorProduct.lmul' R).toRingHom).obj
              (ModuleCat.of A A))) ∧
        ∃ hflat : (algebraMap A (A ⊗[R] A)).Flat,
          (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat
            ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj
              ((ModuleCat.restrictScalars (algebraMap A (A ⊗[R] A))).obj
                (ModuleCat.of (A ⊗[R] A) (A ⊗[R] A)))) ∧
          Nonempty (DerivedCategory.Q ⋙ affineDiagonalPullback hflat ≅
            (ModuleCat.extendScalars (algebraMap A (A ⊗[R] A))).mapHomologicalComplex
              (.up ℤ) ⋙ DerivedCategory.Q) ∧
          Nonempty (affineDiagonalPullback hflat ⋙
            (ModuleCat.restrictScalars (algebraMap A (A ⊗[R] A))).mapDerivedCategory ≅
            tensorRight ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
              ((ModuleCat.restrictScalars (algebraMap A (A ⊗[R] A))).obj
                (ModuleCat.of (A ⊗[R] A) (A ⊗[R] A))))) ∧
          (∀ i : ℤ, Nonempty (affineDiagonalPullback hflat ⋙
              DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] A)) i ≅
            DerivedCategory.homologyFunctor (ModuleCat.{u} A) i ⋙
              ModuleCat.extendScalars (algebraMap A (A ⊗[R] A)))) ∧
          ∀ i : ℤ, i < a → IsZero
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] A)) i).obj
              ((affineDiagonalPullback hflat).obj (DerivedCategory.Q.obj C))) := by
  sorry

end AlgebraicGeometry
