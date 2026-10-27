/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.DerivedOpenUnitCone
import WeilConjectures.AlgebraicGeometry.DerivedStructureSheafHomHypercohomology
import WeilConjectures.AlgebraicGeometry.KoszulCoordinateMulTriangle
import WeilConjectures.AlgebraicGeometry.KoszulRestrictionZero
import WeilConjectures.AlgebraicGeometry.KoszulSupportedAugmentationVanishing
import WeilConjectures.AlgebraicGeometry.AffinePerfectOpenRepresentCohomology
import WeilConjectures.AlgebraicGeometry.AffineDerivedTildeHomologyComparison
import Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Koszul orthogonality and upper localization on an affine scheme

Source: Stacks Project, Derived Categories of Schemes, Tag 0GEJ,
`lemma-orthogonal-koszul-first-variant`, implication (2) to (1).
(blueprint: lem-sfb-affine-koszul-upper-localization).
-/

@[expose] public section

universe u wY wU

open CategoryTheory CategoryTheory.Limits

set_option autoImplicit false
set_option synthInstance.maxSize 2048

namespace AlgebraicGeometry

/-- Vanishing of Hom from negative shifts of the sheafified Koszul complex in degrees
at least `a` makes the upper truncation of the canonical open-restriction unit invertible.
The unit is obtained by deriving the actual restriction/pushforward adjunction, after
transporting restriction through `Scheme.Modules.overFunctorEquiv`.
Source: Stacks Project, Tag 0GEJ, `lemma-orthogonal-koszul-first-variant`, (2) implies (1).
(blueprint: lem-sfb-affine-koszul-upper-localization).

Proof:
1. The finite union `U` of principal opens is quasi-compact, by
   `lem-weil-pbc-spec-localization-away-basic-open` and
   `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`. Complete the canonical unit
   `E → B = Rj_*(E|_U)` to a triangle `N → E → B → N[1]`.
   `lem-pc-derived-open-unit-cone` gives quasi-coherent cohomology and zero restriction
   for `N`; shifts preserve these properties.
2. `lem-pc-koszul-restriction-zero` and derived adjunction
   (`lem-pc-ringed-spaces-derived-adjoint-general`) kill all Hom from shifted Koszul
   objects to `B` and `B[-1]`. Hom-into-triangle exactness
   (`lem-weil-pbc-hom-into-triangle-exact`) transfers the stated vanishing to `N`.
3. Induct on the sum of the positive coordinate exponents minus one.
   `lem-pc-koszul-coordinate-mul-triangle`, followed by
   `lem-weil-pbc-hom-out-of-triangle-exact`, transfers the same vanishing range to the
   Koszul complex on every positive-power tuple; the threshold `a` does not change.
4. For a map `O_Y[-n] → N`, `lem-pc-koszul-supported-augmentation-vanishing` kills its
   composite with some tail augmentation. The augmentation triangle of
   `lem-sc-affine-perfect-open-represent-cohomology` and Hom-out-of-triangle exactness
   factor that map through the corresponding power Koszul object. Step 3 kills it.
5. `lem-pc-derived-structure-sheaf-hom-hypercohomology` identifies this Hom vanishing
   with `H^n(RΓ(Y,N)) = 0`. The counit of `lem-pc-affine-qcoh-derived-equivalence` and
   `new-affine-derived-tilde-homology-comparison` give `H^n(N) = 0` for every `n ≥ a`.
6. The cohomology exact sequence (`lem-weil-heart-short-exact-triangles`) of the
   triangle in Step 1 shows that the unit induces isomorphisms in every degree `n ≥ a`.
   Standard truncation retains these groups and kills all degrees below `a`.
7. A derived morphism inducing isomorphisms in every degree is invertible: represent
   it by a roof using `lem-pc-right-fraction-representation` and
   `lem-pc-quasi-isomorphisms-multiplicative-system`; both legs are quasi-isomorphisms.
   Apply this to the truncated canonical unit.
The empty tuple gives `U = ∅` and the structure sheaf in degree zero. No nonzero-ring,
regularity, nonzero-generator, or boundedness assumption is used. -/
theorem affine_koszul_upper_localization
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (U : (Spec (.of A)).Opens)
    (hU : U = ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))
    [HasDerivedCategory.{wU}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (E : schemeDerivedQCohCategory (Spec (.of A))) (a : ℤ)
    (hvan : ∀ n : ℤ, a ≤ n → Subsingleton
      ((DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          _ _ _ _ (tilde.functor (.of A))
          ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
          ((ExteriorAlgebra.koszulComplex A r f).extend
            ComplexShape.embeddingDownNat)))⟦-n⟧ ⟶ E.obj)) :
    IsIso ((DerivedCategory.TStructure.t.truncGE a).map
      ((Adjunction.mapDerivedCategoryRightDerivedAdjunction
        (C := SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (L := schemeOpenRestriction (Spec (.of A)) U)
        (R := RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom)
        ((Scheme.Modules.restrictAdjunction U.ι).ofNatIsoLeft
          (Scheme.Modules.overFunctorEquiv U).symm)).unit.app E.obj)) := by
  sorry

end AlgebraicGeometry
