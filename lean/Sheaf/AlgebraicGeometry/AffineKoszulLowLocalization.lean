/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral
import WeilConjectures.AlgebraicGeometry.DerivedOpenUnitCone
import WeilConjectures.AlgebraicGeometry.KoszulRestrictionZero
import WeilConjectures.AlgebraicGeometry.KoszulCoordinateMulTriangle
import WeilConjectures.AlgebraicGeometry.KoszulSupportedAugmentationVanishing
import WeilConjectures.AlgebraicGeometry.AffinePerfectOpenRepresentCohomology
import WeilConjectures.AlgebraicGeometry.DerivedStructureSheafHomHypercohomology
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.AffineDerivedTildeHomologyComparison
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-! # Low-degree localization detected by an affine Koszul complex

Source: Stacks Project, perfect.tex, Tag 0GEK, lemma-orthogonal-koszul-second-variant,
implication (2) to (1), with the reviewed cone-shift endpoint correction.
(blueprint: lem-sfb-affine-koszul-low-localization).
-/

@[expose] public section

set_option autoImplicit false

universe u wY wW

open CategoryTheory

namespace AlgebraicGeometry

/-- Vanishing against the sheafified Koszul complex in degrees at most `a` makes
truncation at `a - 1` of the canonical derived open-restriction unit invertible.
Source: Stacks Project, perfect.tex, Tag 0GEK, lemma-orthogonal-koszul-second-variant,
implication (2) to (1), with the reviewed correction of its cone shift.
(blueprint: lem-sfb-affine-koszul-low-localization).

Proof:
1. Each principal open is a quasi-compact spectrum of a localization; hence their
   finite union W is quasi-compact, including for r = 0. Complete the canonical unit
   E → B = Rj_*j^*E to a distinguished triangle E → B → N → E[1]. By
   lem-pc-derived-open-unit-cone, N has quasi-coherent cohomology and restricts to zero.
2. The Koszul complex restricts to zero (lem-pc-koszul-restriction-zero). Derived
   adjunction makes all its shifted Hom groups into B zero. For n ≤ a - 1,
   Hom(C_f[-n], E[1]) = Hom(C_f[-(n+1)], E) = 0. Representable exactness on the
   rotated triangle therefore gives Hom(C_f[-n], N) = 0. The n+1 explains the endpoint.
3. Induct on the sum of the positive exponents minus one. The coordinate multiplication
   triangle (lem-pc-koszul-coordinate-mul-triangle) and contravariant Hom exactness
   propagate this vanishing to every positive-power Koszul tuple at the same n.
4. For a map O_Y[-n] → N, lem-pc-koszul-supported-augmentation-vanishing supplies an
   index e annihilating its composite with the tail augmentation. The augmentation
   triangle of lem-sc-affine-perfect-open-represent-cohomology factors it through the
   Koszul object with exponents e+1; Step 3 makes the factor zero.
5. By lem-pc-derived-structure-sheaf-hom-hypercohomology the resulting Hom vanishing is
   H^n(RΓN) = 0. Apply lem-pc-affine-qcoh-derived-equivalence and
   new-affine-derived-tilde-homology-comparison to obtain H^n(N) = 0 for n ≤ a - 1.
6. The cohomology long exact sequence (lem-weil-heart-short-exact-triangles, clause 5)
   gives invertibility of H^n(E → B) in these degrees, since both H^{n-1}(N) and
   H^n(N) vanish. Standard truncation therefore makes this map a cohomology isomorphism.
7. Represent the truncated morphism by a right-fraction roof in the homotopy category,
   using lem-pc-quasi-isomorphisms-multiplicative-system and
   lem-pc-right-fraction-representation. Both roof arrows are quasi-isomorphisms, so
   both are inverted in the derived category. Thus the truncated unit is invertible.

The unit used here is obtained by deriving the actual open restriction/direct-image
adjunction, transported along Scheme.Modules.overFunctorEquiv. Its right adjoint is
schemeDerivedDirectImage W.ι, and its left adjoint is exact restriction to W. There is
no arbitrary map or choice of an adjunction. The Koszul terms use the recorded
ExteriorAlgebra.koszulComplex, extended with K_q in degree -q and sheafified by tilde.
No nonemptiness, regular-sequence or boundedness hypothesis is imposed. -/
theorem affine_koszul_low_localization
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (W : (Spec (.of A)).Opens)
    (hW : W = ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))
    [HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{wW}
      (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    (E : schemeDerivedCategory (Spec (.of A)))
    (hE : schemeDerivedQCohProperty (Spec (.of A)) E) (a : ℤ)
    (hvan : ∀ n : ℤ, n ≤ a → Subsingleton
      (((DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          _ _ _ _ (tilde.functor (.of A))
          ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
          ((ExteriorAlgebra.koszulComplex A r f).extend
            ComplexShape.embeddingDownNat)))⟦-n⟧) ⟶ E)) :
    IsIso ((DerivedCategory.TStructure.t.truncLE (a - 1)).map
      (((@id ((schemeOpenRestriction (Spec (.of A)) W) ⊣
        RingedSpace.moduleDirectImage W.ι.toLRSHom.toShHom)
          ((Scheme.Modules.restrictAdjunction W.ι).ofNatIsoLeft
            (Scheme.Modules.overFunctorEquiv W).symm)).mapDerivedCategoryRightDerivedAdjunction
              ).unit.app E)) := by
  sorry

end AlgebraicGeometry
