module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Limits.MorphismProperty
import WeilConjectures.AlgebraicGeometry.FlatFibreDimensionStrataCover
import WeilConjectures.AlgebraicGeometry.Modules.Differentials
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.SmoothRelativeDifferentialsFiniteLocallyFree
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.Morphisms.LocallyPrincipalSupportDimensionOne
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres

/-! # Birational open immersions between smooth trait models

Source: Bosch--Lutkebohmert--Raynaud, Neron Models, section 5.1, Theorem 5,
proof of the no-shrinking assertion, printed page 114 (PDF page 120).
(blueprint: lem-sfb-smooth-trait-birational-immersion)

The fraction field is the canonical `FractionRing R`. Density is stated on
scheme-theoretic fibres, and the generic-fibre map is the existing base-change
functor applied to the given morphism over `Spec R`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A fibrewise dense open containing the generic fibre contains all points of local-ring
Krull dimension at most one. A generically invertible morphism of smooth separated
finite-type trait models that is an open immersion on this open is an open immersion.

Source: BLR, Neron Models, section 5.1, Theorem 5, proof of the no-shrinking assertion,
printed page 114 (PDF page 120).
(blueprint: lem-sfb-smooth-trait-birational-immersion)

Proof plan from the accepted DAG split:
1. Choose a uniformizer pi. A DVR is Noetherian and has precisely its generic and
   closed points (def-sc-discrete-valuation-ring, lem-sc-dvr-dimension-one).
   The finite-type source is Noetherian (lem-weil-pbc-finite-type-over-noetherian).
   Smoothness implies flatness and local finite presentation (lem-pc-smooth-flat),
   hence openness (lem-weil-pbc-flat-lfp-open). Thus the generic fibre is dense:
   every nonempty open has nonempty open image in the trait, containing its generic point.
2. A point over the generic point belongs to U. At a special-fibre point with
   local-ring dimension at most one, the flat height formula
   (lem-weil-pbc-flat-height-formula) gives dim A = 1 + dim(A/pi A), so the fibre
   local ring has dimension zero. The point is therefore a component generic point
   of the special fibre. Its dense open U contains it by
   lem-sbc-flat-fibre-dimension-strata-cover. This proves the first conclusion.
3. For the given morphism f consider the canonical map from the pullback of the target's
   relative differential sheaf to the source's relative differential sheaf
   (def-sc-relative-differential-sheaf, def-pc-module-pullback).
   Both are finite locally free (lem-ag-smooth-relative-differentials-finite-locally-free,
   def-sc-finite-locally-free-sheaf); on U the map is invertible.
   On any common trivializing neighbourhood the two ranks agree, since that neighbourhood
   meets the dense generic fibre contained in U. Hence the differential matrix is square.
4. On an affine trivializing neighbourhood its determinant h is a unit on U. If h
   were noninvertible at x, the first conclusion would force dim O_x > 1.
   The locally principal ideal (h) then has a dimension-one generalization of x in
   its support (lem-sbc-locally-principal-support-dimension-one, pqf-def-locnoeth).
   This generalization belongs to U by step 2, contradicting vanishing of h there.
   Thus the differential map is invertible everywhere. In rank zero its determinant is 1.
5. The relative cotangent criterion between smooth schemes
   (lem-sfb-smooth-morphism-cotangent-isomorphism-etale) makes f etale near every point;
   locality gives etaleness (lem-weil-pbc-etale-local-on-source), hence smoothness,
   flatness and local finite presentation (lem-weil-pbc-etale-smooth-zero-dimensional-fibres,
   lem-pc-smooth-flat).
6. Put P = X times_Z X. Its first projection is etale by base change
   (lem-weil-pbc-etale-base-change-finite-limits). The diagonal of f is closed,
   being a base change of the closed diagonal of X over the trait
   (lem-weil-pbc-closed-immersion-base-change). The projection is separated
   (lem-weil-pbc-separated-base-change). Its diagonal section is consequently an
   open and closed immersion (lem-weil-pbc-etale-section-clopen-immersion).
7. The generic fibre of P is dense: its etale projection to X is open
   (lem-weil-pbc-etale-morphism-open-map), and the generic fibre of X is dense.
   The diagonal contains that generic fibre because the generic-fibre map of f is
   invertible. Its clopen image is therefore all of P, so the diagonal is invertible.
   Thus f is a monomorphism. The flat, locally finitely presented monomorphism
   criterion (lem-pe-flat-lfp-monomorphism-open) now makes f an open immersion. -/
theorem smooth_trait_birational_immersion
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (X Z : Over (Spec (CommRingCat.of R)))
    [Smooth X.hom] [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [Smooth Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (U : X.left.Opens)
    (hgeneric : Set.range (pullback.fst X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))) ⊆ (U : Set X.left))
    (hdense : ∀ t : Spec (CommRingCat.of R),
      Dense ((X.hom.fiberι t) ⁻¹' (U : Set X.left))) :
    (∀ x : X.left, ringKrullDim (X.left.presheaf.stalk x) ≤ 1 → x ∈ U) ∧
      (∀ f : X ⟶ Z,
        IsIso ((Over.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))).map f).left →
        IsOpenImmersion (U.ι ≫ f.left) → IsOpenImmersion f.left) := by
  sorry

end AlgebraicGeometry
