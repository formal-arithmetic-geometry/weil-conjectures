/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q117
-/
module

public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension
import WeilConjectures.RingTheory.ClosedPointDimensionLocalRing
import WeilConjectures.Mathlib.RingTheory.Nullstellensatz
import WeilConjectures.RingTheory.RegularLocalDimOneIffNormal
import Sheaf.AlgebraicGeometry.IsRegularScheme
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.RingTheory.KrullDimension.Zero

/-!
# Coherent normalization quotient and its exact singular support

Source: Stacks Project, Varieties, Tag 0C1R, parts (1)--(3) and the singular-support
argument; Tag 0B8X for the smooth locus over a perfect field.
(blueprint: lem-trf-curve-normalization-coherent-support).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The direct image of the structure module of the componentwise normalization.
Source: Stacks Project, Varieties, Tag 0C1R(2).
(blueprint: lem-trf-curve-normalization-coherent-support). -/
abbrev normalizationCoherentPushforward (X : Scheme.{u}) : X.Modules :=
  (Modules.pushforward X.fromReducedNormalization).obj
    (SheafOfModules.unit X.reducedNormalization.ringCatSheaf)

/-- The structural inclusion into the normalization direct image, before proving injectivity.
Source: Stacks Project, Varieties, Tag 0C1R(2).
(blueprint: lem-trf-curve-normalization-coherent-support). -/
abbrev normalizationCoherentMap (X : Scheme.{u}) :
    SheafOfModules.unit X.ringCatSheaf ⟶ normalizationCoherentPushforward X :=
  SheafOfModules.unitToPushforwardObjUnit X.fromReducedNormalization.toRingCatSheafHom

/-- The actual sheaf cokernel of the canonical normalization map.
Source: Stacks Project, Varieties, Tag 0C1R(2).
(blueprint: lem-trf-curve-normalization-coherent-support). -/
abbrev normalizationCoherentQuotient (X : Scheme.{u}) : X.Modules :=
  cokernel (normalizationCoherentMap X)

/-- The locus where the local ring is an integrally closed domain.
Source: Stacks Project, Varieties, Tags 0C1R and 0B8X; Algebra, Tag 030C.
(blueprint: lem-trf-curve-normalization-coherent-support). -/
def normalizationNormalLocus (X : Scheme.{u}) : Set X :=
  {x | IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)}

/-- The module quotient C_x/A_x, with the canonical stalk map defining the image of A_x.
The stalk of the structure module is the underlying module of the local ring A_x.
Source: Stacks Project, Varieties, Tag 0C1R(3)--(4); Modules, Tag 01AG.
(blueprint: lem-trf-curve-normalization-coherent-support). -/
abbrev normalizationCoherentStalkQuotient (X : Scheme.{u}) (x : X) : Type u :=
  ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
    (normalizationCoherentPushforward X)) ⧸
      LinearMap.range ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map
        (normalizationCoherentMap X)).hom

/-- The normalization quotient is coherent and supported exactly at the nonsmooth points.
Its stalk identification is specified on every representative by the stalk of the cokernel
projection, hence is the canonical quotient identification rather than an arbitrary isomorphism.

Source: Stacks Project, Varieties, Tag 0C1R(1)--(3) and its support argument; Tag 0B8X.
(blueprint: lem-trf-curve-normalization-coherent-support).

Proof:
1. Apply lem-trf-normalization-affine-stalk-closure: X and its normalization are Noetherian,
   the normalization is finite, and its affine and stalk maps are inclusions into finite
   integral closures. The affine injections imply sheaf injectivity by the sheaf axiom.
   Take Q to be the actual cokernel of the structural map.
2. The structure modules on the two Noetherian schemes are quasi-coherent of finite type,
   hence coherent by pqf-lem-coherent-ft-locnoeth. Finite direct image is coherent by
   lem-weil-pbc-finite-pushforward-coherent. Apply
   lem-weil-pbc-coherent-kernel-cokernel-locnoeth to Q and lem-weil-pbc-module-stalk-exact
   to the sequence. The induced quotient identification sends the class of b to q_x(b).
   The finite generators of the normalization stalk generate its quotient.
3. If A_x is a normal domain, its integral closure in its fraction field is itself.
   Conversely, zero quotient identifies A_x with its integral closure in its total fractions,
   a finite product of fields (lem-trf-normalization-affine-stalk-closure). Coordinate
   idempotents are integral. In a nonzero local ring an idempotent is zero or one, so this
   product has only one factor. Thus A_x is an integrally closed domain.
4. Every irreducible closed chain lies in a component, so pure dimension one bounds its
   length by one. Sobriety (lem-sc-scheme-sober) implies every point is generic or closed.
   At a closed point apply lem-sbc-equidimensional-open-local-dimension and
   lem-weil-pbc-closed-point-dimension-local-ring to get local-ring dimension one.
   The affine-stalk description gives a reduced Noetherian localization of a finite-type
   k-algebra, hence essentially finite type. The residue map is an isomorphism by
   lem-wf-affine-nullstellensatz-vanishing(1).
5. Generic local rings are fields by lem-weil-pbc-minimal-prime-reduced-localization-field.
   The other normal points are regular by lem-weil-pbc-regular-local-dim-one-iff-normal.
   The normal open is locally Noetherian (pqf-def-locnoeth), hence a regular scheme
   (def-weil-regular-scheme). The algebraically closed field is perfect, so
   lem-trf-regular-perfect-field-smooth makes this open smooth. Conversely smooth local
   rings are regular (lem-weil-pbc-smooth-scheme-over-field-regular), hence normal by
   rem-pc-regular-normal. This proves equality with the smooth locus.
6. The support is the closed complement of the dense normal open and misses component
   generic points. A positive-length chain in this complement would extend to a chain of
   length two in X. It therefore has dimension at most zero. Use
   lem-weil-pbc-noetherian-scheme-closed-subsets-minimal and lem-sc-scheme-sober to obtain
   the Noetherian T0 space, and lem-sc-zero-dim-noetherian-closed-finite to conclude that
   the support is finite and consists of closed points. On the empty scheme all module
   sheaves vanish, giving zero Q and empty support.
-/
theorem curve_normalization_coherent_support
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [IsReduced X]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (hpure : ∀ Z : Set X, Z ∈ irreducibleComponents X → topologicalKrullDim Z = 1) :
    (ShortComplex.mk (normalizationCoherentMap X)
      (cokernel.π (normalizationCoherentMap X))
      (cokernel.condition (normalizationCoherentMap X))).ShortExact ∧
    RingedSpace.IsCoherent X.toRingedSpace (SheafOfModules.unit X.ringCatSheaf) ∧
    RingedSpace.IsCoherent X.toRingedSpace (normalizationCoherentPushforward X) ∧
    RingedSpace.IsCoherent X.toRingedSpace (normalizationCoherentQuotient X) ∧
    (∀ x : X,
      (∃ e : normalizationCoherentStalkQuotient X x ≃ₗ[X.presheaf.stalk x]
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
            (normalizationCoherentQuotient X)),
        ∀ b : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
            (normalizationCoherentPushforward X),
          e (Submodule.Quotient.mk b) =
            ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map
              (cokernel.π (normalizationCoherentMap X))) b) ∧
      Module.Finite (X.presheaf.stalk x)
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
          (normalizationCoherentQuotient X)) ∧
      (Subsingleton ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
        (normalizationCoherentQuotient X)) ↔ x ∈ normalizationNormalLocus X)) ∧
    IsOpen (normalizationNormalLocus X) ∧ Dense (normalizationNormalLocus X) ∧
    (∀ x : X, x ∈ normalizationNormalLocus X ↔
      ∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ (X ↘ Spec (.of k)))) ∧
    {x : X | ¬ Subsingleton ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
      (normalizationCoherentQuotient X))} = (normalizationNormalLocus X)ᶜ ∧
    ((normalizationNormalLocus X)ᶜ).Finite ∧
    (∀ x : X, x ∉ normalizationNormalLocus X → IsClosed ({x} : Set X)) ∧
    (∀ (Z : Set X), Z ∈ irreducibleComponents X →
      ∀ x : X, IsGenericPoint x Z → x ∈ normalizationNormalLocus X) ∧
    (∀ x : X, IsClosed ({x} : Set X) →
      _root_.IsReduced (X.presheaf.stalk x) ∧ IsNoetherianRing (X.presheaf.stalk x) ∧
      ringKrullDim (X.presheaf.stalk x) = 1 ∧
      ((X.presheaf.germ ⊤ x (TopologicalSpace.Opens.mem_top x)).hom.comp
        (((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop).hom)).EssFiniteType ∧
      ∃ e : X.residueField x ≅ CommRingCat.of k,
        Spec.map e.inv = X.fromSpecResidueField x ≫ (X ↘ Spec (.of k))) ∧
    (IsEmpty X → IsZero (normalizationCoherentQuotient X) ∧
      {x : X | ¬ Subsingleton ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
        (normalizationCoherentQuotient X))} = ∅) := by
  sorry

end AlgebraicGeometry.Scheme
