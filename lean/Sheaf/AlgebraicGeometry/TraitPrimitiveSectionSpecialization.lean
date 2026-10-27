/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q146
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Filtration
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.AlgebraicGeometry.InvertibleModuleGenericStalk
import Sheaf.AlgebraicGeometry.TensorPullbackOpenRestriction

/-! # Primitive specialization of a generic line section over a trait

Source: Stacks Project, Algebra, Tag 031T (2), and Descent, Tag 036D;
the agent-extracted geometric section lemma uses the denominator/maximal-divisibility
argument from Algebra, Tags 00PD and 00IQ, and Schemes, Tag 01IA.
(blueprint: lem-sfb-trait-primitive-section-specialization)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A nonzero generic line section can be rescaled to an integral section with nonzero
special-fibre restriction, without properness or completeness.

Source: Stacks Project, Algebra, Tag 031T (2), and Descent, Tag 036D; the proof below
instead uses Algebra, Tags 00PD and 00IQ, Schemes, Tag 01IA, and Varieties, Tag 056S.
(blueprint: lem-sfb-trait-primitive-section-specialization)

Proof:
1. A DVR is Noetherian, and its fraction field is obtained by inverting the uniformizer
   (lem-weil-pbc-dvr-unit-times-uniformizer-power). The generic fibre is the principal
   open D(pi), by lem-weil-pbc-principal-localization-open-immersion,
   lem-weil-pbc-open-immersion-base-change and lem-weil-pbc-fibre-product-affine-spectra.
   Tensor pullback there is restriction
   (lem-weil-pbc-open-immersion-module-pullback-restriction). Finite presentation gives
   quasi-compactness of X.
2. The geometric-fibre hypothesis descends connectedness and nonemptiness to X_K:
   use lem-weil-pbc-field-extension-base-change-faithfully-flat and
   lem-weil-pbc-faithfully-flat-surjective-spectrum. Smoothness survives base change
   (lem-pc-proper-base-change), and lem-weil-pbc-smooth-scheme-over-field-regular and
   lem-sc-regular-connected-integral make X_K integral.
3. On each nonempty affine chart, smoothness gives flatness and finite presentation
   (lem-weil-pbc-smooth-restrict-open-subschemes,
   lem-weil-pbc-smooth-ring-map-iff-smooth-affine, lem-weil-pbc-smooth-ring-map-flat).
   By lem-trf-flat-module-torsionfree-domain its ring injects into its nonzero generic
   localization, a domain by step 2. Thus X is integral and locally Noetherian by
   lem-weil-pbc-finite-type-algebra-noetherian. Sections on nonempty opens inject into
   the generic stalk by lem-sc-invertible-module-generic-stalk.
4. Choose a finite affine trivializing cover. Clear denominators on each member by
   lem-weil-pbc-affine-module-basic-open-localization, choose one common exponent N,
   and glue using the generic-stalk injectivity from step 3. This gives a section t
   restricting to pi^N s_K, which is nonzero.
5. Choose x on the nonempty special fibre. Its local ring is Noetherian by
   lem-weil-pbc-affine-open-stalk-localization and lem-weil-pbc-localization-noetherian;
   C_x is finite free of rank one, pi lies in the maximal ideal, and t_x is nonzero by
   generic-stalk injectivity. By lem-weil-pbc-krull-intersection-jacobson some power
   pi^b C_x does not contain t_x.
6. The natural numbers j for which t is globally divisible by pi^j form a nonempty
   set bounded by b. Choose its largest member a and write t = pi^a s. On the generic
   fibre, cancellation gives s|_K = pi^(N-a) s_K.
7. If s restricted to the special fibre were zero, its coefficient on each affine
   trivialization would lie in pi A (lem-weil-pbc-fibre-product-affine-spectra and
   lem-weil-pbc-open-immersion-module-pullback-restriction). Divide these coefficients
   by pi. Flat torsion-freeness makes the resulting local sections agree, so they
   glue to v with s = pi v. This contradicts maximality of a. Take m = N-a in Z. -/
theorem exists_trait_primitive_section
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    (X : Scheme.{u}) (f : X ⟶ Spec (.of R))
    [Smooth f] [IsSeparated f] [QuasiCompact f] [GeometricallyConnected f]
    (C : X.Modules) [C.IsInvertible]
    (sK : Γ((tensorPullback
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj C, ⊤))
    (hsK : sK ≠ 0) :
    ∃ (m : ℤ) (s : Γ(C, ⊤)),
      ((tensorPullbackSectionAdjunction
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).unit.app C).app
          ⊤ s =
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).appTop
          ((Scheme.ΓSpecIso (.of K)).inv ((algebraMap R K π) ^ m)) • sK ∧
      ((tensorPullbackSectionAdjunction
        (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))).unit.app C).app
          ⊤ s ≠ 0 := by
  sorry

end AlgebraicGeometry.Scheme.Modules
