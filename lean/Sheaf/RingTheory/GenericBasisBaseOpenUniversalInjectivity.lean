/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q95
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.LinearAlgebra.TensorProduct.Map
import WeilConjectures.RingTheory.Flat.LocalizationPreservesFlatness
import Mathlib.RingTheory.Flat.Localization

/-!
# A generic fibre basis becomes universally injective on a base open

Source: Stacks Project, More on Flatness, Tag 05IA, lemma-induction-step-fp,
implication (1) to the universal-injectivity assertion of (2), with q = p and M flat
over R (blueprint: lem-trf-generic-basis-base-open-universal-injectivity).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace AlgebraicGeometry

/-- A prescribed generic-fibre basis map becomes universally injective after inverting
one base element outside the specified prime. The geometric-integrality hypothesis
says exactly that every fibre remains a nonzero domain after every residue-field
extension. Localization uses the base action: a denominator f^n acts on a B-module
as the image of f^n in B, so these are the same fractions as localization in B.
The localized finite free source is canonically B_f to the power a.

Source: Stacks Project, More on Flatness, Tag 05IA, lemma-induction-step-fp,
implication (1) to the universal-injectivity assertion of (2), with q = p
(blueprint: lem-trf-generic-basis-base-open-universal-injectivity).

Proof plan:
1. Localize the R-flat B-module M at B minus p. By
   lem-pc-affine-flat-module-localization-preserves-flatness, M_p is R-flat.
   Since p contracts to r, every element outside r acts invertibly on M_p.
   The canonical fraction action therefore makes it an R_r-module.
   By lem-weil-pbc-flat-over-localization (Tag 00HT), it is R_r-flat.
2. Apply lem-sfb-local-flat-generic-basis-universal-injectivity, with its base
   prime p renamed r, its algebra prime q renamed p = rB, E = M and rank a.
   Flat finite presentation, geometrically integral fibres, primeness and
   contraction, finite presentation of M and the specified residue-field
   isomorphism are precisely the hypotheses here. Step 1 gives its remaining
   local flatness hypothesis. It supplies f outside r and injectivity after
   tensoring the localized map with every R_f-module L. Both localizations
   invert the image of this same f, so this is exactly the asserted map.
-/
theorem exists_genericBasis_baseOpen_universalInjectivity
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [Module.Flat R B] [Algebra.FinitePresentation R B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap R B)))]
    (M : Type v) [AddCommGroup M] [Module B M] [Module R M] [IsScalarTower R B M]
    [Module.FinitePresentation B M] [Module.Flat R M]
    (r : Ideal R) [r.IsPrime] (p : Ideal B) [p.IsPrime]
    (hp : p = Ideal.map (algebraMap R B) r)
    (hcontract : Ideal.comap (algebraMap R B) p = r)
    (a : ℕ) (α : (Fin a → B) →ₗ[B] M)
    (hα : Function.Bijective (α.baseChange p.ResidueField)) :
    ∃ f : R, f ∉ r ∧
      ∀ (L : Type (max u v w)) [AddCommGroup L] [Module (Localization.Away f) L],
        Function.Injective
          ((LocalizedModule.map (Submonoid.powers f) (α.restrictScalars R)).lTensor L) := by
  sorry

end AlgebraicGeometry
