/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Sheaf.AlgebraicGeometry.IsRegularScheme
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Abelian.RightDerived
import Sheaf.AlgebraicGeometry.RegularEtaleDirectImageBaseChange
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import Sheaf.Paper.ConstantSheafSectionsLocallyConstant
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.RingTheory.GeometricIntegralityFiniteFieldTest

/-!
# Integral geometric fibres of a local regular morphism of strictly local schemes

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVII,
Lemma 4.3.2.3, printed pages 284--285
(blueprint: lem-per-strict-local-regular-integral-fibres).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A local regular morphism between Noetherian strictly local schemes has nonempty,
integral geometric fibres. Strictly local schemes are written as spectra of strictly
henselian local rings, and the morphism is the spectrum of a local ring homomorphism.
`IsIntegral` includes nonemptiness as well as reducedness and irreducibility.
Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVII,
Lemma 4.3.2.3, printed pages 284--285
(blueprint: lem-per-strict-local-regular-integral-fibres).

Proof:
1. Write X = Spec A and Y = Spec B. Choose a prime ell invertible in A, hence in B.
   For a point z of X and a finite extension L of its residue field, form W_L =
   Y x_X Spec L. The affine-morphism permanence theorem
   (lem-weil-pbc-affine-morphism-permanence) makes Spec L -> X qcqs, and
   lem-weil-pbc-fibre-product-affine-spectra identifies W_L with Spec(B tensor_A L).
2. Apply lem-per-regular-etale-direct-image-base-change to the constant F_ell sheaf
   on Spec L. By lem-pe-constant-left-module-inverse-image, pullback is exact and
   preserves constant modules. Taking degree zero using
   lem-weil-pbc-left-exact-injective-resolution-degree-zero and
   def-weil-pbc-direct-image, then using lem-weil-pbc-exchange-forget-coefficients,
   gives f^{-1} g_* F_ell isomorphic to p_* F_ell on Y.
3. The closed geometric point of Y maps to that of X because the ring map is local.
   Apply lem-weil-pbc-strictly-henselian-sections-stalk on X and Y, and
   lem-weil-pbc-inverse-image-stalk-germ. Evaluating direct images identifies
   Gamma(W_L,F_ell) with Gamma(Spec L,F_ell). The latter has ell elements by
   lem-weil-pbc-constant-sheaf-sections-locally-constant.
4. That same locally constant description shows W_L is nonempty and connected:
   the empty scheme has one section; a nontrivial clopen decomposition gives at
   least ell squared sections, contradicting the count ell in either case.
5. The finite-extension regularity assumption makes W_L locally Noetherian and
   regular (def-weil-regular-scheme and def-pc-scheme-fibre). Apply
   lem-sc-regular-connected-integral to conclude it is integral. Thus B tensor_A L
   is a domain by def-pc-integral-scheme.
6. Set S = B tensor_A kappa(z). The canonical balanced tensor isomorphism identifies
   S tensor_kappa(z) L with B tensor_A L. Apply
   lem-per-geometric-integrality-finite-field-test (Stacks 0FWF) to S to obtain
   a domain after any extension Omega of kappa(z). The affine fibre-product formula
   identifies its spectrum with the specified geometric fibre. Its integrality
   includes nonemptiness; no Noetherianity of the Omega-base-changed fibre is assumed.
-/
theorem isIntegral_geometricFiber_of_strictlyHenselian_local_regular
    (A B : Type u) [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsStrictlyHenselianLocalRing A] [IsStrictlyHenselianLocalRing B]
    (φ : A →+* B) [IsLocalHom φ] [Flat (Spec.map (CommRingCat.ofHom φ))]
    (hreg : ∀ (x : Spec (.of A)) (L : Type u) [Field L]
      [Algebra ((Spec (.of A)).residueField x) L]
      [Module.Finite ((Spec (.of A)).residueField x) L],
      IsRegularScheme
        (pullback ((Spec.map (CommRingCat.ofHom φ)).fiberToSpecResidueField x)
          (Spec.map (CommRingCat.ofHom
            (algebraMap ((Spec (.of A)).residueField x) L)))))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω) ⟶ Spec (.of A)) :
    IsIntegral (pullback (Spec.map (CommRingCat.ofHom φ)) z) := by
  sorry

end AlgebraicGeometry
