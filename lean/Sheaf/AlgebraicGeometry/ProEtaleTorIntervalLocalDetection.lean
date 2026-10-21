/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q87
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.CategoryTheory.Sites.GeometricInverseImageExact
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import Mathlib.CategoryTheory.Sites.LocalProperties
import Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection

/-! # Detection of a fixed Tor interval on the pro-etale site

Source: Weil conjectures blueprint, main-20261015, sec-proetale-coefficients,
sk-def-localizing-closure, ctf-equals-bc proof, Locality and Strata;
Stacks Project, Tags 04JC, 015F, 010N, 07A4, 03CE, 04TQ and 09AH
(blueprint: lem-sfb-tor-interval-local-detection).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Tor amplitude in one fixed interval is detected by a pro-etale covering family,
and by restriction to a closed subscheme and its complementary quasi-compact open.
Coefficients are an arbitrary commutative ring sheaf, and complexes are unbounded.
The interval condition is expanded as the test on every module in degree zero.
The coefficient on each source is the actual inverse-image ring; the structural
identification is its identity, so the displayed derived pullback is inverse image.

Source: blueprint main-20261015, ctf-equals-bc proof, Locality and Strata;
Stacks Project, Tags 04JC, 015F, 010N, 07A4, 03CE, 04TQ and 09AH
(blueprint: lem-sfb-tor-interval-local-detection).

Proof:
1. For any f, use the coefficient f⁻¹ A and its identity structural map.
   By lem-trf-geometric-inverse-image-exact the module inverse image is exact.
   Lemmas lem-weil-pbc-exact-functor-derived-factorization and
   lem-weil-pbc-exact-functor-derived-functor identify its termwise descent with
   derived pullback on all unbounded complexes. By
   lem-weil-pbc-exact-functor-complex-cohomology, H^q(f⁻¹ E) = f⁻¹ H^q(E),
   and a degree-zero module stays in degree zero.
2. Lemma lem-weil-pbc-ringed-topoi-derived-tensor-pullback gives the canonical
   isomorphism f⁻¹(K ⊗ᴸ M[0]) ≅ f⁻¹K ⊗ᴸ (f⁻¹M)[0]. Its coefficient map is
   the identity; there is no change to a different coefficient ring.
3. For a cover, fix M and q outside [c,d], and put F = H^q(K ⊗ᴸ M[0]).
   Steps 1 and 2 and each local Tor bound make the inverse image of F zero on
   every cover member. The abelian clause of
   lem-sfb-proetale-object-inverse-image-restriction identifies this with slice
   restriction. Base change of the cover supplies the CoversTop hypothesis of
   lem-sfb-sheaf-cover-local-isomorphism, applied to F → 0. Thus F is zero,
   also as a module sheaf. Vary M and q to obtain the first assertion.
4. For the closed/open pair, apply steps 1 and 2 to both immersions. Testing
   their Tor bounds on i⁻¹M and j⁻¹M makes i⁻¹F and j⁻¹F zero. Apply
   lem-exc-open-closed-detection with the inverse-image coefficient rings and
   identity identifications. This gives F = 0. Vary M and q to obtain the
   second assertion, with the same interval and no quasi-coherence assumption. -/
theorem proEtale_torInterval_local_detection
    (X : Scheme.{u}) (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (K : DerivedCategory (proEtaleRingModules X A)) (c d : ℤ) (_hcd : c ≤ d) :
    (∀ (𝒱 : X.Cover.{u + 1} (Scheme.precoverage @WeaklyEtale))
      (_ : QuasiCompactCover 𝒱.toPreZeroHypercover),
      (∀ t : 𝒱.I₀,
        ∀ (M : proEtaleRingModules (𝒱.X t)
            ((proEtaleSheafInverseImage (𝒱.f t) CommRingCat.{u + 1}).obj A))
          (q : ℤ), q < c ∨ d < q →
          IsZero ((DerivedCategory.homologyFunctor _ q).obj
            ((SheafOfModules.siteDerivedTensorIndependentCoefficients (ProEt.topology (𝒱.X t))
              ((proEtaleSheafInverseImage (𝒱.f t) CommRingCat.{u + 1}).obj A)).obj
              (((proEtaleRingDerivedPullback (𝒱.f t) A _ (Iso.refl _)).obj K),
                (DerivedCategory.singleFunctor _ 0).obj M)))) →
      ∀ (M : proEtaleRingModules X A) (q : ℤ), q < c ∨ d < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((SheafOfModules.siteDerivedTensorIndependentCoefficients (ProEt.topology X) A).obj
            (K, (DerivedCategory.singleFunctor _ 0).obj M)))) ∧
    (∀ (Z U : Scheme.{u}) (i : Z ⟶ X) (j : U ⟶ X)
      (_ : IsClosedImmersion i) (_ : IsOpenImmersion j) (_ : QuasiCompact j),
      Set.range j = (Set.range i)ᶜ →
      (∀ (M : proEtaleRingModules Z
          ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj A))
        (q : ℤ), q < c ∨ d < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((SheafOfModules.siteDerivedTensorIndependentCoefficients (ProEt.topology Z)
            ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj A)).obj
            (((proEtaleRingDerivedPullback i A _ (Iso.refl _)).obj K),
              (DerivedCategory.singleFunctor _ 0).obj M)))) →
      (∀ (M : proEtaleRingModules U
          ((proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj A))
        (q : ℤ), q < c ∨ d < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((SheafOfModules.siteDerivedTensorIndependentCoefficients (ProEt.topology U)
            ((proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj A)).obj
            (((proEtaleRingDerivedPullback j A _ (Iso.refl _)).obj K),
              (DerivedCategory.singleFunctor _ 0).obj M)))) →
      ∀ (M : proEtaleRingModules X A) (q : ℤ), q < c ∨ d < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((SheafOfModules.siteDerivedTensorIndependentCoefficients (ProEt.topology X) A).obj
            (K, (DerivedCategory.singleFunctor _ 0).obj M)))) := by
  sorry

end AlgebraicGeometry.Scheme
