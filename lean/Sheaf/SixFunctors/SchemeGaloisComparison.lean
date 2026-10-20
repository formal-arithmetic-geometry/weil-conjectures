/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q160
-/
module

public import Sheaf.SixFunctors.SchemeFrobenius
public import Sheaf.AlgebraicGeometry.FrobeniusFactorization
public import WeilConjectures.AlgebraicGeometry.Morphisms.Frobenius
public import Sheaf.AlgebraicGeometry.AbsoluteFrobeniusSite
import Sheaf.AlgebraicGeometry.FrobeniusTrivializationPullback
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.Topology.Homeomorph.Defs
public import Sheaf.Paper.FiniteFieldFiber
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
import Sheaf.RingTheory.PowerGeneratedSpectrumHomeomorphism
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

/-!
# Comparison of scheme and Galois pullbacks

Source: the Weil conjectures blueprint, `prop-trf-scheme-galois-comparison`, order 2420
(blueprint: prop-trf-scheme-galois-comparison); the comparison of geometric and
arithmetic Frobenius uses Stacks Project, Tag 0CC8, and invariance of the pro-etale
site under universal homeomorphisms.
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.FiniteFieldDatum

/-- The scheme and geometric-Galois pullbacks are canonically compared on the
small pro-etale derived category, with the same comparison available at every
positive iterate.  The absolute Frobenius in the factorization is a universal
homeomorphism, including for nonreduced and empty schemes.

Source: blueprint `prop-trf-scheme-galois-comparison`, order 2420
(blueprint: prop-trf-scheme-galois-comparison).

Proof, following the eight steps in the DAG:
1. Use `absoluteFrobenius_factorization` and the inverse arithmetic/geometric
   Galois maps to obtain Phi^m = g^m H_m = H_m g^m. Characteristic p comes from
   the finite-field datum and its structure maps to section rings.
2. On affine charts H_m is x ↦ x^(p^(am)). Its kernel is nil, every target
   element has a p^(am)-power in the image, and p^(am) annihilates every element.
   Apply `universally_isHomeomorph_specMap_of_power_generated` (Stacks 0BRA),
   then glue over a target affine cover to prove the universal condition.
3. The constant-section coefficient comparisons preserve constants. The module
   inverse image is exact, so its termwise descent computes the unbounded
   derived pullback for this arbitrary finite A, without a special presentation.
4. Use the normalized module adjunction mates for the canonical composition
   comparison. Fibre-product projection uniqueness gives coherence; termwise
   descent and localization preserve it. K-flat resolutions identify this with
   the selected canonical derived comparison.
5. Relative Frobenius on each weakly etale object gives the site isomorphisms r.
   Their sectionwise inverse maps give the direct-image trivialization, and the
   normalized left-adjoint mate is tau. The canonical absolute-Frobenius-site
   theorem and its pullback-naturality extension give its addition law.
6. Define kappa_m by the displayed factorization transport, canonical composition
   comparison, and derived descent of tau_m, whiskered by G_m. For m=1 this is kappa.
7. Apply `absoluteFrobenius_proEtale_trivialization_pullback` to u=g^n and
   exponent am. Its naturality equation moves tau_m past the semilinear Galois
   pullback, using no assertion that g is a k-morphism.
8. The composition coherence from Step 4 and the addition law from Step 5 give
   kappa_(m+n) = G_m(kappa_n) composed with kappa_m at T_n. The two whiskerings
   express exactly that formula. All equations hold termwise on complexes;
   localization carries them to the unbounded derived category. -/
theorem schemeGaloisComparison
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, IsUnit (n : D.k) ∧ ∀ a : A, n • a = 0) :
    ∃ κ :
        AlgebraicGeometry.Scheme.proEtaleConstantRingDerivedPullback A
            (D.schemeFrobenius X₀) ≅
          AlgebraicGeometry.Scheme.proEtaleConstantRingDerivedPullback A
            (D.geometricGaloisFrobenius X₀),
      ∃ κiter : ∀ m : ℕ, 1 ≤ m →
          (AlgebraicGeometry.Scheme.proEtaleConstantRingDerivedPullback A
              (D.schemeFrobeniusIterate X₀ m) ≅
            AlgebraicGeometry.Scheme.proEtaleConstantRingDerivedPullback A
              (HPow.hPow (α := End (D.geometricFiber X₀).left)
                (D.geometricGaloisFrobenius X₀) m)),
        κiter 1 (by decide) = κ ∧
        (∀ (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n),
          ∃ hP : D.schemeFrobeniusIterate X₀ m ≫ D.schemeFrobeniusIterate X₀ n =
              D.schemeFrobeniusIterate X₀ (m + n),
          ∃ hG : (HPow.hPow (α := End (D.geometricFiber X₀).left)
                (D.geometricGaloisFrobenius X₀) m) ≫
              (HPow.hPow (α := End (D.geometricFiber X₀).left)
                (D.geometricGaloisFrobenius X₀) n) =
              (HPow.hPow (α := End (D.geometricFiber X₀).left)
                (D.geometricGaloisFrobenius X₀) (m + n)),
            (κiter (m + n) (by omega)).hom =
              eqToHom (congrArg
                (AlgebraicGeometry.Scheme.proEtaleConstantRingDerivedPullback A) hP.symm) ≫
              (AlgebraicGeometry.Scheme.proEtaleConstantRingPullbackComposition
                (D.schemeFrobeniusIterate X₀ m) (D.schemeFrobeniusIterate X₀ n) A).inv ≫
              Functor.whiskerLeft
                (AlgebraicGeometry.Scheme.proEtaleConstantRingDerivedPullback A
                  (D.schemeFrobeniusIterate X₀ n)) (κiter m hm).hom ≫
              Functor.whiskerRight (κiter n hn).hom
                (AlgebraicGeometry.Scheme.proEtaleConstantRingDerivedPullback A
                  (HPow.hPow (α := End (D.geometricFiber X₀).left)
                    (D.geometricGaloisFrobenius X₀) m)) ≫
              (AlgebraicGeometry.Scheme.proEtaleConstantRingPullbackComposition
                (HPow.hPow (α := End (D.geometricFiber X₀).left)
                  (D.geometricGaloisFrobenius X₀) m)
                (HPow.hPow (α := End (D.geometricFiber X₀).left)
                  (D.geometricGaloisFrobenius X₀) n) A).hom ≫
              eqToHom (congrArg
                (AlgebraicGeometry.Scheme.proEtaleConstantRingDerivedPullback A) hG)) ∧
        (∀ m : ℕ, 1 ≤ m →
          IsUniversalHomeomorphism
            ((D.geometricFiber X₀).left.iterateFrobenius D.prime
              (D.model_characteristic
                (pullback.fst X₀.hom
                  (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫ X₀.hom))
              (D.a * m))) ∧
        (∀ m : ℕ, 1 ≤ m →
          (D.geometricFiber X₀).left.iterateFrobenius D.prime
              (D.model_characteristic
                (pullback.fst X₀.hom
                  (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫ X₀.hom))
              (D.a * m) =
            D.schemeFrobeniusIterate X₀ m ≫
              (HPow.hPow (α := End (D.geometricFiber X₀).left)
                (D.arithmeticGaloisFrobenius X₀) m)) ∧
        (∀ m : ℕ, 1 ≤ m →
          (D.geometricFiber X₀).left.iterateFrobenius D.prime
              (D.model_characteristic
                (pullback.fst X₀.hom
                  (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫ X₀.hom))
              (D.a * m) =
            (HPow.hPow (α := End (D.geometricFiber X₀).left)
                (D.arithmeticGaloisFrobenius X₀) m) ≫
              D.schemeFrobeniusIterate X₀ m) ∧
        (∀ (m : ℕ) (hm : 1 ≤ m),
          ∃ r : 𝟭 (D.geometricFiber X₀).left.ProEt ≅
              AlgebraicGeometry.Scheme.proEtaleBaseChange
                ((D.geometricFiber X₀).left.iterateFrobenius D.prime
              (D.model_characteristic
                (pullback.fst X₀.hom
                  (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫ X₀.hom))
              (D.a * m)),
          ∃ τ : AlgebraicGeometry.Scheme.proEtaleConstantRingPullback A
              ((D.geometricFiber X₀).left.iterateFrobenius D.prime
              (D.model_characteristic
                (pullback.fst X₀.hom
                  (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫ X₀.hom))
              (D.a * m)) ≅ 𝟭 _,
            (∀ V : (D.geometricFiber X₀).left.ProEt,
              ∃ hV : (D.p : Γ(V.left, ⊤)) = 0,
                (r.hom.app V).left ≫
                    pullback.fst V.hom
                      ((D.geometricFiber X₀).left.iterateFrobenius D.prime
              (D.model_characteristic
                (pullback.fst X₀.hom
                  (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫ X₀.hom))
              (D.a * m)) =
                  V.left.iterateFrobenius D.prime hV (D.a * m)) ∧
            (∀ (M : AlgebraicGeometry.Scheme.proEtaleRingModules
                (D.geometricFiber X₀).left
                (AlgebraicGeometry.Scheme.proEtaleConstantRing
                  (D.geometricFiber X₀).left A))
                (V : (D.geometricFiber X₀).left.ProEt)
                (s : M.val.obj (Opposite.op V)),
              ((AlgebraicGeometry.Scheme.proEtaleConstantRingAdjunction A
                  ((D.geometricFiber X₀).left.iterateFrobenius D.prime
              (D.model_characteristic
                (pullback.fst X₀.hom
                  (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫ X₀.hom))
              (D.a * m))).unit.app M ≫
                (AlgebraicGeometry.Scheme.proEtaleConstantRingPushforward A
                  ((D.geometricFiber X₀).left.iterateFrobenius D.prime
              (D.model_characteristic
                (pullback.fst X₀.hom
                  (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫ X₀.hom))
              (D.a * m))).map
                    (τ.hom.app M)).val.app (Opposite.op V) s =
                M.val.map (r.inv.app V).op s) ∧
            ∃ w : D.schemeFrobeniusIterate X₀ m =
                ((D.geometricFiber X₀).left.iterateFrobenius D.prime
              (D.model_characteristic
                (pullback.fst X₀.hom
                  (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫ X₀.hom))
              (D.a * m)) ≫
                  (HPow.hPow (α := End (D.geometricFiber X₀).left)
                    (D.geometricGaloisFrobenius X₀) m),
              (κiter m hm).hom =
                eqToHom (congrArg
                  (AlgebraicGeometry.Scheme.proEtaleConstantRingDerivedPullback A) w) ≫
                (AlgebraicGeometry.Scheme.proEtaleConstantRingPullbackComposition
                  ((D.geometricFiber X₀).left.iterateFrobenius D.prime
              (D.model_characteristic
                (pullback.fst X₀.hom
                  (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫ X₀.hom))
              (D.a * m))
                  (HPow.hPow (α := End (D.geometricFiber X₀).left)
                    (D.geometricGaloisFrobenius X₀) m) A).inv ≫
                Functor.whiskerLeft
                  (AlgebraicGeometry.Scheme.proEtaleConstantRingDerivedPullback A
                    (HPow.hPow (α := End (D.geometricFiber X₀).left)
                      (D.geometricGaloisFrobenius X₀) m))
                  (AlgebraicGeometry.Scheme.proEtaleFrobeniusDerivedIso A τ).hom ≫
                (Functor.rightUnitor _).hom) := by
  sorry

end WeilConjectures.FiniteFieldDatum
