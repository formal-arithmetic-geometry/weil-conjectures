/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

import Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import Sheaf.Paper.ScalarExtensionDualEvaluation

/-! # Normalized signed finite Tate coefficient and exponent maps

Source: blueprint main-20261015, sec-smooth-purity/sk-def-sp-scalar-extension,
proof paragraph (3), expanded signed normalization and Kummer compatibility.
(blueprint: lem-sp-signed-tate-coefficient-exponent-normalization).

All objects and normalization predicates are the published ones. A natural index n
represents the positive exponent n + 1. A quotient homomorphism to A is equivalent
to annihilation by that power of ell; its composite with f supplies the map to B.
The identity and composition clauses use heterogeneous equality solely to compare
the presentations indexed by equal quotient homomorphisms (all ZMod ring maps
with a fixed codomain are equal). No section equality is conditional on HEq here.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- The unique signed coefficient families, their ordinary scalar extensions, and
both rings' unique signed Kummer comparisons at common exponents satisfy identity,
composition and the
coefficient/exponent squares, including all negative degrees.

Source: blueprint scalar-extension proof (3), Stacks 03EK and 03EM.
(blueprint: lem-sp-signed-tate-coefficient-exponent-normalization).

Proof:
1. Use the compatible primitive-root cover of det-def-sp-tate-twist-locally-free.
   Localized tensor restriction and the tensor unit identify each root tensor line
   with the coefficient unit. Tensor powers and their internal duals have the
   corresponding power basis and dual basis, on every further slice.
2. The balanced root-tensor rule defines degree one by the bilinear universal
   property; degree zero is f. Repeated balanced tensor products define positive
   degrees, sending the A-basis to the B-basis.
3. Ordinary scalar extension sends these bases to bases, even when f is not flat.
   Its local inverses glue by the sheaf property of internal Hom.
4. Apply lem-sp-scalar-extension-dual-evaluation to a positive power, then
   precompose its extended dual with the inverse positive comparison. Its value
   on c(x) is f(lambda(x)). The dual basis proves it is invertible and unique.
5. Unit and root formulas force degrees zero and one; the tensor universal
   property forces positive degrees; evaluation on the local target basis forces
   negative degrees. This proves uniqueness without assuming f surjective.
6. The actual Kummer power map induces the exponent comparison by clause (2) of
   det-def-sp-tate-twist-locally-free. Extend it by the identity, tensor powers,
   and inverse precomposition on duals. These formulas force the unique family.
7. The identity root map and multiplication of Kummer exponents give the identity
   and composition laws. Tensoring proves positive degrees; inverse
   precomposition proves negative degrees, as slice-wise internal-Hom identities.
8. Both coefficient/exponent paths on a root tensor are the Kummer power of the
   root tensored with f of the coefficient. Tensor induction proves all positive
   degrees. In negative degree evaluate both paths on the image positive basis:
   each value is f(lambda(x)). Local basis detection and Hom descent prove equality.
9. On a scalar tensor b tensor x the two extended paths have values b times the
   preceding semilinear paths. The bilinear universal property proves the ordinary
   scalar-extension square. Taking b = 1 recovers the semilinear square.
-/
theorem signedTateCoefficientExponentNormalization
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)] :
    (∀ (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A),
      (∃! c : ScalarExtensionTateMaps f T ℓ n a,
        IsCanonicalScalarExtensionTateMaps f T ℓ n a c) ∧
      ∀ r : ℤ,
        (scalarExtensionTateLine T ℓ A n a r).IsFiniteLocallyFreeOfRank 1 ∧
        (scalarExtensionTateLine T ℓ B n (f.comp a) r).IsFiniteLocallyFreeOfRank 1 ∧
        ∃! e : (proEtaleRingExtension (proEtaleConstantRingMap (T := T) f)).obj
            (scalarExtensionTateLine T ℓ A n a r) ≅
              scalarExtensionTateLine T ℓ B n (f.comp a) r,
          ∀ (U : T.ProEtᵒᵖ) (b : (proEtaleConstantRing T B).obj.obj U)
            (x : (scalarExtensionTateLine T ℓ A n a r).val.obj U),
            e.hom.val.app U
                (reductionTensorSection T (proEtaleConstantRingMap (T := T) f) _ U b x) =
              b • (@id ((scalarExtensionTateLine T ℓ B n (f.comp a) r).val.obj U)
                ((scalarExtensionTateMaps f T ℓ n a r).val.app U x))) ∧
    (∀ (k n : ℕ) (hkn : k ≤ n) (a : ZMod (ℓ ^ (k + 1)) →+* A),
      ∃! e : ∀ r : ℤ, scalarExtensionTateLine T ℓ A n
          (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hkn))
            (ZMod (ℓ ^ (k + 1))))) r ≅ scalarExtensionTateLine T ℓ A k a r,
        IsCanonicalScalarExtensionTateLevelMaps T ℓ A k n hkn a
          (fun r ↦ (e r).hom)) ∧
    (∀ (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A) (r : ℤ),
      HEq (scalarExtensionTateLevelIso T ℓ A n n (Nat.le_refl n) a r).hom
        (𝟙 (scalarExtensionTateLine T ℓ A n a r))) ∧
    (∀ (j k n : ℕ) (hjk : j ≤ k) (hkn : k ≤ n)
        (a : ZMod (ℓ ^ (j + 1)) →+* A) (r : ℤ),
      HEq ((scalarExtensionTateLevelIso T ℓ A k n hkn
          (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hjk))
            (ZMod (ℓ ^ (j + 1))))) r).hom ≫
          (scalarExtensionTateLevelIso T ℓ A j k hjk a r).hom)
        (scalarExtensionTateLevelIso T ℓ A j n (Nat.le_trans hjk hkn) a r).hom) ∧
    (∀ (k n : ℕ) (hkn : k ≤ n) (a : ZMod (ℓ ^ (k + 1)) →+* A),
      ∃! e : ∀ r : ℤ, scalarExtensionTateLine T ℓ B n
          ((f.comp a).comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hkn))
            (ZMod (ℓ ^ (k + 1))))) r ≅ scalarExtensionTateLine T ℓ B k (f.comp a) r,
        IsCanonicalScalarExtensionTateLevelMaps T ℓ B k n hkn (f.comp a)
          (fun r ↦ (e r).hom)) ∧
    (∀ (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A) (r : ℤ),
      HEq (scalarExtensionTateLevelIso T ℓ B n n (Nat.le_refl n) (f.comp a) r).hom
        (𝟙 (scalarExtensionTateLine T ℓ B n (f.comp a) r))) ∧
    (∀ (j k n : ℕ) (hjk : j ≤ k) (hkn : k ≤ n)
        (a : ZMod (ℓ ^ (j + 1)) →+* A) (r : ℤ),
      HEq ((scalarExtensionTateLevelIso T ℓ B k n hkn
          ((f.comp a).comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hjk))
            (ZMod (ℓ ^ (j + 1))))) r).hom ≫
          (scalarExtensionTateLevelIso T ℓ B j k hjk (f.comp a) r).hom)
        (scalarExtensionTateLevelIso T ℓ B j n (Nat.le_trans hjk hkn) (f.comp a) r).hom) ∧
    (∀ (k n : ℕ) (hkn : k ≤ n) (a : ZMod (ℓ ^ (k + 1)) →+* A) (r : ℤ),
      scalarExtensionTateMaps f T ℓ n
          (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hkn))
            (ZMod (ℓ ^ (k + 1))))) r ≫
        (proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := T) f)).map
          (scalarExtensionTateLevelIso T ℓ B k n hkn (f.comp a) r).hom =
      (scalarExtensionTateLevelIso T ℓ A k n hkn a r).hom ≫
        scalarExtensionTateMaps f T ℓ k a r) ∧
    (∀ (k n : ℕ) (hkn : k ≤ n) (a : ZMod (ℓ ^ (k + 1)) →+* A) (r : ℤ),
      (proEtaleRingExtension (proEtaleConstantRingMap (T := T) f)).map
          (scalarExtensionTateLevelIso T ℓ A k n hkn a r).hom ≫
        (scalarExtensionTateIso f T ℓ k a r).hom =
      (scalarExtensionTateIso f T ℓ n
          (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hkn))
            (ZMod (ℓ ^ (k + 1))))) r).hom ≫
        (scalarExtensionTateLevelIso T ℓ B k n hkn (f.comp a) r).hom) := by
  sorry

end AlgebraicGeometry.ProEtale
