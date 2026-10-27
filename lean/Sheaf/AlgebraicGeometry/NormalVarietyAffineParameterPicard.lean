module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Sheaf.AlgebraicGeometry.AffineSpaceOpenInvertibleTrivial

/-! # Line-module fibres at rational affine-space parameters

Source: Stacks Project, Varieties, Tag 0BEH, `lemma-rational-equivalence-for-Pic`
(blueprint: lem-sfb-normal-variety-affine-parameter-picard).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- An invertible module on a normal variety times an open of affine space has
isomorphic tensor pullbacks at any two rational parameter points. The structure
map of `U` is the open immersion `j` followed by the polynomial projection.

Source: Stacks Project, Varieties, Tag 0BEH, `lemma-rational-equivalence-for-Pic`
(blueprint: lem-sfb-normal-variety-affine-parameter-picard).

Proof:
1. Put Y = X ×_k U and f = pr_X. A field is Noetherian, hence X is locally
   Noetherian by `pqf-lem-locnoeth-lft`. On an affine open Spec A of X and a
   principal open D(g) of U, `lem-weil-pbc-fibre-product-affine-spectra` gives
   the ring A[t₁, ..., tₙ] localized at g. It is generated over A by the
   variables and g⁻¹, so f is locally of finite type. The same permanence
   lemma makes Y locally Noetherian.
2. The polynomial projection is flat by `lem-nagata-polynomial-projection-flat`.
   Restricting its source to U preserves its local rings and flatness at every
   point (`def-weil-flat-morphism`), so f is flat.
3. At x in X the fibre is the open U_{κ(x)} in affine n-space over κ(x).
   The point p supplies a point of this open. Its ambient polynomial ring is
   a domain by `lem-sfb-polynomial-field-ufd`, so the fibre is integral and
   nonempty (`def-pc-integral-scheme`).
4. At the generic point, `lem-sfb-affine-space-open-invertible-trivial`
   trivializes the pulled-back invertible module. Apply
   `lem-sfb-normal-noetherian-generic-line-pullback`: the base is integral
   and normal; both schemes are locally Noetherian; f is flat and locally of
   finite type with integral nonempty fibres. Obtain an invertible M on X
   and an isomorphism f* M ≅ N.
5. For r = p,q the canonical section i_r = (id_X, sX ≫ r) satisfies
   i_r ≫ f = id_X by `def-pc-fibre-product`. Pull back the isomorphism of
   Step 4 and use the identity and composition comparisons of
   `def-pc-module-pullback` to identify each i_r* N with M. Compose the
   isomorphism for p with the inverse of the one for q.
-/
theorem nonempty_iso_tensorPullback_lift_of_normal_variety
    (k : Type u) [Field k] (X : Scheme.{u}) [IsIntegral X]
    (sX : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType sX] [QuasiCompact sX]
    [IsClosedImmersion (pullback.diagonal sX)]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    (n : ℕ) (U : Scheme.{u})
    (j : U ⟶ Spec (CommRingCat.of (MvPolynomial (Fin n) k))) [IsOpenImmersion j]
    (p q : Spec (CommRingCat.of k) ⟶ U)
    (hp : p ≫ (j ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C))) = 𝟙 _)
    (hq : q ≫ (j ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C))) = 𝟙 _)
    (N : (pullback sX (j ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C)))).Modules)
    [N.IsInvertible] :
    Nonempty
      ((Scheme.Modules.tensorPullback
          (pullback.lift (𝟙 X) (sX ≫ p) (by simp [hp]))).obj N ≅
        (Scheme.Modules.tensorPullback
          (pullback.lift (𝟙 X) (sX ≫ q) (by simp [hq]))).obj N) := by
  sorry

end AlgebraicGeometry
