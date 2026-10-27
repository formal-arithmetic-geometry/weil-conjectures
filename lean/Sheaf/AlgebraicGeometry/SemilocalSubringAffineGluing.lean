/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Affine gluing of independent semilocal subrings

Source: Stacks Project, Varieties, Tags 09N4 and 09NJ
(blueprint: lem-trf-semilocal-subring-affine-gluing).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Independent one-dimensional Noetherian semilocal subrings of a common fraction field
admit an affine gluing. In the local case the closed points are exactly the distinct chart
closed points, the corresponding localizations are the given subrings, and the canonical
maps from the spectrum of the field exhibit every overlap as a pullback.

Source: Stacks Project, Varieties, Tag 09N4, and the local consequences in Tag 09NJ.
(blueprint: lem-trf-semilocal-subring-affine-gluing).

Proof:
1. Induct on the nonempty finite family, constructing the intersection ring. The singleton
   case is the identity open immersion (def-weil-open-immersion).
2. Put B equal to the intersection of all but the first ring. If the tensor map from the
   first ring and B were not surjective, lem-trf-one-dimensional-subrings-common-dvr-criterion
   gives a proper DVR containing both. Its maximal ideal contracts to a nonzero, hence
   maximal, ideal of B. A chart containing this point identifies its localization with a
   chart localization inside the DVR, by lem-weil-pbc-spec-domain-stalks-function-field and
   def-weil-pbc-localization-at-prime. This puts a second original ring in that DVR,
   contradicting the pairwise tensor-surjectivity criterion.
3. Apply lem-trf-two-semilocal-rings-intersection-cover to the first ring and B. Compose
   its open charts with the induction cover; functoriality of def-weil-affine-spectrum
   identifies these maps with the original inclusions.
4. The intersection is a domain. The generic stalk identifies its fraction field with K
   (lem-weil-pbc-spec-domain-stalks-function-field). A prime chain lies in a chart containing
   its largest prime, so dimension is one (def-weil-pbc-krull-dimension-ring). Every maximal
   prime comes from a maximal prime of a chart, proving semilocality.
5. The Noetherian affine charts make the glued spectrum locally Noetherian
   (pqf-def-locnoeth). Apply pqf-lem-affine-open-locnoeth to obtain Noetherianity of the ring.
6. A closed point in two charts would put both rings, hence K by tensor surjectivity, in
   its local ring. This is impossible at a nonzero maximal ideal of a dimension-one domain
   (def-weil-pbc-localization-at-prime). Thus exactly one chart contains each closed point.
7. If all charts are local, their maximal ideals give distinct nonzero maximal ideals of
   the glued ring and exhaust them. The stalk identifications give the displayed compatible
   ring equivalences. Two charts intersect only at the generic point, whose stalk is K;
   all maps are induced by the given inclusions, giving the stated canonical pullback.
-/
theorem exists_semilocal_subring_affine_gluing
    {K : Type u} [Field K] (r : ℕ) (hr : 1 ≤ r) (A : Fin r → Subring K)
    [∀ i, IsFractionRing (A i) K] [∀ i, IsNoetherianRing (A i)]
    [∀ i, Finite (MaximalSpectrum (A i))]
    (hdim : ∀ i, ringKrullDim (A i) = 1)
    (hsurj : ∀ i j, i ≠ j → Function.Surjective
      (Algebra.TensorProduct.productMap
        (IsScalarTower.toAlgHom ℤ (A i) K) (IsScalarTower.toAlgHom ℤ (A j) K))) :
    ∃ (R : Subring K) (hRA : ∀ i, R ≤ A i),
      IsDomain R ∧ IsNoetherianRing R ∧ Finite (MaximalSpectrum R) ∧
      ringKrullDim R = 1 ∧ IsFractionRing R K ∧
      (∀ i, IsOpenImmersion (Spec.map (CommRingCat.ofHom (Subring.inclusion (hRA i))))) ∧
      (∀ x : Spec (CommRingCat.of R), ∃ i,
        x ∈ Set.range (Spec.map (CommRingCat.ofHom (Subring.inclusion (hRA i))))) ∧
      (∀ x : Spec (CommRingCat.of R), IsClosed ({x} : Set (Spec (CommRingCat.of R))) →
        ∃! i, x ∈ Set.range (Spec.map (CommRingCat.ofHom (Subring.inclusion (hRA i))))) ∧
      (∀ [hl : ∀ i, IsLocalRing (A i)],
        ∃ m : Fin r → MaximalSpectrum R,
          Function.Injective m ∧ Function.Surjective m ∧
          (∀ i, Spec.map (CommRingCat.ofHom (Subring.inclusion (hRA i)))
            ⟨IsLocalRing.maximalIdeal (A i), inferInstance⟩ =
              ⟨(m i).asIdeal, inferInstance⟩) ∧
          (∀ i, ∃ e : Localization.AtPrime (m i).asIdeal ≃+* A i,
            ∀ x : R, e (algebraMap R (Localization.AtPrime (m i).asIdeal) x) =
              Subring.inclusion (hRA i) x) ∧
          (∀ i j, i ≠ j → IsPullback
            (Spec.map (CommRingCat.ofHom (A i).subtype))
            (Spec.map (CommRingCat.ofHom (A j).subtype))
            (Spec.map (CommRingCat.ofHom (Subring.inclusion (hRA i))))
            (Spec.map (CommRingCat.ofHom (Subring.inclusion (hRA j)))))) := by
  sorry

end AlgebraicGeometry
