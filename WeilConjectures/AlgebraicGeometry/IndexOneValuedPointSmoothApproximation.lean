/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.FieldTheory.SeparableExtension

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.FiniteType

/-! # Smooth approximation of a valued point for an index-one DVR extension

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, §3.6, Proposition 4, p.79,
as used in §7.2, Theorem 1, pp.176–177
(blueprint: lem-sfb-index-one-valued-point-smooth-approximation).

The generic restriction of the integral point is specified by both pullback
projections, which uniquely determine it. Residue separability allows transcendence.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A valued point of a smooth finite-type generic fibre factors through a smooth affine
finite-type scheme over the smaller DVR. No excellence, completeness, or separability
of the fraction-field extension is required.

Source: BLR, Néron Models, §3.6, Proposition 4, p.79, and §7.2, Theorem 1, pp.176–177
(blueprint: lem-sfb-index-one-valued-point-smooth-approximation).

Proof plan:
1. Choose an affine neighbourhood `Spec C` of the image of `w`. Scale its finitely many
   algebra generators by powers of a uniformizer so their images lie in `A`. They generate
   a finite-type `R`-subalgebra `B₀` of `C`, with a map to `A` and with `B₀[1/π] = C`.
   The generic fibre is smooth, and multiplication by `π` is injective.
2. Use lem-sfb-index-one-differential-defect-criterion to obtain a finite nonnegative
   differential torsion defect `d`. At each step dilate the residue centre
   `ker (Bⱼ → A → κ(A))`. The node lem-sfb-index-one-residue-dilatation-defect-drop
   preserves finite type, the generic algebra, and the compatible valued point, while
   decreasing the defect to at most `max (0, δ - 1)`. Induction gives defect zero after
   at most `d` steps, including the case `d = 0` with no dilatations.
3. The defect criterion gives a principal smooth neighbourhood `Spec (B_d[1/f])` with
   the image of `f` a unit in `A`. This is the required affine finite-type `U`, and the
   localized map gives `a`. The affine tensor-product description of pullbacks
   (lem-weil-pbc-fibre-product-affine-spectra) identifies its generic fibre with
   `Spec (C[1/f])`, giving `h`. The compatible algebra maps imply `aK ≫ h = w`.
   Since `π` also generates the maximal ideal of `A`, its generic spectrum is `Spec L`.

Here `q` is the structure morphism of `W`, `f` that of `U`, and `aK` is the unique
map to the generic pullback whose projections are the restriction of `a` and the
canonical map `Spec L → Spec K`. -/
theorem exists_smooth_affine_factorization_of_index_one
    (R A K L : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra R A] [IsLocalHom (algebraMap R A)]
    (hRA : Function.Injective (algebraMap R A))
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra A L] [IsFractionRing A L]
    (hindex : (IsLocalRing.maximalIdeal R).map (algebraMap R A) =
      IsLocalRing.maximalIdeal A)
    (hsep : Algebra.IsSeparableExtension (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField A))
    (W : Scheme.{u}) (q : W ⟶ Spec (.of K))
    [Smooth q] [LocallyOfFiniteType q] [QuasiCompact q]
    (w : Spec (.of L) ⟶ W)
    (hw : w ≫ q =
      Spec.map (CommRingCat.ofHom (IsFractionRing.map (K := K) (L := L) hRA))) :
    ∃ (U : Scheme.{u}) (f : U ⟶ Spec (.of R)),
      IsAffine U ∧ Smooth f ∧ LocallyOfFiniteType f ∧ QuasiCompact f ∧
      ∃ a : Spec (.of A) ⟶ U,
        a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)) ∧
        ∃ h : pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶ W,
          h ≫ q = pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
          ∃ aK : Spec (.of L) ⟶
              pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))),
            aK ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
              Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ a ∧
            aK ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
              Spec.map (CommRingCat.ofHom (IsFractionRing.map (K := K) (L := L) hRA)) ∧
            aK ≫ h = w := by
  sorry

end AlgebraicGeometry
