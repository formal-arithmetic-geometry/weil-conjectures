/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q89
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.TensorProduct.Basic

import Sheaf.RingTheory.FormallyEtaleAssociatedGraded
import WeilConjectures.AlgebraicGeometry.AffineTripleTensorBaseChange
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing

/-!
# Faithfully flat Taylor realization at the residue-field diagonal

Source: Stacks Project, Algebra, Tags 0H1D, 00HT, 00HR, 00MC, 00FN;
Morphisms, Tag 02GO (blueprint: lem-trf-diagonal-taylor-faithful-flatness).

The auxiliary structures package the conclusions, including the maps on every
infinitesimal neighbourhood. They select no existence witnesses. Every map in them
is fixed on representatives; in particular the completion equivalence is fixed on
every projection by finite Taylor truncation. Affine rings are the actual rings of
sections, and the source of the Taylor map is the intrinsic stalk. This expresses
independence of the affine neighbourhood without choosing a preferred affine chart.
The tensor-ring augmentation describes the residue-field-valued diagonal point.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w t

open CategoryTheory TensorProduct

namespace AlgebraicGeometry

/-- Localization at the prime kernel of a map to a field.
Source: Stacks, Algebra, Tag 00HT
(blueprint: lem-trf-diagonal-taylor-faithful-flatness). -/
def diagonalTaylorLocalRing {A : Type u} {K : Type v} [CommRing A] [Field K]
    (e : A →+* K) : CommRingCat.{u} :=
  letI : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  CommRingCat.of (Localization.AtPrime (RingHom.ker e))

/-- The actual localization homomorphism at the kernel.
Source: Stacks, Algebra, Tag 00HT
(blueprint: lem-trf-diagonal-taylor-faithful-flatness). -/
def diagonalTaylorLocalization {A : Type u} {K : Type v} [CommRing A] [Field K]
    (e : A →+* K) : A →+* diagonalTaylorLocalRing e :=
  letI : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  algebraMap A (Localization.AtPrime (RingHom.ker e))

/-- The extended diagonal ideal in its localization.
Source: Stacks, Algebra, Tags 00HT and 00MC
(blueprint: lem-trf-diagonal-taylor-faithful-flatness). -/
def diagonalTaylorLocalIdeal {A : Type u} {K : Type v} [CommRing A] [Field K]
    (e : A →+* K) : Ideal (diagonalTaylorLocalRing e) :=
  Ideal.map (diagonalTaylorLocalization e) (RingHom.ker e)

/-- The centered polynomial homomorphism, with coefficients in the right tensor factor.
Source: Stacks, Algebra, Tag 0H1D, applied to the translated etale chart
(blueprint: lem-trf-diagonal-taylor-faithful-flatness). -/
def diagonalTaylorCentered {k : Type u} {A : Type v} {K : Type w}
    [Field k] [CommRing A] [Field K] [Algebra k A] [Algebra k K]
    {n : ℕ} (x : Fin n → A) (e : A →+* K) :
    MvPolynomial (Fin n) K →+* A ⊗[k] K :=
  MvPolynomial.eval₂Hom Algebra.TensorProduct.includeRight.toRingHom
    (fun i ↦ x i ⊗ₜ[k] (1 : K) - (1 : A) ⊗ₜ[k] e (x i))

/-- All affine conclusions for one coefficient field. The augmentation is specified
on every pure tensor. The quotient equivalences are specified on every polynomial
or ring representative, and the completion equivalence on every finite projection.
The stalk comparison identifies `A_p` with the actual stalk, and `localMap` is the
localized base-change homomorphism. `factorization` specifies the composite in the node.

Source: Stacks, Algebra, Tags 0H1D, 00HT, 00MC
(blueprint: lem-trf-diagonal-taylor-faithful-flatness). -/
structure DiagonalTaylorAffineData {k : Type u} {A : Type v} {K : Type w}
    [Field k] [CommRing A] [Field K] [Algebra k A] [Algebra k K]
    {n : ℕ} (x : Fin n → A) (e : A →+* K)
    {R : Type t} [CommRing R] (germ : A →+* R)
    (T : R →+* MvPowerSeries (Fin n) K) where
  /-- Evaluation at the diagonal rational point. -/
  augmentation : A ⊗[k] K →+* K
  augmentation_tmul : ∀ (a : A) (l : K), augmentation (a ⊗ₜ[k] l) = e a * l
  /-- The prime of that point is in fact maximal. -/
  maximal : (RingHom.ker augmentation).IsMaximal
  quotient : ∀ (q : ℕ), 1 ≤ q →
    (MvPolynomial (Fin n) K ⧸ MvPolynomial.idealOfVars (Fin n) K ^ q) ≃+*
      ((A ⊗[k] K) ⧸ RingHom.ker augmentation ^ q)
  quotient_mk : ∀ (q : ℕ) (hq : 1 ≤ q) (p : MvPolynomial (Fin n) K),
    quotient q hq (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (diagonalTaylorCentered x e p)
  quotient_reduction : ∀ (q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r) (hqr : q ≤ r)
      (p : MvPolynomial (Fin n) K ⧸ MvPolynomial.idealOfVars (Fin n) K ^ r),
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hqr) (quotient r hr p) =
      quotient q hq (Ideal.Quotient.factor (Ideal.pow_le_pow_right hqr) p)
  localQuotient : ∀ (q : ℕ), 1 ≤ q →
    ((A ⊗[k] K) ⧸ RingHom.ker augmentation ^ q) ≃+*
      (diagonalTaylorLocalRing augmentation ⧸ diagonalTaylorLocalIdeal augmentation ^ q)
  localQuotient_mk : ∀ (q : ℕ) (hq : 1 ≤ q) (a : A ⊗[k] K),
    localQuotient q hq (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (diagonalTaylorLocalization augmentation a)
  localQuotient_reduction : ∀ (q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r) (hqr : q ≤ r)
      (a : (A ⊗[k] K) ⧸ RingHom.ker augmentation ^ r),
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hqr) (localQuotient r hr a) =
      localQuotient q hq (Ideal.Quotient.factor (Ideal.pow_le_pow_right hqr) a)
  completion : AdicCompletion (diagonalTaylorLocalIdeal augmentation)
      (diagonalTaylorLocalRing augmentation) ≃+* MvPowerSeries (Fin n) K
  completion_projection : ∀ (q : ℕ) (hq : 1 ≤ q) (S : MvPowerSeries (Fin n) K),
    AdicCompletion.evalₐ (diagonalTaylorLocalIdeal augmentation) q (completion.symm S) =
      localQuotient q hq (quotient q hq (Ideal.Quotient.mk _ (S.truncTotal q)))
  stalkEquiv : diagonalTaylorLocalRing e ≃+* R
  stalkEquiv_localization : ∀ a : A, stalkEquiv (diagonalTaylorLocalization e a) = germ a
  localMap : R →+* diagonalTaylorLocalRing augmentation
  localMap_germ : ∀ a : A,
    localMap (germ a) = diagonalTaylorLocalization augmentation (a ⊗ₜ[k] (1 : K))
  factorization : T = completion.toRingHom.comp
    ((algebraMap (diagonalTaylorLocalRing augmentation)
      (AdicCompletion (diagonalTaylorLocalIdeal augmentation)
        (diagonalTaylorLocalRing augmentation))).comp localMap)

/-- Naturality of all the affine maps under an extension of coefficient fields.
Every map is fixed on representatives, and both completion and quotient squares
commute. The coefficient extension does not alter the source ring or its stalk.

Source: Stacks, Algebra, Tag 0H1D, naturality; Section 00M9
(blueprint: lem-trf-diagonal-taylor-faithful-flatness). -/
structure DiagonalTaylorAffineExtension {k : Type u} {A : Type v}
    {L : Type w} {K : Type t} [Field k] [CommRing A] [Field L] [Field K]
    [Algebra k A] [Algebra k L] [Algebra k K]
    {n : ℕ} {x : Fin n → A} {e : A →+* L} {R : Type v} [CommRing R]
    {germ : A →+* R} {T : R →+* MvPowerSeries (Fin n) L} (i : L →+* K)
    (D : DiagonalTaylorAffineData (k := k) x e germ T)
    (E : DiagonalTaylorAffineData (k := k) x (i.comp e) germ ((MvPowerSeries.map i).comp T)) where
  tensorMap : A ⊗[k] L →+* A ⊗[k] K
  tensorMap_tmul : ∀ (a : A) (l : L), tensorMap (a ⊗ₜ[k] l) = a ⊗ₜ[k] i l
  quotientMap : ∀ q : ℕ,
    ((A ⊗[k] L) ⧸ RingHom.ker D.augmentation ^ q) →+*
      ((A ⊗[k] K) ⧸ RingHom.ker E.augmentation ^ q)
  quotientMap_mk : ∀ (q : ℕ) (a : A ⊗[k] L),
    quotientMap q (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (tensorMap a)
  quotient_square : ∀ (q : ℕ) (hq : 1 ≤ q) (p : MvPolynomial (Fin n) L),
    quotientMap q (D.quotient q hq (Ideal.Quotient.mk _ p)) =
      E.quotient q hq (Ideal.Quotient.mk _ (MvPolynomial.map i p))
  localMap : diagonalTaylorLocalRing D.augmentation →+*
    diagonalTaylorLocalRing E.augmentation
  localMap_localization : ∀ a : A ⊗[k] L,
    localMap (diagonalTaylorLocalization D.augmentation a) =
      diagonalTaylorLocalization E.augmentation (tensorMap a)
  localMap_stalk : localMap.comp D.localMap = E.localMap
  localQuotientMap : ∀ q : ℕ,
    (diagonalTaylorLocalRing D.augmentation ⧸ diagonalTaylorLocalIdeal D.augmentation ^ q)
      →+* (diagonalTaylorLocalRing E.augmentation ⧸
        diagonalTaylorLocalIdeal E.augmentation ^ q)
  localQuotientMap_mk : ∀ (q : ℕ) (a : diagonalTaylorLocalRing D.augmentation),
    localQuotientMap q (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (localMap a)
  localQuotient_square : ∀ (q : ℕ) (hq : 1 ≤ q)
      (a : (A ⊗[k] L) ⧸ RingHom.ker D.augmentation ^ q),
    localQuotientMap q (D.localQuotient q hq a) =
      E.localQuotient q hq (quotientMap q a)
  completionMap : AdicCompletion (diagonalTaylorLocalIdeal D.augmentation)
      (diagonalTaylorLocalRing D.augmentation) →+*
    AdicCompletion (diagonalTaylorLocalIdeal E.augmentation)
      (diagonalTaylorLocalRing E.augmentation)
  completion_projection : ∀ (q : ℕ)
      (z : AdicCompletion (diagonalTaylorLocalIdeal D.augmentation)
        (diagonalTaylorLocalRing D.augmentation)),
    AdicCompletion.evalₐ (diagonalTaylorLocalIdeal E.augmentation) q (completionMap z) =
      localQuotientMap q (AdicCompletion.evalₐ (diagonalTaylorLocalIdeal D.augmentation) q z)
  completion_square : E.completion.toRingHom.comp completionMap =
    (MvPowerSeries.map i).comp D.completion.toRingHom

/-- The affine realization on the actual sections of an affine neighbourhood.
The algebra structures are induced by the given coordinates and evaluation, rather
than supplied as extra hypotheses.
Source: Stacks, Schemes, Tag 01HV; Algebra, Tag 0H1D
(blueprint: lem-trf-diagonal-taylor-faithful-flatness). -/
def diagonalTaylorAffineAt {k : Type u} [Field k] {U : Scheme.{u}} {n : ℕ}
    (c : MvPolynomial (Fin n) k →+* Γ(U, ⊤)) (b : U)
    (V : U.Opens) (hb : b ∈ V) {K : Type v} [Field K]
    (i : U.residueField b →+* K)
    (T : U.presheaf.stalk b →+* MvPowerSeries (Fin n) K) : Type (max u v) :=
  letI : Algebra k Γ(U, V) :=
    ((U.presheaf.map (homOfLE le_top).op).hom.comp (c.comp MvPolynomial.C)).toAlgebra
  letI : Algebra k K := (i.comp ((U.Γevaluation b).hom.comp
    (c.comp MvPolynomial.C))).toAlgebra
  DiagonalTaylorAffineData (k := k)
    (fun j ↦ U.presheaf.map (homOfLE le_top).op (c (MvPolynomial.X j)))
    (i.comp (U.evaluation V b hb).hom) (U.presheaf.germ V b hb).hom T

/-- The coefficient-extension comparison on an affine neighbourhood, with precisely
the coefficient algebra structures induced by the chart and residue evaluation.
Source: Stacks, Algebra, Tag 0H1D; Section 00M9
(blueprint: lem-trf-diagonal-taylor-faithful-flatness). -/
def diagonalTaylorExtensionAt {k : Type u} [Field k] {U : Scheme.{u}} {n : ℕ}
    (c : MvPolynomial (Fin n) k →+* Γ(U, ⊤)) (b : U)
    (V : U.Opens) (hb : b ∈ V) {K : Type v} [Field K]
    (i : U.residueField b →+* K)
    (T : U.presheaf.stalk b →+* MvPowerSeries (Fin n) (U.residueField b))
    (D : diagonalTaylorAffineAt c b V hb (RingHom.id _) T)
    (E : diagonalTaylorAffineAt c b V hb i ((MvPowerSeries.map i).comp T)) :
    Type (max u v) :=
  letI : Algebra k Γ(U, V) :=
    ((U.presheaf.map (homOfLE le_top).op).hom.comp (c.comp MvPolynomial.C)).toAlgebra
  letI : Algebra k (U.residueField b) :=
    ((U.Γevaluation b).hom.comp (c.comp MvPolynomial.C)).toAlgebra
  letI : Algebra k K := (i.comp ((U.Γevaluation b).hom.comp
    (c.comp MvPolynomial.C))).toAlgebra
  DiagonalTaylorAffineExtension (k := k) i D E

/-- The Taylor realization at an arbitrary point is faithfully flat, agrees with
the inverse limit of the canonical quotient isomorphisms on every affine
neighbourhood, and is natural under every coefficient extension. The coordinates
give the map to the polynomial spectrum, the standard affine presentation of
`AffineSpace (ULift (Fin n)) (Spec k)` with the corresponding renamed variables.
The finite-type condition is imposed on the structure morphism determined by `c`.
No closedness, algebraicity, positive dimension, or characteristic assumption occurs.

Source: Stacks Project, Algebra, Tags 0H1D, 00HT, 00HR, 00MC, 00FN;
Morphisms, Tag 02GO
(blueprint: lem-trf-diagonal-taylor-faithful-flatness).

Proof:
1. Restrict the etale chart to each affine neighbourhood and base change to the
residue field (lem-a1-etale-open-restriction,
lem-weil-pbc-etale-scheme-base-change). Identify its ring with the tensor product
using lem-weil-pbc-affine-triple-tensor-base-change and translate each coordinate
by its residue. The augmentation is surjective, with maximal kernel J.
2. Apply lem-sfb-augmented-etale-associated-graded to the centered formally etale
map. It gives the actual compatible quotient isomorphisms P/I^q -> C/J^q.
3. Every denominator outside J is invertible modulo J^q: for its nonzero residue
d and u = 1-d^(-1)s, the inverse is d^(-1) times the sum of u^r for r < q.
Clearing denominators shows the kernel is precisely J^q. This proves the second
quotient isomorphism and compatibility with reduction, without assuming J = IC.
4. Identify affine localizations with stalks by
lem-weil-pbc-affine-open-stalk-localization. The inverse-limit identification of
lem-trf-etale-chart-rational-point-taylor-iso is characterized on every projection
by the finite Taylor truncation, hence is the limit of the maps of steps 2--3.
5. The map A -> A tensor_k L is faithfully flat by
lem-weil-pbc-field-extension-base-change-faithfully-flat. The contraction of J is p.
Use lem-weil-pbc-flat-local-ring-maps to localize; the resulting flat local map is
faithfully flat by lem-pc-local-flat-faithful-flat-reflects-surjective.
6. The tensor ring and its localization are Noetherian: use
lem-weil-pbc-etale-algebra-finite-presentation-localization,
lem-weil-pbc-finite-type-algebra-noetherian, and
lem-weil-pbc-localization-noetherian. Then
lem-weil-pbc-local-completion-faithfully-flat applies. Compose the two faithfully
flat maps and transport along the completion equivalence to obtain T.
7. Stalk maps and coordinate germs are intrinsic. On two affine neighbourhoods the
finite truncations coincide; equality on all projections gives the same completed
coordinate identification and the same T. The truncations give the coordinate
formula and the residue formula, including for fractions.
8. For L -> K, the tensor map sends a tensor l to a tensor i(l); evaluation
commutes, so the inverse image of J_K is J. All maps therefore localize and descend
to the power quotients. Their squares commute on polynomial and fraction
representatives. Passing to compatible sequences gives the completion square,
and finite truncation identifies its power-series map with coefficientwise i.
This also proves compatibility on A and on its localization. For n = 0 the
variable ideal is zero and the same maps identify the completed diagonal stalk
with the coefficient field; no step requires a coordinate. -/
theorem diagonalTaylor_faithfullyFlat {k : Type u} [Field k] (U : Scheme.{u})
    (n : ℕ) (c : MvPolynomial (Fin n) k →+* Γ(U, ⊤))
    (hchart : Etale (U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom c)))
    (hft : LocallyOfFiniteType
      (U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (c.comp MvPolynomial.C))))
    (hqc : QuasiCompact
      (U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (c.comp MvPolynomial.C)))) (b : U) :
    ∃ T : U.presheaf.stalk b →+* MvPowerSeries (Fin n) (U.residueField b),
      T.FaithfullyFlat ∧
      (∀ a : U.presheaf.stalk b, MvPowerSeries.constantCoeff (T a) = U.residue b a) ∧
      (∀ j : Fin n, T (U.presheaf.germ ⊤ b (by trivial) (c (MvPolynomial.X j))) =
        MvPowerSeries.C (U.Γevaluation b (c (MvPolynomial.X j))) + MvPowerSeries.X j) ∧
      (∀ (V : U.Opens) (hV : IsAffineOpen V) (hb : b ∈ V),
        ∃ D : diagonalTaylorAffineAt c b V hb (RingHom.id _) T,
          ∀ (K : Type (max u v)) [Field K] (i : U.residueField b →+* K),
            ∃ E : diagonalTaylorAffineAt c b V hb i ((MvPowerSeries.map i).comp T),
              Nonempty (diagonalTaylorExtensionAt c b V hb i T D E)) := by
  sorry

end AlgebraicGeometry
