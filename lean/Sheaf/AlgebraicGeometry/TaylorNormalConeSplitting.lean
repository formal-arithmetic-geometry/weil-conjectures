/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.AlgebraicGeometry.EtaleChartRationalPointTaylorIso
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.RingTheory.AssociatedGradedRing
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.LinearAlgebra.Basis.Defs
public import Sheaf.AlgebraicGeometry.NodalLocalTangentData
public import Sheaf.RingTheory.ProjectiveConeHilbertStandardDegrees
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.AlgebraicGeometry.Regular
import Mathlib.RingTheory.Smooth.Field
import WeilConjectures.RingTheory.FormallySmoothAdic
import WeilConjectures.RingTheory.FormallySmoothAdicClosedFiber
import Mathlib.RingTheory.RegularLocalRing.Defs
import Sheaf.RingTheory.RelativeCohenFlatPresentation
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Completeness
import WeilConjectures.RingTheory.CompletionRegularLocal
import Mathlib.RingTheory.LocalRing.Module
import Sheaf.RingTheory.RegularCompleteCoefficientCoordinates

/-! # Associated graded comparison for the local Taylor map

Source: the completed-diagonal comparison for Bierstone--Milman (1997), Definition 3.4
and proof of Theorem 9.6; Stacks Tags 0C35 and 0C0S for the local structure
(blueprint: lem-trf-taylor-normal-cone-splitting).

The residue field is the actual residue field of the original stalk. The input point
and its residue equation specify the residue-field-valued diagonal, and the Taylor map
is the composite through its actual stalk and the specified chart completion.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.TaylorNormalCone

/-- The canonical residue-field action on the cotangent space of the stalk.
Source: the definition of c and the chosen basis in the completed-diagonal comparison
(blueprint: lem-trf-taylor-normal-cone-splitting). -/
instance cotangentModule (M : Scheme.{u}) (a : M) :
    Module (M.residueField a) (IsLocalRing.maximalIdeal (M.presheaf.stalk a)).Cotangent :=
  inferInstanceAs (Module (IsLocalRing.ResidueField (M.presheaf.stalk a))
    (IsLocalRing.maximalIdeal (M.presheaf.stalk a)).Cotangent)

/-- The canonical residue-field algebra structure on the existing associated graded ring.
Source: step 6 of the completed-diagonal comparison, Stacks Tag 05GG
(blueprint: lem-trf-taylor-normal-cone-splitting). -/
instance gradedAlgebra (M : Scheme.{u}) (a : M) :
    Algebra (M.residueField a)
      (IsLocalRing.maximalIdeal (M.presheaf.stalk a)).associatedGraded :=
  Ideal.associatedGradedAlgebra (IsLocalRing.maximalIdeal (M.presheaf.stalk a))

/-- The local map from the original stalk to the diagonal stalk, including restriction
and transport along the specified equality of points.
Source: the affine tensor/localization description in step 1 of the completed-diagonal
comparison (blueprint: lem-trf-taylor-normal-cone-splitting). -/
def diagonalStalkMap {k : Type u} [Field k] {M : Scheme.{u}}
    (p : M ⟶ Spec (.of k)) (U : M.Opens) (a : U)
    [Algebra k (M.residueField a.1)]
    (b : EtaleChartTaylor.baseChange (U.ι ≫ p) (M.residueField a.1))
    (ha : (pullback.fst (U.ι ≫ p)
      (Spec.map (CommRingCat.ofHom (algebraMap k (M.residueField a.1))))) b = a) :
    M.presheaf.stalk a.1 →+*
      (EtaleChartTaylor.baseChange (U.ι ≫ p) (M.residueField a.1)).presheaf.stalk b :=
  ((U.stalkIso a).inv ≫
    (U.toScheme.presheaf.stalkCongr (Inseparable.of_eq ha.symm)).hom ≫
    (pullback.fst (U.ι ≫ p)
      (Spec.map (CommRingCat.ofHom (algebraMap k (M.residueField a.1))))).stalkMap b).hom

/-- The chart Taylor homomorphism, with its required completion factorization.
Source: steps 1 and 3, using the chart isomorphism of Tag 039M
(blueprint: lem-trf-taylor-normal-cone-splitting). -/
def taylorMap {k : Type u} [Field k] {M : Scheme.{u}}
    (p : M ⟶ Spec (.of k)) (U : M.Opens) (a : U)
    [Algebra k (M.residueField a.1)]
    (b : EtaleChartTaylor.baseChange (U.ι ≫ p) (M.residueField a.1))
    (ha : (pullback.fst (U.ι ≫ p)
      (Spec.map (CommRingCat.ofHom (algebraMap k (M.residueField a.1))))) b = a)
    {n : ℕ}
    (θ : MvPowerSeries (Fin n) (M.residueField a.1) ≃+*
      AdicCompletion
        (IsLocalRing.maximalIdeal
          ((EtaleChartTaylor.baseChange (U.ι ≫ p) (M.residueField a.1)).presheaf.stalk b))
        ((EtaleChartTaylor.baseChange (U.ι ≫ p) (M.residueField a.1)).presheaf.stalk b)) :
    M.presheaf.stalk a.1 →+* MvPowerSeries (Fin n) (M.residueField a.1) :=
  θ.symm.toRingHom.comp
    ((algebraMap _ _).comp (diagonalStalkMap p U a b ha))

/-- The homogeneous polynomial of exactly degree `q`, including zero components.
Source: the monomial calculation in step 6 of the completed-diagonal comparison
(blueprint: lem-trf-taylor-normal-cone-splitting). -/
def degreePart {L : Type v} [CommRing L] {n : ℕ} (q : ℕ)
    (f : MvPowerSeries (Fin n) L) : MvPolynomial (Fin n) L :=
  MvPowerSeries.truncTotal (q + 1) (MvPowerSeries.homogeneousComponent q f)

/-- The ideal of lowest nonzero total-degree parts, with the zero series excluded.
Source: steps 9 and 10 of the completed-diagonal comparison
(blueprint: lem-trf-taylor-normal-cone-splitting). -/
def lowestPartsIdeal {L : Type v} [Field L] {n : ℕ}
    (K : Ideal (MvPowerSeries (Fin n) L)) : Ideal (MvPolynomial (Fin n) L) :=
  Ideal.span {h | ∃ f ∈ K, f ≠ 0 ∧ h = degreePart f.order.toNat f}

/-- The linear Taylor parts are independent, the chosen cotangent basis identifies
`gr_m R` with its polynomial algebra, and all ideal initial parts commute with this
identification and extension to the Taylor ring.

Source: the completed-diagonal comparison needed for Bierstone--Milman (1997),
Definition 3.4 and proof of Theorem 9.6; Stacks Tags 0C35, 0C0S, 07NQ
(blueprint: lem-trf-taylor-normal-cone-splitting).

Proof (the ten steps of the node):
1. In an affine neighbourhood write R = C_p and D = (C tensor_k L)_q for the
   diagonal evaluation prime. Finite-type Noetherian permanence and localization
   (lem-weil-pbc-finite-type-algebra-noetherian, lem-weil-pbc-localization-noetherian)
   make both local rings Noetherian. Smoothness gives regularity of R by
   lem-weil-pbc-smooth-scheme-over-field-regular.
2. Characteristic zero gives formal smoothness of k -> L by
   lem-weil-pbc-char-zero-field-extension-formally-smooth. Lift the L-map over a
   square-zero ideal, combine with the R-map by the tensor universal property,
   and invert denominators, which lift units across a square-zero ideal. Thus
   R -> D is formally smooth in the adic sense (def-weil-pbc-formally-smooth-adic).
3. Apply lem-weil-pbc-fs-adic-flat-geometrically-regular-closed-fibre and
   lem-trf-relative-cohen-flat-presentation. The chart completion is the specified
   Taylor ring by lem-trf-etale-chart-rational-point-taylor-iso. The compatible
   coefficient sections need not be the constant embedding in Taylor coordinates.
4. Regroup L[[X,W]] as L[[X]][[W]]. For the finitely generated relation ideal H,
   the coefficientwise quotient has kernel H L[[X,W]], giving S = R-hat[[W]].
   Noetherianity of the power-series ring is supplied by
   lem-weil-pbc-power-series-field-cohen-regular-complete.
5. Completion is Noetherian, complete, local, and regular by
   lem-weil-pbc-adic-completion-noetherian, lem-weil-pbc-module-completion-complete,
   lem-weil-pbc-local-completion-local-ring, lem-weil-pbc-completion-regular-local.
   Modulo powers (lem-weil-pbc-adic-completion-mod-power) the cotangent basis is
   unchanged. Use lem-weil-pbc-regular-local-cotangent-dimension and
   lem-weil-pbc-nakayama-local-generators, then
   lem-trf-regular-complete-coefficient-coordinates, to obtain an isomorphism
   Psi : L[[Z,W]] -> S carrying Z_j to the Taylor image of z_j.
6. Powers of the variable ideal consist of series having no terms below that degree.
   Psi and its inverse preserve these powers. Their graded maps are inverse;
   degree one proves independence of the ell_j. Completion modulo powers gives
   the stated polynomial identification of gr_m R (def-weil-pbc-associated-graded-ring).
7. For f in I intersect m^q, the degree-q part of Psi(f) substitutes ell_j for Z_j:
   higher-order terms do not contribute, and coefficients contribute their residues.
   Products of representatives show that the displayed J_q form a homogeneous ideal.
8. Put A = R-hat and K = IA. Approximate the coefficients in a finite expression
   h = sum a_i f_i modulo m^(q+1), using lem-weil-pbc-adic-completion-mod-power.
   This identifies every initial class of K with a class from I intersect m^q,
   so its initial homogeneous ideal is exactly J, degree by degree.
9. The ideal K A[[W]] consists of series whose W-coefficients lie in K, by finite
   generation. Its degree-q part is sum W^nu (h_nu)_(q-|nu|), which lies in
   J L[Z,W]. Conversely every homogeneous generator of J and its monomial multiples
   occur as initial parts. Hence its initial ideal is J L[Z,W].
10. Transport by Psi, which extends the Taylor map and preserves order. Its graded
    map sends Z_j to ell_j, giving exactly the asserted ideal equality. For I=0
    both sides vanish; I=R gives the unit ideal. For c=0 Nakayama gives m=0,
    so R=L. Empty variable lists are allowed throughout.
-/
theorem taylor_normal_cone_splitting
    {k : Type u} [Field k] [CharZero k] {M : Scheme.{u}}
    (p : M ⟶ Spec (.of k)) [Smooth p] [LocallyOfFiniteType p] [QuasiCompact p]
    (U : M.Opens) (a : U) [Algebra k (M.residueField a.1)]
    (hscalar : algebraMap k (M.residueField a.1) =
      (M.residue a.1).hom.comp
        (((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫
          M.presheaf.germ ⊤ a.1 trivial).hom))
    (n : ℕ) (t : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) (Spec (.of k)))
    [Etale t]
    (ht : t ≫ (AffineSpace (ULift.{u} (Fin n)) (Spec (.of k)) ↘ Spec (.of k)) = U.ι ≫ p)
    (b : EtaleChartTaylor.baseChange (U.ι ≫ p) (M.residueField a.1))
    (ha : (pullback.fst (U.ι ≫ p)
      (Spec.map (CommRingCat.ofHom (algebraMap k (M.residueField a.1))))) b = a)
    (hb : Function.Bijective (EtaleChartTaylor.residueMap (U.ι ≫ p) b))
    (hdiag : ∀ f : M.presheaf.stalk a.1,
      (EtaleChartTaylor.baseChange (U.ι ≫ p) (M.residueField a.1)).residue b
        (diagonalStalkMap p U a b ha f) =
      EtaleChartTaylor.residueMap (U.ι ≫ p) b (M.residue a.1 f))
    (θ : MvPowerSeries (Fin n) (M.residueField a.1) ≃+*
      AdicCompletion
        (IsLocalRing.maximalIdeal
          ((EtaleChartTaylor.baseChange (U.ι ≫ p) (M.residueField a.1)).presheaf.stalk b))
        ((EtaleChartTaylor.baseChange (U.ι ≫ p) (M.residueField a.1)).presheaf.stalk b))
    (hθ : EtaleChartTaylor.IsExpansion (EtaleChartTaylor.scalarMap (U.ι ≫ p) b)
      (EtaleChartTaylor.centeredCoordinate (U.ι ≫ p) t b hb) θ.toRingHom)
    (c : ℕ) (z : Fin c → IsLocalRing.maximalIdeal (M.presheaf.stalk a.1))
    (B : Module.Basis (Fin c) (M.residueField a.1)
      (IsLocalRing.maximalIdeal (M.presheaf.stalk a.1)).Cotangent)
    (hz : ∀ j : Fin c, B j =
      (IsLocalRing.maximalIdeal (M.presheaf.stalk a.1)).toCotangent (z j)) :
    LinearIndependent (M.residueField a.1)
      (fun j : Fin c ↦ degreePart 1 (taylorMap p U a b ha θ (z j))) ∧
    ∃ e : MvPolynomial (Fin c) (M.residueField a.1) ≃ₐ[M.residueField a.1]
        (IsLocalRing.maximalIdeal (M.presheaf.stalk a.1)).associatedGraded,
      (∀ j : Fin c, e (MvPolynomial.X j) =
        NodalLocal.initialForm (M.presheaf.stalk a.1) 1
          ⟨(z j).1, by simpa only [pow_one] using (z j).2⟩) ∧
      ∀ I : Ideal (M.presheaf.stalk a.1),
        lowestPartsIdeal (Ideal.map (taylorMap p U a b ha θ) I) =
          Ideal.map (MvPolynomial.aeval
            (fun j : Fin c ↦ degreePart 1 (taylorMap p U a b ha θ (z j)))).toRingHom
            (Ideal.map e.symm.toRingHom
              (Hironaka.adicInitialIdeal (IsLocalRing.maximalIdeal (M.presheaf.stalk a.1)) I)) ∧
        ∀ (q : ℕ) (f : ↥(IsLocalRing.maximalIdeal (M.presheaf.stalk a.1) ^ q)), f.1 ∈ I →
          degreePart q (taylorMap p U a b ha θ f.1) =
            MvPolynomial.aeval
              (fun j : Fin c ↦ degreePart 1 (taylorMap p U a b ha θ (z j)))
              (e.symm (NodalLocal.initialForm (M.presheaf.stalk a.1) q f)) := by
  sorry

end AlgebraicGeometry.TaylorNormalCone
