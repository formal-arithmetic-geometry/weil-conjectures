/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q74
-/
module

public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Sheaf.AlgebraicGeometry.PureDimension
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.PowerSeries.Basic
import Sheaf.RingTheory.FieldsExcellent
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.RingTheory.QuasiExcellentNagata
import WeilConjectures.RingTheory.CompletionFiniteExtension
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Completeness
import Sheaf.AlgebraicGeometry.IsRegularScheme
import Sheaf.RingTheory.RegularCompleteCoefficientCoordinates

/-! # Coordinates on the actual normalization branches of a curve

Source: Stacks Project, Varieties, Tags 0C1R(8), 0C3V; Algebra, Tags 07N9, 0C0S(2)
(blueprint: lem-trf-normalized-curve-branch-coordinates).

The product is indexed by the points of the normalization fibre itself. The equations
at every quotient level characterize the canonical completed maps, and the equations
on coefficients retain the structural field rather than an abstract residue-field choice.
The stalk B of the pushforward of the normalization's structure sheaf, its structural map
from A (the stalk at x of the structure-sheaf map of the normalization), the ideal m_A B
and the completions H, C are written out from Mathlib primitives; so is the structural
scalar map k → O_{X,x} (global sections of the structure map, then the germ at x).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The actual local ring at a point of the normalization fibre. Source: Stacks Project,
Varieties, Tags 0C1R and 0C3V (blueprint: lem-trf-normalized-curve-branch-coordinates). -/
abbrev normalizedCurveBranchLocalRing (X : Scheme.{u}) (x : X)
    (y : {y : X.reducedNormalization // X.fromReducedNormalization y = x}) : Type u :=
  X.reducedNormalization.presheaf.stalk y.1

/-- The maximal-ideal completion of the actual branch local ring. Source: Stacks Project,
Varieties, Tag 0C3V (blueprint: lem-trf-normalized-curve-branch-coordinates). -/
abbrev normalizedCurveBranchCompletion (X : Scheme.{u}) (x : X)
    (y : {y : X.reducedNormalization // X.fromReducedNormalization y = x}) : Type u :=
  AdicCompletion (IsLocalRing.maximalIdeal (normalizedCurveBranchLocalRing X x y))
    (normalizedCurveBranchLocalRing X x y)

/-- Restriction from the normalization pushforward stalk to the actual branch stalk.
Source: Stacks Project, Algebra, Tag 07N9; Varieties, Tag 0C3V
(blueprint: lem-trf-normalized-curve-branch-coordinates). -/
def normalizedCurveBranchStalkMap (X : Scheme.{u}) (x : X)
    (y : {y : X.reducedNormalization // X.fromReducedNormalization y = x}) :
    ((TopCat.Presheaf.pushforward CommRingCat X.fromReducedNormalization.base).obj
      X.reducedNormalization.presheaf).stalk x →+* normalizedCurveBranchLocalRing X x y :=
  (((((TopCat.Presheaf.pushforward CommRingCat X.fromReducedNormalization.base).obj
    X.reducedNormalization.presheaf).stalkCongr (Inseparable.of_eq y.2.symm)).hom) ≫
      X.reducedNormalization.presheaf.stalkPushforward CommRingCat
        X.fromReducedNormalization.base y.1).hom

/-- The structural coefficient map into a completed branch: global sections of the
structure map of the normalization, the germ at the branch point, then completion.
Source: Stacks Project, Algebra, Tag 0C0S(2)
(blueprint: lem-trf-normalized-curve-branch-coordinates). -/
def normalizedCurveBranchCoefficient {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (x : X)
    (y : {y : X.reducedNormalization // X.fromReducedNormalization y = x}) :
    k →+* normalizedCurveBranchCompletion X x y :=
  (algebraMap (normalizedCurveBranchLocalRing X x y)
    (normalizedCurveBranchCompletion X x y)).comp
      ((X.reducedNormalization.presheaf.germ ⊤ y.1 (Set.mem_univ y.1)).hom.comp
        ((X.fromReducedNormalization ≫ p).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom))

/-- The product coordinate equivalence induced by individual branch coordinates.
Source: Stacks Project, Varieties, Tag 0C1R(8); Algebra, Tag 0C0S(2)
(blueprint: lem-trf-normalized-curve-branch-coordinates). -/
def normalizedCurveBranchProductCoordinates {k : Type u} [Field k] {X : Scheme.{u}}
    {x : X} {C : Type u} [CommRing C]
    (e : C ≃+* ((y : {y : X.reducedNormalization // X.fromReducedNormalization y = x}) →
        normalizedCurveBranchCompletion X x y))
    (E : (y : {y : X.reducedNormalization // X.fromReducedNormalization y = x}) →
      PowerSeries k ≃+* normalizedCurveBranchCompletion X x y) :
    C ≃+* ({y : X.reducedNormalization // X.fromReducedNormalization y = x} → PowerSeries k) :=
  e.trans (RingEquiv.piCongrRight (fun y ↦ (E y).symm))

/-- Complete DVR branches, prescribed-parameter coordinates, and their diagonal residue image.
Source: Stacks Project, Varieties, Tags 0C1R(8), 0C3V; Algebra, Tags 07N9, 0C0S(2)
(blueprint: lem-trf-normalized-curve-branch-coordinates).

Proof, following the seven DAG steps:
1. `lem-trf-curve-delta-completion-data` gives the finite nonempty actual fibre,
   structural residue fields, finite integral closure B, and completion H of A.
2. Fields are excellent; finite-type algebras and localizations are excellent. Excellence
   implies quasi-excellence and hence Nagata, so the local ring A is Nagata.
3. `lem-trf-normalization-affine-stalk-closure` identifies B on an affine neighbourhood.
   Localization-spectrum and affine-open-stalk-localization identify its localizations
   over the maximal ideal of A with the actual local rings at the fibre points, fixing A.
4. `lem-trf-nagata-normalization-dvr-branches` makes these local rings DVRs.
   `lem-trf-finite-dvr-branch-completion` and completion-finite-extension give the product
   decomposition of C into their completions, with the stated quotient-level maps.
5. Local-completion-local-ring identifies the maximal ideal and structural residue field.
   Module-completion-complete gives completeness for that maximal ideal.
6. A DVR is regular local of dimension one. Apply regular-complete-coefficient-coordinates
   with d = 1 and each prescribed generator, and take the product of the inverse maps.
7. The first quotient of every completed local map is the structural residue map k → k,
   hence the identity. A series differs from its constant coefficient by a multiple of T.
   Consequently every image of h has constant term its residue. Structural constants
   supply every diagonal tuple, giving exactly the asserted image.

The DVR clauses are spelled out as local principal ideal domains that are not fields.
The local structures in the conclusion are witnesses, not additional hypotheses.
The two quotient-level formulas specify the H-algebra structures and the canonical
product isomorphism; coefficient-preserving ring equivalences are k-algebra equivalences.
Here A = `X.presheaf.stalk x`, B is the stalk at x of the pushforward of the normalization's
structure presheaf with A → B the stalk of the structure-sheaf map, H is the m_A-adic and C
the m_A B-adic completion.
-/
theorem normalized_curve_branch_coordinates
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    (p : X ⟶ Spec (.of k)) [IsReduced X] [LocallyOfFiniteType p] [QuasiCompact p]
    (hpure : X.IsPureDimension 1) (x : X) (hx : IsClosed ({x} : Set X)) :
    Finite {y : X.reducedNormalization // X.fromReducedNormalization y = x} ∧
    Nonempty {y : X.reducedNormalization // X.fromReducedNormalization y = x} ∧
    (∀ y : {y : X.reducedNormalization // X.fromReducedNormalization y = x},
      IsDomain (normalizedCurveBranchLocalRing X x y) ∧
      IsPrincipalIdealRing (normalizedCurveBranchLocalRing X x y) ∧
      ¬ IsField (normalizedCurveBranchLocalRing X x y)) ∧
    ∃ φ : X.presheaf.stalk x →+*
        ((TopCat.Presheaf.pushforward CommRingCat X.fromReducedNormalization.base).obj
          X.reducedNormalization.presheaf).stalk x,
      φ = ((TopCat.Presheaf.stalkFunctor CommRingCat x).map X.fromReducedNormalization.c).hom ∧
    ∃ (hlocal : ∀ y : {y : X.reducedNormalization // X.fromReducedNormalization y = x},
        IsLocalRing (normalizedCurveBranchCompletion X x y))
      (hH : IsLocalRing (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x)))
      (r : (X.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ≃+* k)
      (g : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)
        →+* AdicCompletion ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).map φ)
          (((TopCat.Presheaf.pushforward CommRingCat X.fromReducedNormalization.base).obj
            X.reducedNormalization.presheaf).stalk x))
      (e : AdicCompletion ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).map φ)
          (((TopCat.Presheaf.pushforward CommRingCat X.fromReducedNormalization.base).obj
            X.reducedNormalization.presheaf).stalk x) ≃+*
        ((y : {y : X.reducedNormalization // X.fromReducedNormalization y = x}) →
          normalizedCurveBranchCompletion X x y)),
      (∀ a : k, r (Ideal.Quotient.mk _ ((X.presheaf.germ ⊤ x (Set.mem_univ x)).hom
        (p.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom a)))) = a) ∧
      RingHom.ker (r.toRingHom.comp
          (AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal (X.presheaf.stalk x))).toRingHom) =
        @IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x)) _ hH ∧
      (∀ (n : ℕ)
          (h : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
            (X.presheaf.stalk x))
          (a : X.presheaf.stalk x),
        AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) n h =
            Ideal.Quotient.mk _ a →
          AdicCompletion.evalₐ ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).map φ) n (g h) =
            Ideal.Quotient.mk _ (φ a)) ∧
      (∀ (y : {y : X.reducedNormalization // X.fromReducedNormalization y = x})
          (n : ℕ)
          (c : AdicCompletion ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).map φ)
            (((TopCat.Presheaf.pushforward CommRingCat X.fromReducedNormalization.base).obj
              X.reducedNormalization.presheaf).stalk x))
          (b : ((TopCat.Presheaf.pushforward CommRingCat X.fromReducedNormalization.base).obj
            X.reducedNormalization.presheaf).stalk x),
        AdicCompletion.evalₐ ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).map φ) n c =
            Ideal.Quotient.mk _ b →
          AdicCompletion.evalₐ
              (IsLocalRing.maximalIdeal (normalizedCurveBranchLocalRing X x y)) n (e c y) =
            Ideal.Quotient.mk _ (normalizedCurveBranchStalkMap X x y b)) ∧
      (∀ y : {y : X.reducedNormalization // X.fromReducedNormalization y = x},
        IsDomain (normalizedCurveBranchCompletion X x y) ∧
        IsPrincipalIdealRing (normalizedCurveBranchCompletion X x y) ∧
        ¬ IsField (normalizedCurveBranchCompletion X x y) ∧
        IsAdicComplete (@IsLocalRing.maximalIdeal (normalizedCurveBranchCompletion X x y)
          _ (hlocal y)) (normalizedCurveBranchCompletion X x y) ∧
        Function.Bijective ((Ideal.Quotient.mk
          (@IsLocalRing.maximalIdeal (normalizedCurveBranchCompletion X x y) _ (hlocal y))).comp
            (normalizedCurveBranchCoefficient p x y))) ∧
      (∀ t : (y : {y : X.reducedNormalization // X.fromReducedNormalization y = x}) →
          normalizedCurveBranchCompletion X x y,
        (∀ y, Ideal.span {t y} =
          @IsLocalRing.maximalIdeal (normalizedCurveBranchCompletion X x y) _ (hlocal y)) →
        ∃ E : (y : {y : X.reducedNormalization // X.fromReducedNormalization y = x}) →
            PowerSeries k ≃+* normalizedCurveBranchCompletion X x y,
          (∀ y, (∀ a : k, E y (PowerSeries.C a) =
              normalizedCurveBranchCoefficient p x y a) ∧
            E y PowerSeries.X = t y ∧
            (∀ n : ℕ, Ideal.comap (E y).toRingHom
              ((@IsLocalRing.maximalIdeal (normalizedCurveBranchCompletion X x y)
                _ (hlocal y)) ^ n) = Ideal.span {PowerSeries.X} ^ n)) ∧
          (∀ (h : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
                (X.presheaf.stalk x))
              (y : {y : X.reducedNormalization // X.fromReducedNormalization y = x}),
            PowerSeries.constantCoeff (normalizedCurveBranchProductCoordinates e E (g h) y) =
              r (AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) h)) ∧
          Set.range (fun h : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
              (X.presheaf.stalk x) ↦
            fun y ↦ PowerSeries.constantCoeff
              (normalizedCurveBranchProductCoordinates e E (g h) y)) =
            Set.range (fun a : k ↦
              fun _ : {y : X.reducedNormalization // X.fromReducedNormalization y = x} ↦ a)) := by
  sorry

end AlgebraicGeometry.Scheme
