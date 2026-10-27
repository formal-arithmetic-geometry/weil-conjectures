/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q150
-/
module

public import Sheaf.AlgebraicGeometry.RegularImmersionClassSystem
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.RingTheory.Localization.Basic

/-! # Supported continuity at localization limits

Source: ILO, Expose XVI 2.1--2.3 and 3.2--3.3; Stacks Project, Tag 03Q6
(blueprint: def-per-regular-supported-local-continuity).

The canonical supported continuity predicate for affine ind-etale presentations
of Noetherian localization and strict-localization pairs.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  DerivedCategory.singleFunctors Ext.homEquiv Ext.comp Ext.mk₀ Ext.mapExactFunctor

/-- The actual localization or strict-localization morphisms, allowing isomorphic
presentations. The first alternative includes arbitrary multiplicative-set localizations;
the second uses the published geometric strict-localization structural map.
Source: ILO XVI 3.2; Stacks 03Q6
(blueprint: def-per-regular-supported-local-continuity). -/
def IsRegularClassLocalLimit {X Y : Scheme.{u}} (v : Y ⟶ X) : Prop :=
  (∃ (R B : CommRingCat.{u}) (S : Submonoid R) (a : Algebra R B)
      (_h : @IsLocalization R _ S B _ a) (e : X ≅ Spec R) (e' : Y ≅ Spec B),
    v ≫ e.hom = e'.hom ≫ Spec.map (CommRingCat.ofHom (@algebraMap R B _ _ a))) ∨
  (∃ (Ω : Type u) (_hΩ : Field Ω) (_haΩ : IsAlgClosed Ω)
      (s : Spec (CommRingCat.of Ω) ⟶ X) (e : Y ≅ Scheme.strictHenselizationScheme s),
    v = e.hom ≫ Scheme.strictHenselizationStructuralMap s)

/-- The canonical supported continuity identification, expressed by class descent and
by eventual vanishing. Only affine ind-etale presentations of a localization or a
strict localization of a Noetherian pair occur here. The restriction equations specify
the true canonical maps, in every degree and every signed Tate twist.
Source: Stacks 03Q6, supported extraction; ILO XVI 3.2
(blueprint: def-per-regular-supported-local-continuity). -/
def RegularClassLocalContinuity (ell : ℕ) (h : ell.Prime) : Prop :=
  ∀ (n : ℕ) (_hn : 0 < n) {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D E : J ⥤ Scheme.{u}) (i : E ⟶ D)
    [∀ j, IsAffine (D.obj j)] [∀ j, IsNoetherian (D.obj j)]
    [∀ j, IsNoetherian (E.obj j)] [∀ j, IsClosedImmersion (i.app j)]
    [∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)]
    [∀ {j k : J} (f : j ⟶ k), AlgebraicGeometry.Etale (D.map f)]
    (sq : ∀ {j k : J} (f : j ⟶ k), IsPullback (E.map f) (i.app j) (i.app k) (D.map f))
    (C : Cone D) (_hC : IsLimit C) (B : Cone E) (_hB : IsLimit B)
    [IsNoetherian C.pt] [IsNoetherian B.pt]
    (iLimit : B.pt ⟶ C.pt) [IsClosedImmersion iLimit]
    (sqLimit : ∀ j, IsPullback (B.π.app j) iLimit (i.app j) (C.π.app j))
    (j₀ : J) (_hv : IsRegularClassLocalLimit (C.π.app j₀))
    (hD : ∀ j, IsUnit (ell : Γ(D.obj j, ⊤)))
    (hLimit : IsUnit (ell : Γ(C.pt, ⊤))) (a : ℤ) (q : ℕ),
    (∀ x : regularSupportedCohomology (regularClassCoefficient ell n) (ell ^ n)
        (regularClassAnnihilator ell n) iLimit a q,
      ∃ (j : J) (y : regularSupportedCohomology (regularClassCoefficient ell n) (ell ^ n)
          (regularClassAnnihilator ell n) (i.app j) a q),
        RegularSupportedRestriction _ _ _ (regularClassTransport ell h n)
          (i.app j) iLimit (C.π.app j) (B.π.app j) (sqLimit j)
          (regularClassExponentUnit ell n (D.obj j) (hD j))
          (regularClassExponentUnit ell n C.pt hLimit) a q y x) ∧
    (∀ (j : J) (y : regularSupportedCohomology (regularClassCoefficient ell n) (ell ^ n)
        (regularClassAnnihilator ell n) (i.app j) a q),
      RegularSupportedRestriction _ _ _ (regularClassTransport ell h n)
        (i.app j) iLimit (C.π.app j) (B.π.app j) (sqLimit j)
        (regularClassExponentUnit ell n (D.obj j) (hD j))
        (regularClassExponentUnit ell n C.pt hLimit) a q y 0 →
      ∃ (k : J) (f : k ⟶ j),
        RegularSupportedRestriction _ _ _ (regularClassTransport ell h n)
          (i.app j) (i.app k) (D.map f) (E.map f) (sq f)
          (regularClassExponentUnit ell n (D.obj j) (hD j))
          (regularClassExponentUnit ell n (D.obj k) (hD k)) a q y 0)

end AlgebraicGeometry.Etale
