/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q08 and Q31
-/
module

public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.Paper.IntrinsicCompletionCompleted

/-!
# Transport of the published intrinsic completion

Source: blueprint order 1247; Stacks Tags 099M and 091Z
(blueprint: def-weil-pbc-intrinsic-completion).

The published Koszul fiber is reused through the canonical comparison between
its completed quotient-ring presentation and the continuous-functions presentation.
Both rings are inverse limits of the finite quotient sheaves. Neither is identified
with the constant sheaf associated to A. The transport preserves the prescribed
fiber differential, positive-power transitions and the completion unit (u,0).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The same arithmetic datum in the published completion interface.
Source: blueprint order 1239 (blueprint: def-weil-pbc-intrinsic-completion). -/
def intrinsicPresentationDatum {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) : ProEtaleAdicCoefficientDatum A where
  toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
  quotientFinite := d.quotientFinite

variable (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- Exact restriction to the published completed-ring presentation.
Source: blueprint order 1247 (blueprint: def-weil-pbc-intrinsic-completion). -/
abbrev intrinsicPresentationModules : pbcModules T (pbcAdicCompletion T d) ⥤
    adicDatumModules T (intrinsicPresentationDatum d) :=
  pbcRestrict (pbcCompletedComparison T d).hom

/-- Exact restriction back through the inverse of the canonical ring comparison.
Source: blueprint order 1247 (blueprint: def-weil-pbc-intrinsic-completion). -/
abbrev intrinsicPresentationModulesBack : adicDatumModules T (intrinsicPresentationDatum d) ⥤
    pbcModules T (pbcAdicCompletion T d) :=
  pbcRestrict (pbcCompletedComparison T d).inv

/-- The round trip is uniquely fixed by identity on underlying sections.
Source: blueprint order 1247; Stacks Tag 03DA
(blueprint: def-weil-pbc-intrinsic-completion).
Proof: the two restricted actions compose by the inverse/hom identity of the
canonical ring isomorphism. Identity on sections is therefore linear in both
directions and natural in objects and site restrictions. Its two composites
are identities. Faithfulness on sections determines the isomorphism uniquely. -/
theorem intrinsicPresentationRoundTrip_exists :
    ∃! e : 𝟭 (pbcModules T (pbcAdicCompletion T d)) ≅
        intrinsicPresentationModules T d ⋙ intrinsicPresentationModulesBack T d,
      ∀ (M : pbcModules T (pbcAdicCompletion T d)) (U : T.ProEtᵒᵖ)
        (x : M.val.obj U), (e.hom.app M).val.app U x = x := by
  sorry

/-- The actual identity-on-sections coefficient round trip.
Source: blueprint order 1247 (blueprint: def-weil-pbc-intrinsic-completion). -/
def intrinsicPresentationRoundTrip : 𝟭 (pbcModules T (pbcAdicCompletion T d)) ≅
    intrinsicPresentationModules T d ⋙ intrinsicPresentationModulesBack T d :=
  (intrinsicPresentationRoundTrip_exists T d).exists.choose

/-- Apply the coefficient comparison to a representative, term by term.
Source: blueprint order 1247 (blueprint: def-weil-pbc-intrinsic-completion). -/
abbrev intrinsicPresentationComplex :=
  (intrinsicPresentationModules T d).mapHomologicalComplex (.up ℤ)

/-- Return the published explicit Koszul fiber to the specified coefficient ring.
Source: blueprint order 1247 (blueprint: def-weil-pbc-intrinsic-completion). -/
def intrinsicCompletionComplex (r : ℕ) (a : Fin r → A)
    (C : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) :=
  ((intrinsicPresentationModulesBack T d).mapHomologicalComplex (.up ℤ)).obj
    (completedKoszulFiber T (intrinsicPresentationDatum d) r a
      ((intrinsicPresentationComplex T d).obj C))

/-- The transported (u,0) completion map in each degree.
Source: blueprint order 1247 (blueprint: def-weil-pbc-intrinsic-completion). -/
def intrinsicCompletionUnitComponent (r : ℕ) (a : Fin r → A)
    (C : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) (q : ℤ) :
    C.X q ⟶ (intrinsicCompletionComplex T d r a C).X q :=
  (intrinsicPresentationRoundTrip T d).hom.app (C.X q) ≫
    (intrinsicPresentationModulesBack T d).map
      ((completedKoszulUnitComplex T (intrinsicPresentationDatum d) r a
        ((intrinsicPresentationComplex T d).obj C)).f q)

/-- The transported completion unit commutes with differentials.
Source: blueprint order 1247 (blueprint: def-weil-pbc-intrinsic-completion).
Proof: naturality of the identity-on-sections round trip commutes with C's
differential. The published completion unit is a chain map. Apply the additive
backward restriction functor to its chain-map equation and compose the two
equalities; functoriality gives exactly the displayed degreewise equation. -/
theorem intrinsicCompletionUnitComponent_comm (r : ℕ) (a : Fin r → A)
    (C : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) (q k : ℤ) :
    intrinsicCompletionUnitComponent T d r a C q ≫
        (intrinsicCompletionComplex T d r a C).d q k =
      C.d q k ≫ intrinsicCompletionUnitComponent T d r a C k := by
  sorry

/-- The published completion chain map, transported with its fixed section normalization.
Source: blueprint order 1247 (blueprint: def-weil-pbc-intrinsic-completion). -/
def intrinsicCompletionComplexUnit (r : ℕ) (a : Fin r → A)
    (C : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) :
    C ⟶ intrinsicCompletionComplex T d r a C where
  f q := intrinsicCompletionUnitComponent T d r a C q
  comm' q k _ := intrinsicCompletionUnitComponent_comm T d r a C q k

/-- Intrinsic completion uses the published explicit Koszul fiber on any representative.
Exact mutually inverse coefficient restrictions preserve its product, differential,
transitions and unit. No representative or unrelated fiber is chosen.
Source: blueprint order 1247 (blueprint: def-weil-pbc-intrinsic-completion). -/
def intrinsicCompletion (r : ℕ) (a : Fin r → A)
    (_ha : Ideal.span (Set.range a) = d.ideal)
    (_K : reductionDerivedCategory T (completedReductionCoefficient T d))
    (C : CochainComplex (reductionModules T (completedReductionCoefficient T d)) ℤ)
    (_e : DerivedCategory.Q.obj C ≅ _K) :
    reductionDerivedCategory T (completedReductionCoefficient T d) :=
  DerivedCategory.Q.obj (intrinsicCompletionComplex T d r a C)

/-- The transported published (u,0) completion unit, with the supplied realization.
Source: blueprint order 1247 (blueprint: def-weil-pbc-intrinsic-completion). -/
def intrinsicCompletionUnit (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = d.ideal)
    (K : reductionDerivedCategory T (completedReductionCoefficient T d))
    (C : CochainComplex (reductionModules T (completedReductionCoefficient T d)) ℤ)
    (e : DerivedCategory.Q.obj C ≅ K) : K ⟶ intrinsicCompletion T d r a ha K C e :=
  e.inv ≫ DerivedCategory.Q.map (intrinsicCompletionComplexUnit T d r a C)

/-- Derived I-completeness is invertibility of the same transported completion unit.
Source: blueprint order 1247 (blueprint: def-weil-pbc-intrinsic-completion). -/
def IsDerivedCompleteIntrinsic (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = d.ideal)
    (K : reductionDerivedCategory T (completedReductionCoefficient T d))
    (C : CochainComplex (reductionModules T (completedReductionCoefficient T d)) ℤ)
    (e : DerivedCategory.Q.obj C ≅ K) : Prop :=
  IsIso (intrinsicCompletionUnit T d r a ha K C e)

end AlgebraicGeometry.Scheme
