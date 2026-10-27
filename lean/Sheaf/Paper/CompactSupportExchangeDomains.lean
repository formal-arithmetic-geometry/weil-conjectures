/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange
public import Sheaf.Paper.QbarCompactSupportBaseChange
public import Sheaf.Paper.PbcQbarCompletedPullback
public import Sheaf.Paper.CompactSupportExchangeTransport
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.CompleteCompactSupportProetale
public import Sheaf.Paper.FiniteExtensionCompactSupportBaseChange
public import WeilConjectures.Compactification.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import all Sheaf.Paper.CompactSupportExchangeTransport
import all Sheaf.Paper.PbcCompletedPullbackActual
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.PurityFiniteSetting

/-! # Compact-support exchange on the specified coefficient domains

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/
prop-functor-package.proof.md, clause (4); Stacks Tags 03DJ and 0F7L
(blueprint: lem-sf-bc-compact-support-domain).

The finite, completed, localized and common-stage statements use their published
canonical maps.

## Main statements

* `sfCompactSupportDomain_finite`: finite exchange, refinement and extension-by-zero bounds.
* `sfCompactSupportDomain_witness`: invertibility and independence of the retained origin.
* `sfCompactSupportDomain_integral`: the completed proper/open composite is invertible.
* `sfCompactSupportDomain_rational`: normalized rational exchange and lattice independence.
* `sfCompactSupportDomain_qbar`: normalized common-stage representatives and independence.
* The three `Refinement` statements retain compactification compatibility after transport.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open scoped CategoryTheory.Functor

namespace WeilConjectures

/-- The retained Cartesian identification from the operation datum's square.
Source: clause (4) (blueprint: lem-sf-bc-compact-support-domain). -/
def sfDomainSquare {D : FiniteFieldDatum.{u}} (Q : SixFunctorCompactifiedSquare D) :
    ChosenCartesianSquare Q.g'.hom.left Q.f'.hom.left Q.f.hom.left Q.g.hom.left where
  w := Q.square.w
  isoPullback := Q.square.isoPullback
  hom_fst := Q.square.isoPullback_hom_fst
  hom_snd := Q.square.isoPullback_hom_snd

/-- The proper Cartesian square for the chosen compactification.
Source: clause (4) (blueprint: lem-sf-bc-compact-support-domain). -/
def sfDomainProperSquare {D : FiniteFieldDatum.{u}} (Q : SixFunctorCompactifiedSquare D) :
    ChosenCartesianSquare Q.h.hom.left Q.compactification'.g Q.compactification.g
      Q.g.hom.left where
  w := Q.properSquare.w
  isoPullback := Q.properSquare.isoPullback
  hom_fst := Q.properSquare.isoPullback_hom_fst
  hom_snd := Q.properSquare.isoPullback_hom_snd

/-- The open Cartesian square for the chosen compactification.
Source: clause (4) (blueprint: lem-sf-bc-compact-support-domain). -/
def sfDomainOpenSquare {D : FiniteFieldDatum.{u}} (Q : SixFunctorCompactifiedSquare D) :
    OpenImmersionSquare Q.g'.hom.left Q.compactification'.i Q.compactification.i
      Q.h.hom.left where
  w := Q.openSquare.w
  isoPullback := Q.openSquare.isoPullback
  hom_fst := Q.openSquare.isoPullback_hom_fst
  hom_snd := Q.openSquare.isoPullback_hom_snd
  isOpenImmersion := Q.open_i
  isOpenImmersion' := Q.open_i'

section Finite
variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (E : Type u) [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
  (Q : SixFunctorCompactifiedSquare D)

/-- The specified etale proper/open composite, supplying the proved finiteness
of the positive coefficient quotient. Source: Stacks 0F7L, displayed composite
(blueprint: lem-sf-bc-compact-support-domain). -/
def sfDomainEtaleExchange (c : Compactification Q.f.hom.left) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap
    (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)) Q.square c

/-- The canonical proper/open compactification comparison on the etale site.
Source: Stacks 0F7L, refinement comparisons
(blueprint: lem-sf-bc-compact-support-domain). -/
def sfDomainEtaleComparison [QuasiCompact Q.f.hom.left] (c d : Compactification Q.f.hom.left) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  (Etale.derivedPlusFormalism
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))).shriekIso c d

/-- The canonical comparison between the base-changed compactifications.
Source: Stacks 0F7L (blueprint: lem-sf-bc-compact-support-domain). -/
def sfDomainEtaleComparison' [QuasiCompact Q.f'.hom.left] (c d : Compactification Q.f.hom.left) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  (Etale.derivedPlusFormalism
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))).shriekIso
      (c.ofIsPullback Q.square) (d.ofIsPullback Q.square)

/-- Finite etale exchange is invertible and intertwined by the canonical comparisons.
Extension by zero preserves the specified lower bound and annihilating scalar.
Source: clause (4); Stacks 03DJ and 0F7L
(blueprint: lem-sf-bc-compact-support-domain).

Proof:
1. Apply lem-pur-finite-setting-comparison-hypotheses to the four finite-type corners:
Noetherianity, finite dimension, finite quotients and an invertible annihilator follow.
2. Exact A-linear open extension preserves cohomology bounds and the scalar annihilator.
3. Expand def-cbc-exchange-map as proper exchange on j_!K followed by Rp'_*(beta_K).
Theorem thm-weil-pbc-bounded-below applies to the first factor; the coefficient-forgetting
comparison reflects its invertibility. The derived open base-change theorem gives the second.
4. thm-cbc-finite-torsion identifies every proper/open refinement comparison with shriekIso.
Its comparison square gives the equation below. The shriekIso cocycle removes the common
refinement, defining the same compactification-independent map. -/
theorem sfCompactSupportDomain_finite
    [IsSeparated Q.X.obj.hom] [IsSeparated Q.Y.obj.hom]
    [IsSeparated Q.X'.obj.hom] [IsSeparated Q.Y'.obj.hom]
    [IsSeparated Q.g.hom.left] [LocallyOfFiniteType Q.g.hom.left]
    [QuasiCompact Q.g.hom.left]
    [IsSeparated Q.g'.hom.left] [LocallyOfFiniteType Q.g'.hom.left]
    [QuasiCompact Q.g'.hom.left]
    [IsSeparated Q.f'.hom.left] [LocallyOfFiniteType Q.f'.hom.left]
    [QuasiCompact Q.f'.hom.left]
    [IsSeparated Q.f.hom.left] [LocallyOfFiniteType Q.f.hom.left]
    [QuasiCompact Q.f.hom.left]
    (c : Compactification Q.f.hom.left)
    (K : DerivedCategory.Plus (Sheaf Q.X.obj.left.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))))
    (b : ℤ) [K.obj.IsLE b] :
    IsIso ((sfDomainEtaleExchange D C E n hn Q c).app K) ∧
    (∀ d : Compactification Q.f.hom.left,
      (Etale.upperStar
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
        Q.g.hom.left).mapDerivedCategoryPlus.map
          ((sfDomainEtaleComparison D C E n hn Q c d).hom.app K) ≫
        (sfDomainEtaleExchange D C E n hn Q d).app K =
      (sfDomainEtaleExchange D C E n hn Q c).app K ≫
        (sfDomainEtaleComparison' D C E n hn Q c d).hom.app
          ((Etale.upperStar
            (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
            Q.g'.hom.left).mapDerivedCategoryPlus.obj K)) ∧
    (∀ (a : ℤ), K.obj.IsGE a →
      ((Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
        c.i).mapDerivedCategory.obj K.obj).IsGE a) ∧
    (∀ (r : ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)),
      r • 𝟙 K.obj = 0 →
      r • 𝟙 ((Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
        c.i).mapDerivedCategory.obj K.obj) = 0) := by
  sorry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HasDerivedCategory.standard
  AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
  AlgebraicGeometry.ProEtale.compactExchangeTransportAtWitness

/-- The actual finite pro-etale composite is invertible at its retained bounded-below origin.
Source: clause (4), finite pro-etale paragraph
(blueprint: lem-sf-bc-compact-support-domain).
Proof: use thm-cbc-finite-level-proetale at the supplied compactification and witness.
The exact open site comparison extends the witness to j_!K. Proper site comparison
identifies the proper mate, and the open unit normalization identifies beta. Thus the
actual composite is the witnessed conjugate of the etale exchange, hence invertible. -/
theorem sfCompactSupportDomain_finiteProetale
    [IsSeparated Q.X.obj.hom] [IsSeparated Q.Y.obj.hom]
    [IsSeparated Q.X'.obj.hom] [IsSeparated Q.Y'.obj.hom]
    [IsSeparated Q.g.hom.left] [LocallyOfFiniteType Q.g.hom.left]
    [QuasiCompact Q.g.hom.left]
    [IsSeparated Q.g'.hom.left] [LocallyOfFiniteType Q.g'.hom.left]
    [QuasiCompact Q.g'.hom.left]
    [IsSeparated Q.f'.hom.left] [LocallyOfFiniteType Q.f'.hom.left]
    [QuasiCompact Q.f'.hom.left]
    [IsSeparated Q.f.hom.left] [LocallyOfFiniteType Q.f.hom.left]
    [QuasiCompact Q.f.hom.left]
    (c : Compactification Q.f.hom.left)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Q.X.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))))
    (_W : FixedEtaleOriginWitness Q.X.obj.left
      (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)) K) :
    IsIso ((ProEtale.canonicalFiniteCoefficientCompactSupportExchange C.l E n hn
      (sfDomainSquare Q) c).app K.obj) := by
  exact ProEtale.isIso_csAuxiliaryExchange C.l E n hn (sfDomainSquare Q) c K _W

/-- The existing witness conjugation, specialized to the actual finite quotient.
Its source and target comparisons are the canonical proper/open site comparisons.
Source: clause (4), finite pro-etale conjugation
(blueprint: lem-sf-bc-compact-support-domain). -/
def sfDomainWitnessExchange (c : Compactification Q.f.hom.left)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Q.X.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))))
    (W : FixedEtaleOriginWitness Q.X.obj.left
      (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)) K) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  ProEtale.compactExchangeTransportAtWitness
    (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))
    Q.square c W.complex K.obj W.iso

/-- Invertibility and independence of the retained finite origin.
Source: clause (4), finite pro-etale paragraph
(blueprint: lem-sf-bc-compact-support-domain).
Proof: thm-cbc-finite-level-proetale identifies the displayed conjugate with the
compact-support theorem map. Its factors are invertible by the finite etale theorem
and canonical site comparisons. Full faithfulness of comparison on D+ uniquely lifts
an isomorphism between two witnesses. Naturality of the two endpoint comparisons and
of etale exchange cancels this isomorphism and proves equality of the conjugates. -/
theorem sfCompactSupportDomain_witness
    [IsSeparated Q.X.obj.hom] [IsSeparated Q.Y.obj.hom]
    [IsSeparated Q.X'.obj.hom] [IsSeparated Q.Y'.obj.hom]
    [IsSeparated Q.g.hom.left] [LocallyOfFiniteType Q.g.hom.left]
    [QuasiCompact Q.g.hom.left]
    [IsSeparated Q.g'.hom.left] [LocallyOfFiniteType Q.g'.hom.left]
    [QuasiCompact Q.g'.hom.left]
    [IsSeparated Q.f'.hom.left] [LocallyOfFiniteType Q.f'.hom.left]
    [QuasiCompact Q.f'.hom.left]
    [IsSeparated Q.f.hom.left] [LocallyOfFiniteType Q.f.hom.left]
    [QuasiCompact Q.f.hom.left]
    (c : Compactification Q.f.hom.left)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Q.X.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))))
    (W : FixedEtaleOriginWitness Q.X.obj.left
      (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)) K) :
    IsIso (sfDomainWitnessExchange D C E n hn Q c K W) ∧
    ∀ W' : FixedEtaleOriginWitness Q.X.obj.left
      (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)) K,
      sfDomainWitnessExchange D C E n hn Q c K W =
        sfDomainWitnessExchange D C E n hn Q c K W' := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let Λ := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
  have h (V : FixedEtaleOriginWitness Q.X.obj.left Λ K) :
      sfDomainWitnessExchange D C E n hn Q c K V =
        (ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} Λ) Q.square c).app K.obj :=
    (ProEtale.compactSupport_exchange_transport Λ Q.square c).2 V.complex K.obj V.iso
  refine ⟨?_, fun V ↦ (h W).trans (h V).symm⟩
  rw [h W]
  exact ProEtale.isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_app
    Λ Q.square c K.obj ⟨W.complex.obj, W.complex.property, ⟨W.iso⟩⟩

/-- The witness conjugate is the actual specified pro-etale compact-support map.
Source: clause (4), agreement with the compact-support theorem map
(blueprint: lem-sf-bc-compact-support-domain).
Proof: expand both maps as the proper mate on j_! followed by Rp'_*(beta).
Canonical proper site comparison intertwines the first factor and the normalized open
unit comparison intertwines the second. The resulting source/target square is
compactSupport_exchange_transport. Conjugating it by the retained witness and using
naturality cancels the witness and gives the displayed equality. -/
theorem sfCompactSupportDomain_witness_identification
    [IsSeparated Q.X.obj.hom] [IsSeparated Q.Y.obj.hom]
    [IsSeparated Q.X'.obj.hom] [IsSeparated Q.Y'.obj.hom]
    [IsSeparated Q.g.hom.left] [LocallyOfFiniteType Q.g.hom.left]
    [QuasiCompact Q.g.hom.left]
    [IsSeparated Q.g'.hom.left] [LocallyOfFiniteType Q.g'.hom.left]
    [QuasiCompact Q.g'.hom.left]
    [IsSeparated Q.f'.hom.left] [LocallyOfFiniteType Q.f'.hom.left]
    [QuasiCompact Q.f'.hom.left]
    [IsSeparated Q.f.hom.left] [LocallyOfFiniteType Q.f.hom.left]
    [QuasiCompact Q.f.hom.left]
    (c : Compactification Q.f.hom.left)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Q.X.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))))
    (W : FixedEtaleOriginWitness Q.X.obj.left
      (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)) K) :
    sfDomainWitnessExchange D C E n hn Q c K W =
      (ProEtale.canonicalFiniteCoefficientCompactSupportExchange C.l E n hn
        (sfDomainSquare Q) c).app K.obj := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let Λ := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
  have ht := (ProEtale.compactSupport_exchange_transport Λ Q.square c).2
    W.complex K.obj W.iso
  change sfDomainWitnessExchange D C E n hn Q c K W = _ at ht
  rw [ht]
  simp only [ProEtale.canonicalFiniteCoefficientCompactSupportExchange,
    ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap,
    ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeIso,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, ProEtale.ordinary_open_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Functor.map_comp]
  rfl

end Finite

section Integral
variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (E : Type u) [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] (Q : SixFunctorCompactifiedSquare D)
  [IsSeparated Q.f.hom.left] [LocallyOfFiniteType Q.f.hom.left]
  [QuasiCompact Q.f.hom.left]

/-- Intrinsic completeness of a uniform constructible complete input, in the shared
completed-exchange presentation and for any generating tuple.
Source: clause (4), integral domain (blueprint: lem-sf-bc-compact-support-domain).
Proof: the first defining condition of K supplies intrinsic completeness after the
canonical constant/completed coefficient comparison. Koszul reconstruction is independent
of the generating tuple and of the complex representative; transport its unit through
that comparison. This is exactly cbcCompleteProperty. -/
theorem sfDomainIntegralComplete
    (r : ℕ) (a : Fin r → PbcIntegralRing C.l E)
    (ha : Ideal.span (Set.range a) = (pbcIntegralDatum C.l E).ideal)
    (K : PbcBoundedConstructibleComplete Q.X.obj.left (pbcIntegralDatum C.l E)) :
    cbcCompleteProperty (pbcIntegralDatum C.l E) Q.X.obj.left r a ha K.obj := by
  let _ : IsSeparated Q.f.hom.left := inferInstance
  let _ : LocallyOfFiniteType Q.f.hom.left := inferInstance
  let _ : QuasiCompact Q.f.hom.left := inferInstance
  obtain ⟨s, b, hb, L, eL, hL⟩ := K.property.1
  exact wfComplete_of_presentation Q.X.obj.left (pbcIntegralDatum C.l E) r a ha
    K.obj s b hb L eL hL

/-- The completed composite on the actual lifted valuation ring, with the original
uniform-reduction input retained. The generating tuple only presents its adic ideal.
Source: clause (4), integral paragraph (blueprint: lem-sf-bc-compact-support-domain). -/
def sfDomainIntegralExchange
    (r : ℕ) (a : Fin r → PbcIntegralRing C.l E)
    (ha : Ideal.span (Set.range a) = (pbcIntegralDatum C.l E).ideal)
    (K : PbcBoundedConstructibleComplete Q.X.obj.left (pbcIntegralDatum C.l E)) :=
  completedCompactSupportExchange (pbcIntegralDatum C.l E)
    Q.compactification Q.compactification' Q.h.hom.left
    (sfDomainProperSquare Q) (sfDomainOpenSquare Q) r a ha
    ⟨K.obj, sfDomainIntegralComplete D C E Q r a ha K⟩

/-- The completed proper/open composite is invertible on precisely the uniform
constructible complete domain. Source: clause (4), integral paragraph
(blueprint: lem-sf-bc-compact-support-domain).
Proof:
1. The defining property of K supplies intrinsic completeness, uniform constructible
reductions and compatible etale origins. Exact open extension keeps the finite origins
bounded below and preserves their annihilating ring, by the finite clause.
2. thm-cbc-complete-proetale applies to j_!K, the proper square and the open square.
Its proper arrow is completed proper exchange; its second arrow is Rp'_*(beta).
3. beta is Rlim of the finite open-unit maps followed by the inverse extension/Rlim
comparison. Thus this is exactly the specified completed exchange, not ordinary pullback.
4. Each factor is invertible. The theorem's refinement interchange and comparison
cocycle give compactification independence, as stated separately below. -/
theorem sfCompactSupportDomain_integral
    [IsSeparated Q.X.obj.hom] [IsSeparated Q.Y.obj.hom]
    [IsSeparated Q.X'.obj.hom] [IsSeparated Q.Y'.obj.hom]
    [IsSeparated Q.g.hom.left] [LocallyOfFiniteType Q.g.hom.left]
    [QuasiCompact Q.g.hom.left]
    [IsSeparated Q.g'.hom.left] [LocallyOfFiniteType Q.g'.hom.left]
    [QuasiCompact Q.g'.hom.left]
    [IsSeparated Q.f'.hom.left] [LocallyOfFiniteType Q.f'.hom.left]
    [QuasiCompact Q.f'.hom.left]
    (r : ℕ) (a : Fin r → PbcIntegralRing C.l E)
    (ha : Ideal.span (Set.range a) = (pbcIntegralDatum C.l E).ideal)
    (K : PbcBoundedConstructibleComplete Q.X.obj.left (pbcIntegralDatum C.l E)) :
    IsIso (sfDomainIntegralExchange D C E Q r a ha K) := by
  exact (completeCompactSupportProetale_isIso (pbcIntegralDatum C.l E)
    Q.compactification Q.compactification' Q.h.hom.left
    (sfDomainProperSquare Q) (sfDomainOpenSquare Q) r a ha
    ⟨K.obj, sfDomainIntegralComplete D C E Q r a ha K⟩ K.property.2.2).1

/-- Completed exchange is intertwined by the actual proper/open refinement maps.
Source: clause (4), compactification independence
(blueprint: lem-sf-bc-compact-support-domain).
Proof: apply thm-cbc-complete-proetale's refinement-interchange law to K and its
compatible origins. Before derived limit, proper mate-pasting and the open unit
characterization identify both composites. Derived limit and reconstruction cancel
the intermediate comparisons. The canonical comparison cocycle then removes a common
refinement, so this equation also compares arbitrary compactifications. -/
theorem sfCompactSupportDomain_integralRefinement
    [IsSeparated Q.X.obj.hom] [IsSeparated Q.Y.obj.hom]
    [IsSeparated Q.X'.obj.hom] [IsSeparated Q.Y'.obj.hom]
    [IsSeparated Q.g.hom.left] [LocallyOfFiniteType Q.g.hom.left]
    [QuasiCompact Q.g.hom.left]
    [IsSeparated Q.g'.hom.left] [LocallyOfFiniteType Q.g'.hom.left]
    [QuasiCompact Q.g'.hom.left]
    [IsSeparated Q.f'.hom.left] [LocallyOfFiniteType Q.f'.hom.left]
    [QuasiCompact Q.f'.hom.left]
    (c₁ c₂ : Compactification Q.f.hom.left)
    (c₁' c₂' : Compactification Q.f'.hom.left)
    (gb₁ : c₁'.Z ⟶ c₁.Z) (gb₂ : c₂'.Z ⟶ c₂.Z)
    (sp₁ : ChosenCartesianSquare gb₁ c₁'.g c₁.g Q.g.hom.left)
    (sj₁ : OpenImmersionSquare Q.g'.hom.left c₁'.i c₁.i gb₁)
    (sp₂ : ChosenCartesianSquare gb₂ c₂'.g c₂.g Q.g.hom.left)
    (sj₂ : OpenImmersionSquare Q.g'.hom.left c₂'.i c₂.i gb₂)
    (v : c₁.Refinement c₂) (v' : c₁'.Refinement c₂')
    (_hv : v'.hom ≫ gb₂ = gb₁ ≫ v.hom)
    (r : ℕ) (a : Fin r → PbcIntegralRing C.l E)
    (ha : Ideal.span (Set.range a) = (pbcIntegralDatum C.l E).ideal)
    (K : PbcBoundedConstructibleComplete Q.X.obj.left (pbcIntegralDatum C.l E)) :
    ((pbcIntegralDatum C.l E).completedPull Q.g.hom.left).map
        (cbcRefinementMap (pbcIntegralDatum C.l E) v K.obj) ≫
      cbcExchange (pbcIntegralDatum C.l E) c₁ c₁' gb₁ sp₁ sj₁ r a ha
        ⟨K.obj, sfDomainIntegralComplete D C E Q r a ha K⟩ =
    cbcExchange (pbcIntegralDatum C.l E) c₂ c₂' gb₂ sp₂ sj₂ r a ha
        ⟨K.obj, sfDomainIntegralComplete D C E Q r a ha K⟩ ≫
      cbcRefinementMap (pbcIntegralDatum C.l E)
        (qf := cbcBaseChangeQuasiCompact c₁ c₁' gb₁ sj₁) v'
        (((pbcIntegralDatum C.l E).completedPull Q.g'.hom.left).obj K.obj) := by
  exact completeCompactSupportProetale_refinement (pbcIntegralDatum C.l E)
    c₁ c₂ c₁' c₂' gb₁ gb₂ sp₁ sj₁ sp₂ sj₂ v v' _hv r a ha
    ⟨K.obj, sfDomainIntegralComplete D C E Q r a ha K⟩ K.property.2.2

end Integral

/-- Noetherianity of the finite-type geometric corners used by the coefficient theorems.
Source: clause (4), initial geometric setting
(blueprint: lem-sf-bc-compact-support-domain).
Proof: Spec k is Noetherian. The structure morphism of T is locally of finite type
and quasi-compact by SixFunctorSpace. The finite-type-over-Noetherian theorem makes
T locally Noetherian, and quasi-compactness over the affine point makes it compact.
These are exactly the two fields of IsNoetherian; empty schemes are included. -/
@[instance] theorem sfDomainNoetherian (D : FiniteFieldDatum.{u}) (T : SixFunctorSpace D) :
    IsNoetherian T.obj.left := by
  let := T.property.1
  let := T.property.2
  let := LocallyOfFiniteType.isLocallyNoetherian T.obj.hom
  let := QuasiCompact.compactSpace_of_compactSpace T.obj.hom
  exact {}

/-- A natural dimension bound and coefficient-prime invertibility for every corner.
Source: clause (4), geometric hypotheses (blueprint: lem-sf-bc-compact-support-domain).
Proof: a finite-type scheme over a field has finite topological dimension, by
lem-kun-dimension-finite-type; dimension bottom for the empty scheme is bounded by zero.
The characteristic of k is p, since k is the fixed algebraic closure of F_q.
The prime ell differs from p, so is a unit in k. The structure map carries its
inverse to every stalk, as in lem-pur-finite-setting-comparison-hypotheses. -/
theorem sfDomainGeometry (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (T : SixFunctorSpace D) :
    (∃ d : ℕ, topologicalKrullDim T.obj.left ≤ (d : WithBot ℕ∞)) ∧
      ∀ t : T.obj.left, IsUnit (C.l : T.obj.left.presheaf.stalk t) := by
  let := T.property.1
  let := T.property.2
  refine ⟨exists_topologicalKrullDim_le T.obj.hom, ?_⟩
  let P : PurityFiniteSetting := ⟨D, C, ⊥, 1, by decide⟩
  exact P.coefficientPrime_isUnit_stalk T.obj.left T.obj.hom

section Rational
variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (E : Type (u + 1)) [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] (Q : SixFunctorCompactifiedSquare D)
  [IsSeparated Q.f.hom.left] [LocallyOfFiniteType Q.f.hom.left]
  [QuasiCompact Q.f.hom.left]

/-- Raw rational exchange with its integral normalization and lattice independence.
The existential landing witnesses assert uniform bounded constructible outputs before
localization. They are conclusions, not assumptions about the input lattice.
Source: clause (4), rational paragraph (blueprint: lem-sf-bc-compact-support-domain).
Proof:
1. Noetherianity, dimension bounds and invertibility follow from finite-type geometry.
Apply thm-cbc-finite-extension with the actual valuation ring and compactification.
2. Its uniform landing conclusions lift both complete composite functors to the integral
constructible category, without reducing a rational object modulo the uniformizer.
3. Rational transport extends their completed exchange to the raw localization. On an
integral object it is exactly finiteExtensionCompactSupportExchangeComponent.
4. Naturality extends to all fraction morphisms by linearity and localization's tensor
formula. Applying it to a rational isomorphism gives the displayed lattice independence.
5. Localization preserves the integral refinement square, inverses and the comparison
cocycle, so the same map is compactification independent. -/
theorem sfCompactSupportDomain_rational
    [IsSeparated Q.X.obj.hom] [IsSeparated Q.Y.obj.hom]
    [IsSeparated Q.X'.obj.hom] [IsSeparated Q.Y'.obj.hom]
    [IsSeparated Q.g.hom.left] [LocallyOfFiniteType Q.g.hom.left]
    [QuasiCompact Q.g.hom.left]
    [IsSeparated Q.g'.hom.left] [LocallyOfFiniteType Q.g'.hom.left]
    [QuasiCompact Q.g'.hom.left]
    [IsSeparated Q.f'.hom.left] [LocallyOfFiniteType Q.f'.hom.left]
    [QuasiCompact Q.f'.hom.left] :
    ∃ (hSource : ∀ K : PbcBoundedConstructibleComplete Q.X.obj.left
        (pbcPadicCoefficientDatum C.l E),
      PbcIsBoundedConstructibleComplete Q.Y'.obj.left (pbcPadicCoefficientDatum C.l E)
        ((cbcCompactSupportSource Q.g.hom.left Q.compactification
          (pbcPadicCoefficientDatum C.l E)).obj K.obj)),
    ∃ (hTarget : ∀ K : PbcBoundedConstructibleComplete Q.X.obj.left
        (pbcPadicCoefficientDatum C.l E),
      PbcIsBoundedConstructibleComplete Q.Y'.obj.left (pbcPadicCoefficientDatum C.l E)
        ((cbcCompactSupportTarget Q.g'.hom.left Q.compactification'
          (pbcPadicCoefficientDatum C.l E)).obj K.obj)),
    ∃ η : cbcCompactSupportSourceTransport C.l E Q.g.hom.left Q.compactification
        (pbcPadicCoefficientDatum C.l E) hSource ≅
      cbcCompactSupportTargetTransport C.l E Q.g'.hom.left Q.compactification'
        (pbcPadicCoefficientDatum C.l E) hTarget,
    (∀ (K : PbcBoundedConstructibleComplete Q.X.obj.left (pbcPadicCoefficientDatum C.l E))
      (r : ℕ) (a : Fin r → Padic.coefficientExtensionIntegers C.l E)
      (ha : Ideal.span (Set.range a) = (pbcPadicCoefficientDatum C.l E).ideal)
      (hc : cbcCompleteProperty (pbcPadicCoefficientDatum C.l E) Q.X.obj.left r a ha K.obj),
      η.hom.app ⟨K⟩ = finiteExtensionCompactSupportExchangeComponent C.l E
        Q.compactification Q.compactification' Q.h.hom.left
        (sfDomainProperSquare Q) (sfDomainOpenSquare Q) r a ha hSource hTarget K hc) ∧
    (∀ (K L M : PbcRationalCategory Q.X.obj.left (pbcPadicCoefficientDatum C.l E)
        (Padic.coefficientExtensionUniformizer C.l E)) (α : L ≅ K) (β : M ≅ K),
      (cbcCompactSupportSourceTransport C.l E Q.g.hom.left Q.compactification
          (pbcPadicCoefficientDatum C.l E) hSource).map α.inv ≫
        η.hom.app L ≫
        (cbcCompactSupportTargetTransport C.l E Q.g'.hom.left Q.compactification'
          (pbcPadicCoefficientDatum C.l E) hTarget).map α.hom =
      (cbcCompactSupportSourceTransport C.l E Q.g.hom.left Q.compactification
          (pbcPadicCoefficientDatum C.l E) hSource).map β.inv ≫
        η.hom.app M ≫
        (cbcCompactSupportTargetTransport C.l E Q.g'.hom.left Q.compactification'
          (pbcPadicCoefficientDatum C.l E) hTarget).map β.hom) := by
  obtain ⟨hs, ht, η, hη⟩ := finiteExtension_compactSupportBaseChange C.l E
    Q.compactification Q.compactification' Q.h.hom.left
    (sfDomainProperSquare Q) (sfDomainOpenSquare Q)
    (sfDomainGeometry D C Q.X).1 (sfDomainGeometry D C Q.Y).1
    (sfDomainGeometry D C Q.X').1 (sfDomainGeometry D C Q.Y').1
    (sfDomainGeometry D C Q.X).2 (sfDomainGeometry D C Q.Y).2
    (sfDomainGeometry D C Q.X').2 (sfDomainGeometry D C Q.Y').2
  refine ⟨hs, ht, η, hη, ?_⟩
  intro K L M α β
  have hα := η.hom.naturality α.hom
  have hβ := η.hom.naturality β.hom
  simp only [← Category.assoc, ← hα, ← hβ, ← Functor.map_comp,
    Iso.inv_hom_id]

/-- Raw rationalization preserves the actual completed refinement equation.
Landing witnesses are precisely what is needed to interpret its two endpoints
in the bounded constructible category; no rational reduction is used.
Source: clause (4), rational compactification independence
(blueprint: lem-sf-bc-compact-support-domain).
Proof: the integral refinement-interchange clause identifies the two ambient paths.
The full subcategory inclusion is faithful, so this is the same equality there.
Apply raw rationalization, which preserves identities, composition and the inverse
comparison maps. This proves the rational refinement square. Common refinements and
the integral comparison cocycle then give independence of compactification. -/
theorem sfCompactSupportDomain_rationalRefinement
    [IsSeparated Q.X.obj.hom] [IsSeparated Q.Y.obj.hom]
    [IsSeparated Q.X'.obj.hom] [IsSeparated Q.Y'.obj.hom]
    [IsSeparated Q.g.hom.left] [LocallyOfFiniteType Q.g.hom.left]
    [QuasiCompact Q.g.hom.left]
    [IsSeparated Q.g'.hom.left] [LocallyOfFiniteType Q.g'.hom.left]
    [QuasiCompact Q.g'.hom.left]
    [IsSeparated Q.f'.hom.left] [LocallyOfFiniteType Q.f'.hom.left]
    [QuasiCompact Q.f'.hom.left]
    (c₁ c₂ : Compactification Q.f.hom.left)
    (c₁' c₂' : Compactification Q.f'.hom.left)
    (gb₁ : c₁'.Z ⟶ c₁.Z) (gb₂ : c₂'.Z ⟶ c₂.Z)
    (sp₁ : ChosenCartesianSquare gb₁ c₁'.g c₁.g Q.g.hom.left)
    (sj₁ : OpenImmersionSquare Q.g'.hom.left c₁'.i c₁.i gb₁)
    (sp₂ : ChosenCartesianSquare gb₂ c₂'.g c₂.g Q.g.hom.left)
    (sj₂ : OpenImmersionSquare Q.g'.hom.left c₂'.i c₂.i gb₂)
    (v : c₁.Refinement c₂) (v' : c₁'.Refinement c₂')
    (_hv : v'.hom ≫ gb₂ = gb₁ ≫ v.hom)
    (r : ℕ) (a : Fin r → Padic.coefficientExtensionIntegers C.l E)
    (ha : Ideal.span (Set.range a) = (pbcPadicCoefficientDatum C.l E).ideal)
    (K : PbcBoundedConstructibleComplete Q.X.obj.left (pbcPadicCoefficientDatum C.l E))
    (hc : cbcCompleteProperty (pbcPadicCoefficientDatum C.l E) Q.X.obj.left r a ha K.obj)
    (hs : PbcIsBoundedConstructibleComplete Q.Y'.obj.left (pbcPadicCoefficientDatum C.l E)
      ((cbcCompactSupportSource Q.g.hom.left c₂ (pbcPadicCoefficientDatum C.l E)).obj K.obj))
    (ht : PbcIsBoundedConstructibleComplete Q.Y'.obj.left (pbcPadicCoefficientDatum C.l E)
      ((cbcCompactSupportTarget Q.g'.hom.left c₁'
        (pbcPadicCoefficientDatum C.l E)).obj K.obj)) :
    finiteExtensionRationalArrow C.l E hs ht
      (((pbcPadicCoefficientDatum C.l E).completedPull Q.g.hom.left).map
          (cbcRefinementMap (pbcPadicCoefficientDatum C.l E) v K.obj) ≫
        cbcExchange (pbcPadicCoefficientDatum C.l E) c₁ c₁' gb₁ sp₁ sj₁ r a ha ⟨K.obj, hc⟩) =
    finiteExtensionRationalArrow C.l E hs ht
      (cbcExchange (pbcPadicCoefficientDatum C.l E) c₂ c₂' gb₂ sp₂ sj₂ r a ha ⟨K.obj, hc⟩ ≫
        cbcRefinementMap (pbcPadicCoefficientDatum C.l E)
          (qf := cbcBaseChangeQuasiCompact c₁ c₁' gb₁ sj₁) v'
          (((pbcPadicCoefficientDatum C.l E).completedPull Q.g'.hom.left).obj K.obj)) := by
  apply congrArg (finiteExtensionRationalArrow C.l E hs ht)
  exact completeCompactSupportProetale_refinement (pbcPadicCoefficientDatum C.l E)
    c₁ c₂ c₁' c₂' gb₁ gb₂ sp₁ sj₁ sp₂ sj₂ v v' _hv r a ha
    ⟨K.obj, hc⟩ K.property.2.2

end Rational

/-- Typeclass packaging of the geometric dimension conclusion; this introduces no
extra assumption on the coefficient-domain theorem.
Source: clause (4), finite-type corners (blueprint: lem-sf-bc-compact-support-domain).
Proof: a finite-type scheme over a field has finite dimension. Package the natural
bound supplied by lem-kun-dimension-finite-type in Fact, allowing the empty scheme. -/
theorem sfDomainDimension (D : FiniteFieldDatum.{u}) (T : SixFunctorSpace D) :
    Fact (∃ d : ℕ, topologicalKrullDim T.obj.left ≤ (d : WithBot ℕ∞)) := by
  let := T.property.1
  let := T.property.2
  exact ⟨exists_topologicalKrullDim_le T.obj.hom⟩

/-- Typeclass packaging of invertibility on the geometric corners.
Source: clause (4), ell distinct from p (blueprint: lem-sf-bc-compact-support-domain).
Proof: sfDomainGeometry gives the inverse at every stalk from the structure map
and ell distinct from the characteristic. Package that conclusion in Fact. -/
theorem sfDomainInvertible (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (T : SixFunctorSpace D) : Fact (∀ t : T.obj.left, IsUnit (C.l : T.obj.left.presheaf.stalk t)) :=
  by
  exact ⟨(sfDomainGeometry D C T).2⟩

/-- The existing common-stage scalar system with the finite-type corner hypotheses
filled by their geometric consequences. No new coefficient category is defined.
Source: clause (4), common-stage paragraph
(blueprint: lem-sf-bc-compact-support-domain). -/
abbrev sfDomainScalarSystem (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (T : SixFunctorSpace D) :=
  pbcScalarSystem C.l C.Qbar T.obj.left
    (sfDomainDimension D T).out (sfDomainInvertible D C T).out

/-- The published common-stage model, retaining normalization on every integral
representative, including the identity coefficient extension.
Source: clause (4), common-stage paragraph
(blueprint: lem-sf-bc-compact-support-domain). -/
abbrev sfDomainQbarModel (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (Q : SixFunctorCompactifiedSquare D) [QuasiCompact Q.f.hom.left] :=
  CbcQbarExchangeModel C.l C.Qbar
    (dX := sfDomainDimension D Q.X)
    (iX := sfDomainInvertible D C Q.X)
    (dY' := sfDomainDimension D Q.Y')
    (iY' := sfDomainInvertible D C Q.Y')
    Q.compactification Q.compactification' Q.h.hom.left
    (sfDomainProperSquare Q) (sfDomainOpenSquare Q)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- The stage formulas compare categories, without unfolding their derived models.
attribute [local irreducible] AlgebraicGeometry.Scheme.pbcIntegralDatum
attribute [local irreducible] AlgebraicGeometry.Scheme.pbcScalarExtension
  AlgebraicGeometry.Scheme.pbcScalarAssociator
  CategoryTheory.StageSystem.Morphism.descNatTrans ScalarLocalization.composition
  SheafOfModules.instAbelian SheafOfModules.instCategory
  instCategoryDerivedCategory DerivedCategory.instPreadditive
  ScalarLocalization.category

/-- The specified exchange descends to the actual common-stage category and has the
finite-overfield representative shown below. The model retains all uniform landing
witnesses. Equal fields, further overfields and changes of representing pair are included.
Source: clause (4), algebraically closed coefficients
(blueprint: lem-sf-bc-compact-support-domain).
Proof:
1. Apply thm-cbc-qbar using the Noetherianity, finite dimensions and invertible prime
of the geometric corners. It constructs its normalized coherent model, whose source
and target land in the uniform bounded constructible domains at every finite field.
2. At each field its component is the raw rationalization of the completed exchange
by the model's normalized equation. The rational clause supplies its inverse.
3. Include this inverse in the common-stage category; the common-stage identity and
composition equations prove both inverse laws. Hence descent gives an isomorphism.
4. The coherent Hom equation rewrites a component after E ≤ M by source beta,
the M-component and inverse target beta. This is exactly the mkHom formula below.
The scalar identity and associator laws include M=E and make further extension harmless.
For two nonnested finite overfields pass to a finite compositum.
5. Represent any isomorphism between two presentations at a common finite field.
Finite-stage naturality identifies the two paths there. Descending that equality
proves representative and lattice independence. Apply the same procedure to the
rational refinement square to obtain compactification independence. -/
def sfDomainQbarConclusion
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (Q : SixFunctorCompactifiedSquare D)
    [IsSeparated Q.f.hom.left] [LocallyOfFiniteType Q.f.hom.left]
    [QuasiCompact Q.f.hom.left] : Prop :=
  letI := sfDomainDimension D Q.X
  letI := sfDomainInvertible D C Q.X
  letI := sfDomainDimension D Q.Y'
  letI := sfDomainInvertible D C Q.Y'
  Nonempty (sfDomainQbarModel D C Q) ∧
  ∀ B : sfDomainQbarModel D C Q,
    (∀ (E : Padic.FiniteCoefficientFields C.l C.Qbar)
      (K : pbcStageCategory C.l C.Qbar Q.X.obj.left E),
      IsIso ((B.exchange.τ E).app K)) ∧
    IsIso (StageSystem.Morphism.descNatTrans B.exchange) ∧
    (∀ (K : (sfDomainScalarSystem D C Q.X).PairCategory)
      (M : Padic.FiniteCoefficientFields C.l C.Qbar) (h : K.stage ≤ M),
      (StageSystem.Morphism.descNatTrans B.exchange).app K =
        StageSystem.PairCategory.mkHom
          (X := B.U.base.functor.obj K) (Y := B.V.base.functor.obj K) M h h
          ((B.U.base.β h).hom.app K.obj ≫
            (B.exchange.τ M).app (((sfDomainScalarSystem D C Q.X).T h).obj K.obj) ≫
            (B.V.base.β h).inv.app K.obj)) ∧
    (∀ (K A B' : (sfDomainScalarSystem D C Q.X).PairCategory) (α : A ≅ K) (β : B' ≅ K),
      B.U.base.functor.map α.inv ≫
          (StageSystem.Morphism.descNatTrans B.exchange).app A ≫
          B.V.base.functor.map α.hom =
        B.U.base.functor.map β.inv ≫
          (StageSystem.Morphism.descNatTrans B.exchange).app B' ≫
          B.V.base.functor.map β.hom)

/-- Common-stage compact-support exchange on the stated geometric and coefficient domains.
Source: clause (4) (blueprint: lem-sf-bc-compact-support-domain).
Proof: apply thm-cbc-qbar after filling the geometric hypotheses by sfDomainGeometry.
The normalized finite components are the rationalizations of completed exchange.
Their inverses descend, the scalar Hom equation gives every finite-overfield formula,
and finite-stage naturality gives independence of the representative and lattice.
The common-stage calculus descends the rational refinement equation as well. -/
theorem sfCompactSupportDomain_qbar
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (Q : SixFunctorCompactifiedSquare D)
    [IsSeparated Q.X.obj.hom] [IsSeparated Q.Y.obj.hom]
    [IsSeparated Q.X'.obj.hom] [IsSeparated Q.Y'.obj.hom]
    [IsSeparated Q.g.hom.left] [LocallyOfFiniteType Q.g.hom.left]
    [QuasiCompact Q.g.hom.left]
    [IsSeparated Q.g'.hom.left] [LocallyOfFiniteType Q.g'.hom.left]
    [QuasiCompact Q.g'.hom.left]
    [IsSeparated Q.f'.hom.left] [LocallyOfFiniteType Q.f'.hom.left]
    [QuasiCompact Q.f'.hom.left]
    [IsSeparated Q.f.hom.left] [LocallyOfFiniteType Q.f.hom.left]
    [QuasiCompact Q.f.hom.left] : sfDomainQbarConclusion D C Q := by
  let := sfDomainDimension D Q.X
  let := sfDomainInvertible D C Q.X
  let := sfDomainDimension D Q.Y'
  let := sfDomainInvertible D C Q.Y'
  obtain ⟨h, hh⟩ := qbarCompactSupportBaseChange C.l C.Qbar
    Q.compactification Q.compactification' Q.h.hom.left
    (sfDomainProperSquare Q) (sfDomainOpenSquare Q)
    (sfDomainGeometry D C Q.Y).1 (sfDomainGeometry D C Q.X').1
    (sfDomainGeometry D C Q.Y).2 (sfDomainGeometry D C Q.X').2
  refine ⟨h, ?_⟩
  intro B
  exact ⟨(hh B).1, (hh B).2.1, (hh B).2.2.2.1, (hh B).2.2.2.2⟩

/-- Compactification independence in common-stage coordinates, with both comparison
arrows normalized on integral lattices. The comparison data are fixed by those
normalizations, rather than arbitrary isomorphisms of the endpoints.
Source: clause (4), final compactification-independence paragraph
(blueprint: lem-sf-bc-compact-support-domain). -/
def sfDomainQbarRefinementConclusion
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (Q : SixFunctorCompactifiedSquare D) [QuasiCompact Q.f.hom.left]
    (c₁ c₂ : Compactification Q.f.hom.left)
    (c₁' c₂' : Compactification Q.f'.hom.left)
    (gb₁ : c₁'.Z ⟶ c₁.Z) (gb₂ : c₂'.Z ⟶ c₂.Z)
    (sp₁ : ChosenCartesianSquare gb₁ c₁'.g c₁.g Q.g.hom.left)
    (sj₁ : OpenImmersionSquare Q.g'.hom.left c₁'.i c₁.i gb₁)
    (sp₂ : ChosenCartesianSquare gb₂ c₂'.g c₂.g Q.g.hom.left)
    (sj₂ : OpenImmersionSquare Q.g'.hom.left c₂'.i c₂.i gb₂)
    (v : c₁.Refinement c₂) (v' : c₁'.Refinement c₂') : Prop :=
  letI := sfDomainDimension D Q.X
  letI := sfDomainInvertible D C Q.X
  letI := sfDomainDimension D Q.Y'
  letI := sfDomainInvertible D C Q.Y'
  ∀ (B₁ : CbcQbarExchangeModel C.l C.Qbar c₁ c₁' gb₁ sp₁ sj₁)
    (B₂ : CbcQbarExchangeModel C.l C.Qbar c₂ c₂' gb₂ sp₂ sj₂),
    ∃ (α : StageSystem.Morphism.Hom B₂.U.base B₁.U.base)
      (β : StageSystem.Morphism.Hom B₂.V.base B₁.V.base),
      (∀ (E : Padic.FiniteCoefficientFields C.l C.Qbar)
        (K : pbcIntegralStage C.l C.Qbar Q.X.obj.left E),
        HEq ((α.τ E).app ((pbcStageLocalization C.l C.Qbar Q.X.obj.left E).obj K))
          ((pbcStageLocalization C.l C.Qbar Q.Y'.obj.left E).map
            (ObjectProperty.homMk
              (X := ⟨_, B₂.presSource E K⟩) (Y := ⟨_, B₁.presSource E K⟩)
              (((pbcStageDatum.{u} C.l C.Qbar E).completedPull Q.g.hom.left).map
                (cbcRefinementMap (pbcStageDatum.{u} C.l C.Qbar E) v K.obj))))) ∧
      (∀ (E : Padic.FiniteCoefficientFields C.l C.Qbar)
        (K : pbcIntegralStage C.l C.Qbar Q.X.obj.left E),
        HEq ((β.τ E).app ((pbcStageLocalization C.l C.Qbar Q.X.obj.left E).obj K))
          ((pbcStageLocalization C.l C.Qbar Q.Y'.obj.left E).map
            (ObjectProperty.homMk
              (X := ⟨_, B₂.presTarget E K⟩) (Y := ⟨_, B₁.presTarget E K⟩)
              (cbcRefinementMap (pbcStageDatum.{u} C.l C.Qbar E)
                (qf := cbcBaseChangeQuasiCompact c₁ c₁' gb₁ sj₁) v'
                (((pbcStageDatum.{u} C.l C.Qbar E).completedPull
                  Q.g'.hom.left).obj K.obj))))) ∧
      IsIso (StageSystem.Morphism.descNatTrans α) ∧
      IsIso (StageSystem.Morphism.descNatTrans β) ∧
      StageSystem.Morphism.descNatTrans α ≫
          StageSystem.Morphism.descNatTrans B₁.exchange =
        StageSystem.Morphism.descNatTrans B₂.exchange ≫
          StageSystem.Morphism.descNatTrans β

/-- Common-stage exchange agrees under the specified compactification comparisons.
Source: clause (4), final paragraph (blueprint: lem-sf-bc-compact-support-domain).
Proof: take the completed refinement square of the integral clause at every finite
coefficient field. Both source and target composites have the uniform landing witnesses
retained by the models. Raw localization therefore defines the comparison components
shown in sfDomainQbarRefinementConclusion, with their inverses. Normalized scalar
comparison and its cocycle make them coherent Hom families. Rational transport sends
the integral commuting square to the rational commuting square. Descent of these
compatible transformations preserves this equation and both inverse equations.
Common dominating refinements and the integral cocycle remove the chosen refinement. -/
theorem sfCompactSupportDomain_qbarRefinement
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (Q : SixFunctorCompactifiedSquare D)
    [IsSeparated Q.X.obj.hom] [IsSeparated Q.Y.obj.hom]
    [IsSeparated Q.X'.obj.hom] [IsSeparated Q.Y'.obj.hom]
    [IsSeparated Q.g.hom.left] [LocallyOfFiniteType Q.g.hom.left]
    [QuasiCompact Q.g.hom.left]
    [IsSeparated Q.g'.hom.left] [LocallyOfFiniteType Q.g'.hom.left]
    [QuasiCompact Q.g'.hom.left]
    [IsSeparated Q.f'.hom.left] [LocallyOfFiniteType Q.f'.hom.left]
    [QuasiCompact Q.f'.hom.left]
    [IsSeparated Q.f.hom.left] [LocallyOfFiniteType Q.f.hom.left]
    [QuasiCompact Q.f.hom.left]
    (c₁ c₂ : Compactification Q.f.hom.left)
    (c₁' c₂' : Compactification Q.f'.hom.left)
    (gb₁ : c₁'.Z ⟶ c₁.Z) (gb₂ : c₂'.Z ⟶ c₂.Z)
    (sp₁ : ChosenCartesianSquare gb₁ c₁'.g c₁.g Q.g.hom.left)
    (sj₁ : OpenImmersionSquare Q.g'.hom.left c₁'.i c₁.i gb₁)
    (sp₂ : ChosenCartesianSquare gb₂ c₂'.g c₂.g Q.g.hom.left)
    (sj₂ : OpenImmersionSquare Q.g'.hom.left c₂'.i c₂.i gb₂)
    (v : c₁.Refinement c₂) (v' : c₁'.Refinement c₂')
    (_hv : v'.hom ≫ gb₂ = gb₁ ≫ v.hom) :
    sfDomainQbarRefinementConclusion D C Q c₁ c₂ c₁' c₂' gb₁ gb₂ sp₁ sj₁ sp₂ sj₂ v v' := by
  sorry

end WeilConjectures
