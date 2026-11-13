/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalTowerCoefficients
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTowerTraceLimit

import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystem
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimit
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1CompletedLimitBridge
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Generator.Basic

/-!
# The `ℓ`-adic cycle class of the diagonal

Let `q : ℙ¹_Y ⟶ Y` be the projection, `Δ` the diagonal of `ℙ¹_Y ×_Y ℙ¹_Y` and `p₁, p₂` its
projections. We show that there are a class `δ : Δ_* Λ ⟶ Λ(1)[2]` and a trace
`Tr_q : Rq_* Λ(1)[2] ⟶ Λ` with `Tr_{p_i} ∘ Rp_{i*}(δ) = 1`, for `Λ = 𝒪_E, E, ℚ̄_ℓ`, all obtained
from one class with `ℤ_ℓ`-coefficients, reducing to the torsion cycle classes and traces, and
compatible with base change.

All these data are the members of a `AlgebraicGeometry.ProEtale.DiagonalCoefficients.Family`.
The family built from the canonical whole-system limit of the Cartier–Kummer classes is singled
out by `AlgebraicGeometry.ProEtale.DiagonalCoefficients.Family.IsCanonical`.

## Main statements

- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.exists_family_isCanonical`: the canonical
  family exists.
- The clause lemmas `Family.IsCanonical.integral_delta_reduction`, ...,
  `Family.IsCanonical.trace_pullback`: the properties of the canonical family.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-! ### Splitting the finite comparisons into the class and the trace -/

/-- The class part of `FiniteDiagonalComparison`: the realization of the diagonal class of `d`
with finite coefficients `A` is the canonical Cartier cycle class `finiteCartierArrow`. -/
def FiniteDiagonalClassComparison
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (A : Type (u + 1)) [CommRing A] [hfinite : Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (Y : Scheme.{u}) [IsNoetherian Y]
    (hW : IsUnit (N : Γ(diagonalSurface Y, ⊤)))
    (L : ∀ X : Scheme.{u}, Modules R X) (d : Diagram R Y L)
    (eP : FiniteRealization R A (ProjectiveLine Y))
    (eW : FiniteRealization R A (diagonalSurface Y))
    (lineW : eW.F.obj (L (diagonalSurface Y)) ≅ geoCartierLine A N hA (diagonalSurface Y)) :
    Prop :=
  ∃ sourceIso : eW.F.obj (source R Y) ≅
    (lowerStar (ModuleCat.{u + 1} A) (diagonalImmersion Y)).obj
      (geoCartierConstant A (ProjectiveLine Y)),
  HEq (eW.underlying.inv.app (source R Y) ≫
      (sheafCompose (Scheme.ProEt.topology (diagonalSurface Y))
        (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).map sourceIso.hom)
    ((lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
      (eP.underlying.inv.app (Mod.regular (condensedRingObj R (ProjectiveLine Y))) ≫
        (sheafCompose (Scheme.ProEt.topology (ProjectiveLine Y))
          (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).map eP.unitIso.hom)) ∧
  (DerivedCategory.singleFunctor
      (Sheaf (Scheme.ProEt.topology (diagonalSurface Y)) (ModuleCat.{u + 1} A)) 0).map
        sourceIso.inv ≫
      SpTowerClasses.mapSingleArrow eW.F (X := source R Y)
        (Y := L (diagonalSurface Y)) (2 : ℤ) d.delta ≫
        ((DerivedCategory.singleFunctor
          (Sheaf (Scheme.ProEt.topology (diagonalSurface Y)) (ModuleCat.{u + 1} A)) 0).map
            lineW.hom)⟦(2 : ℤ)⟧' =
    finiteCartierArrow A N hN hA Y hW

/-- The trace part of `FiniteDiagonalComparison`: the realization of the trace of `d` with
finite coefficients `A` is the projective-line trace `geoP1Trace`, the projection to the
constant summand of the decomposition `geoP1TwistedMap` of `Rq_* A(1)[2]`. -/
def FiniteDiagonalTraceComparison
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (A : Type (u + 1)) [CommRing A] [hfinite : Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (Y : Scheme.{u}) [IsNoetherian Y]
    (hY : IsUnit (N : Γ(Y, ⊤)))
    (L : ∀ X : Scheme.{u}, Modules R X) (d : Diagram R Y L)
    (eY : FiniteRealization R A Y) (eP : FiniteRealization R A (ProjectiveLine Y))
    (lineP : eP.F.obj (L (ProjectiveLine Y)) ≅ geoCartierLine A N hA (ProjectiveLine Y)) :
    Prop :=
  ∃ (Rq : DiagonalRightDerived (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y)))
    (q_canonical : Rq.R = geoP1Pushforward A (ProjectiveLine Y ↘ Y)),
  IsCanonicalRightDerived (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y))
    Rq q_canonical ∧
  ∃ (q_square : FinitePushSquare R A (ProjectiveLine Y ↘ Y) eP eY d.Rq Rq)
    (splitting : (geoP1Twist A N hA Y 1 2 ⊞ geoP1Unit A Y) ≅
      (geoP1Pushforward A (ProjectiveLine Y ↘ Y)).obj
        (geoP1Twist A N hA (ProjectiveLine Y) 1 2)),
  splitting.hom = geoP1TwistedMap A N hN hA Y hY ∧
  eY.F.mapDerivedCategory.map d.traceq ≫ eY.derivedUnit =
    q_square.derived.iso.hom.app _ ≫
      Rq.R.map (eP.shiftedLine N hA (L (ProjectiveLine Y)) lineP) ≫
        (eqToIso q_canonical).hom.app _ ≫ geoP1Trace A N hA Y splitting

theorem FiniteDiagonalComparison.classComparison
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {N : ℕ} {hN : 0 < N} {hA : (N : A) = 0} {Y : Scheme.{u}} [IsNoetherian Y]
    {hY : IsUnit (N : Γ(Y, ⊤))} {hW : IsUnit (N : Γ(diagonalSurface Y, ⊤))}
    {L : ∀ X : Scheme.{u}, Modules R X} {d : Diagram R Y L}
    {eY : FiniteRealization R A Y} {eP : FiniteRealization R A (ProjectiveLine Y)}
    {eW : FiniteRealization R A (diagonalSurface Y)}
    {lineP : eP.F.obj (L (ProjectiveLine Y)) ≅ geoCartierLine A N hA (ProjectiveLine Y)}
    {lineW : eW.F.obj (L (diagonalSurface Y)) ≅ geoCartierLine A N hA (diagonalSurface Y)}
    (h : FiniteDiagonalComparison R A N hN hA Y hY hW L d eY eP eW lineP lineW) :
    FiniteDiagonalClassComparison R A N hN hA Y hW L d eP eW lineW := by
  obtain ⟨s, h₁, h₂, -⟩ := h
  exact ⟨s, h₁, h₂⟩

theorem FiniteDiagonalComparison.traceComparison
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {N : ℕ} {hN : 0 < N} {hA : (N : A) = 0} {Y : Scheme.{u}} [IsNoetherian Y]
    {hY : IsUnit (N : Γ(Y, ⊤))} {hW : IsUnit (N : Γ(diagonalSurface Y, ⊤))}
    {L : ∀ X : Scheme.{u}, Modules R X} {d : Diagram R Y L}
    {eY : FiniteRealization R A Y} {eP : FiniteRealization R A (ProjectiveLine Y)}
    {eW : FiniteRealization R A (diagonalSurface Y)}
    {lineP : eP.F.obj (L (ProjectiveLine Y)) ≅ geoCartierLine A N hA (ProjectiveLine Y)}
    {lineW : eW.F.obj (L (diagonalSurface Y)) ≅ geoCartierLine A N hA (diagonalSurface Y)}
    (h : FiniteDiagonalComparison R A N hN hA Y hY hW L d eY eP eW lineP lineW) :
    FiniteDiagonalTraceComparison R A N hN hA Y hY L d eY eP lineP := by
  obtain ⟨-, -, -, h₃⟩ := h
  exact h₃

variable (l : ℕ) [Fact l.Prime]

/-- The class part of `QuotientCompatibility`: the diagonal class of a uniformizer reduction
`d` of the `𝒪_E`-coefficient diagram is the torsion Cartier cycle class. -/
def QuotientClassCompatibility (Y : Scheme.{u}) [IsNoetherian Y]
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ)
    (d : Diagram (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      Y (quotientLine l E π n)) : Prop :=
  ∃ (hfinite : Finite (ULift.{u + 1} (completedResidue l E π n))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : ULift.{u + 1} (completedResidue l E π n)) = 0)
    (hW : IsUnit ((l ^ (r + 1) : ℕ) : Γ(diagonalSurface Y, ⊤)))
    (eP : FiniteRealization (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      (ULift.{u + 1} (completedResidue l E π n)) (ProjectiveLine Y))
    (eW : FiniteRealization (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      (ULift.{u + 1} (completedResidue l E π n)) (diagonalSurface Y))
    (lineW : QuotientLineRealization l E π n r hA (diagonalSurface Y) eW),
    FiniteDiagonalClassComparison
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      (ULift.{u + 1} (completedResidue l E π n))
      (hfinite := hfinite) (l ^ (r + 1)) (pow_pos (Fact.out : l.Prime).pos _) hA Y hW
      (quotientLine l E π n) d eP eW (lineW.iso l)

/-- The trace part of `QuotientCompatibility`: the trace of a uniformizer reduction `d` of the
`𝒪_E`-coefficient diagram is the torsion projective-line trace. -/
def QuotientTraceCompatibility (Y : Scheme.{u}) [IsNoetherian Y]
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ)
    (d : Diagram (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      Y (quotientLine l E π n)) : Prop :=
  ∃ (hfinite : Finite (ULift.{u + 1} (completedResidue l E π n))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : ULift.{u + 1} (completedResidue l E π n)) = 0)
    (hY : IsUnit ((l ^ (r + 1) : ℕ) : Γ(Y, ⊤)))
    (eY : FiniteRealization (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      (ULift.{u + 1} (completedResidue l E π n)) Y)
    (eP : FiniteRealization (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      (ULift.{u + 1} (completedResidue l E π n)) (ProjectiveLine Y))
    (lineP : QuotientLineRealization l E π n r hA (ProjectiveLine Y) eP),
    FiniteDiagonalTraceComparison
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      (ULift.{u + 1} (completedResidue l E π n))
      (hfinite := hfinite) (l ^ (r + 1)) (pow_pos (Fact.out : l.Prime).pos _) hA Y hY
      (quotientLine l E π n) d eY eP (lineP.iso l)

theorem QuotientCompatibility.classCompatibility {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
    [IsNoetherian Y] {E : PadicAlgCl.FiniteIntermediateField l} {π : PadicAlgCl.integers l E}
    {n : ℕ} {d : Diagram (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      Y (quotientLine l E π n)}
    (h : QuotientCompatibility l Y E π n d) : QuotientClassCompatibility l Y E π n d := by
  obtain ⟨hfinite, r, hA, _, hW, _, eP, eW, _, lineW, hc⟩ := h
  exact ⟨hfinite, r, hA, hW, eP, eW, lineW, FiniteDiagonalComparison.classComparison hc⟩

theorem QuotientCompatibility.traceCompatibility {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
    [IsNoetherian Y] {E : PadicAlgCl.FiniteIntermediateField l} {π : PadicAlgCl.integers l E}
    {n : ℕ} {d : Diagram (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      Y (quotientLine l E π n)}
    (h : QuotientCompatibility l Y E π n d) : QuotientTraceCompatibility l Y E π n d := by
  obtain ⟨hfinite, r, hA, hY, _, eY, eP, _, lineP, _, hc⟩ := h
  exact ⟨hfinite, r, hA, hY, eY, eP, lineP, FiniteDiagonalComparison.traceComparison hc⟩

/-! ### The canonical family -/

/-- The coefficient family is the canonical one: its `ℤ_ℓ`-member is the derived limit `δ` of
the whole Cartier–Kummer system of the diagonal together with the completed traces
(`Reference`), and every uniformizer reduction of every `𝒪_E`-member is the torsion cycle class
and trace (`FiniteReductions`). -/
def Family.IsCanonical (Y : Scheme.{u}) [IsNoetherian Y] (family : Family l Y) : Prop :=
  ∃ (hY : IsUnit (l : Γ(Y, ⊤))) (aY : DiagonalTraceLocalizations l Y)
    (aP : DiagonalTraceLocalizations l (ProjectiveLine Y))
    (aW : DiagonalTraceLocalizations l (diagonalSurface Y)),
    let := aY
    let := aP
    let := aW
    ∃ D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)),
      DiagonalCompletionSpec l (diagonalSurface Y) D ∧ DiagonalCycleSystemSpec l Y hY D ∧
      ∃ δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y,
        DiagonalTrace.IsDiagonalLimit l Y hY D δ ∧ Nonempty (Reference l Y δ family) ∧
          FiniteReductions l Y family

private theorem towerGrothendieck (A : Type*) [Category A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] :
    IsGrothendieckAbelian.{u + 1} (ℕᵒᵖ ⥤ A) := by
  let G := separator A
  have hG := isSeparator_separator A
  have hS : ObjectProperty.IsSeparating
      (.ofObj fun j : ℕᵒᵖ ↦ (evaluationLeftAdjoint A j).obj G) := by
    intro F F' f g hfg
    apply NatTrans.ext
    funext j
    apply hG.def
    intro a
    let adj := evaluationAdjunctionRight A j
    apply (adj.homEquiv G F').symm.injective
    have h := hfg _ (ObjectProperty.ofObj_apply _ j) ((adj.homEquiv G F).symm a)
    exact (adj.homEquiv_naturality_right_symm a f).trans
      (h.trans (adj.homEquiv_naturality_right_symm a g).symm)
  have : HasSeparator (ℕᵒᵖ ⥤ A) := ⟨_, hS.isSeparator_coproduct⟩
  have : HasFilteredColimitsOfSize.{u + 1, u + 1} (ℕᵒᵖ ⥤ A) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : AB5OfSize.{u + 1, u + 1} (ℕᵒᵖ ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
  exact { locallySmall := ⟨fun P Q ↦ small_of_injective
    (f := fun f : P ⟶ Q ↦ f.app) (fun f g h ↦ NatTrans.ext h)⟩ }

@[irreducible] private def localizations (X : Scheme.{u}) : DiagonalTraceLocalizations l X := by
  letI : IsGrothendieckAbelian.{u + 1} (DiagonalCompleted l X) :=
    SheafOfModules.isGrothendieckAbelian_coefficientUniverse _
  letI : IsGrothendieckAbelian.{u + 1} (DiagonalSystems l X) :=
    towerGrothendieck (DiagonalMod l X)
  letI : IsGrothendieckAbelian.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb X) :=
    towerGrothendieck (DiagonalAb X)
  letI : IsGrothendieckAbelian.{u + 1} (ℕᵒᵖ ⥤ DiagonalCompleted l X) :=
    towerGrothendieck (DiagonalCompleted l X)
  letI := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} (DiagonalSystems l X)
  exact ⟨HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} (DiagonalAb X),
    HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} (DiagonalMod l X),
    inferInstance,
    HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb X),
    HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} (DiagonalCompleted l X),
    HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} (ℕᵒᵖ ⥤ DiagonalCompleted l X),
    hasExt_of_hasDerivedCategory _⟩

/-- Let `k` be a field of characteristic `p ≠ ℓ` and `Y` a separated `k`-scheme of finite type.
There is a canonical family of diagonal classes `δ_Λ : Δ_* Λ ⟶ Λ(1)[2]` on
`ℙ¹_Y ×_Y ℙ¹_Y` and traces `Tr_q : Rq_* Λ(1)[2] ⟶ Λ`, `Tr_{p_i}`, for
`Λ = ℤ_ℓ, 𝒪_E, E, ℚ̄_ℓ`, coming from the derived limit of the Cartier–Kummer system. -/
theorem exists_family_isCanonical (k : Type u) [Field k] [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ l)] (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [IsNoetherian Y] :
    ∃ family : Family l Y, family.IsCanonical l Y := by
  have hl : (l : k) ≠ 0 := by
    intro hz
    exact (Fact.out : ringChar k ≠ l)
      (CharP.ringChar_of_prime_eq_zero (Fact.out : l.Prime) hz)
  have hY : IsUnit (l : Γ(Y, ⊤)) := by
    simpa only [map_natCast] using (isUnit_iff_ne_zero.mpr hl).map
      (((Scheme.ΓSpecIso (.of k)).inv ≫ (Y ↘ Spec (.of k)).appTop).hom)
  have : IsNoetherian (ProjectiveLine Y) :=
    isNoetherian_of_locallyOfFiniteType (ProjectiveLine Y ↘ Y)
  have : IsNoetherian (diagonalSurface Y) :=
    isNoetherian_of_locallyOfFiniteType
      (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
  let aY := localizations l Y
  let aP := localizations l (ProjectiveLine Y)
  let aW := localizations l (diagonalSurface Y)
  obtain ⟨D, hcompletion, hsystem⟩ := exists_diagonalTowerSystem l Y hY
  obtain ⟨δ, hlimit⟩ := RationalP1.completedLimit_exists l Y hY D
    (diagonalTower_limit l k (ringChar k) (Fact.out : ringChar k ≠ l) Y hY D
      hcompletion hsystem)
  obtain ⟨family, reference, hred⟩ := diagonalTower_coefficients l k (ringChar k)
    (Fact.out : ringChar k ≠ l) Y hY D hcompletion hsystem δ hlimit
  exact ⟨family, hY, aY, aP, aW, D, hcompletion, hsystem, δ, hlimit, reference, hred⟩

variable {l}

/-! ### Integral coefficients -/

/-- The class `δ_{𝒪_E} : Δ_* 𝒪_E ⟶ 𝒪_E(1)[2]` of the canonical family reduces to the torsion cycle
classes: for every uniformizer `π` of `𝒪_E` and every `n`, its derived reduction modulo `π^(n+1)` is
the canonical Cartier cycle class of the diagonal. -/
theorem Family.IsCanonical.integral_delta_reduction {Y : Scheme.{u}} [IsNoetherian Y]
    {family : Family l Y} (h : family.IsCanonical l Y) (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E)) (n : ℕ) :
    ∃ d : Diagram (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      Y (quotientLine l E π n),
      Nonempty (ScalarCompatibility (quotientMap l E π n) Y
        (fun X ↦ spIntegralTwist X l E) (quotientLine l E π n)
        (quotientLineMap l E π n) (family.integral E) d) ∧
      QuotientClassCompatibility l Y E π n d := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hred⟩ := h
  obtain ⟨d, hs, hq⟩ := hred E π hπ n
  exact ⟨d, hs, hq.classCompatibility⟩

/-- The trace `Tr_q : Rq_* 𝒪_E(1)[2] ⟶ 𝒪_E` of the canonical family lifts the torsion traces: for
every uniformizer `π` of `𝒪_E` and every `n`, its derived reduction modulo `π^(n+1)` is the torsion
projective-line trace. -/
theorem Family.IsCanonical.integral_traceq_reduction {Y : Scheme.{u}} [IsNoetherian Y]
    {family : Family l Y} (h : family.IsCanonical l Y) (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E)) (n : ℕ) :
    ∃ d : Diagram (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      Y (quotientLine l E π n),
      Nonempty (ScalarCompatibility (quotientMap l E π n) Y
        (fun X ↦ spIntegralTwist X l E) (quotientLine l E π n)
        (quotientLineMap l E π n) (family.integral E) d) ∧
      QuotientTraceCompatibility l Y E π n d := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hred⟩ := h
  obtain ⟨d, hs, hq⟩ := hred E π hπ n
  exact ⟨d, hs, hq.traceCompatibility⟩

/-- With `𝒪_E`-coefficients, `Tr_{p₁} ∘ Rp_{1*}(δ) = 1`, after the identification
`Rp_{1*} Δ_* 𝒪_E ≅ 𝒪_E`. -/
theorem Family.integral_integration₁ {Y : Scheme.{u}} (family : Family l Y)
    (E : PadicAlgCl.FiniteIntermediateField l) :
    (family.integral E).support₁.hom ≫ (family.integral E).R₁.R.map (family.integral E).delta ≫
      (family.integral E).trace₁ = 𝟙 _ :=
  (family.integral E).integration₁

/-- With `𝒪_E`-coefficients, `Tr_{p₂} ∘ Rp_{2*}(δ) = 1`, after the identification
`Rp_{2*} Δ_* 𝒪_E ≅ 𝒪_E`. -/
theorem Family.integral_integration₂ {Y : Scheme.{u}} (family : Family l Y)
    (E : PadicAlgCl.FiniteIntermediateField l) :
    (family.integral E).support₂.hom ≫ (family.integral E).R₂.R.map (family.integral E).delta ≫
      (family.integral E).trace₂ = 𝟙 _ :=
  (family.integral E).integration₂

/-! ### Finite extensions of `ℚ_ℓ` -/

/-- The class `δ_E : Δ_* E ⟶ E(1)[2]` is the extension of scalars of `δ_{𝒪_E}` along `𝒪_E ⟶ E`. -/
theorem Family.rational_delta_eq {Y : Scheme.{u}} (family : Family l Y)
    (E : PadicAlgCl.FiniteIntermediateField l) :
    (derivedScalars (padicIntegersRingObjToContinuousMapRingObj l E) (diagonalSurface Y)).map
        (family.integral E).delta ≫ (family.toRational E).lineW.shift _ =
      (family.toRational E).supported.iso.hom ≫ (family.rational E).delta :=
  (family.toRational E).delta

/-- The trace `Tr_q : Rq_* E(1)[2] ⟶ E` is the extension of scalars of the `𝒪_E`-trace, through the
canonical scalar/direct-image comparison. -/
theorem Family.rational_traceq_eq {Y : Scheme.{u}} (family : Family l Y)
    (E : PadicAlgCl.FiniteIntermediateField l) :
    (derivedScalars (padicIntegersRingObjToContinuousMapRingObj l E) Y).map
        (family.integral E).traceq ≫ ((family.toRational E).units Y).iso.hom =
      ((family.toRational E).q.square.mate _).app _ ≫
        (family.rational E).Rq.R.map ((family.toRational E).lineP.shift _) ≫
          (family.rational E).traceq :=
  (family.toRational E).q.trace

/-- With `E`-coefficients, `Tr_{p₁} ∘ Rp_{1*}(δ_E) = 1`. -/
theorem Family.rational_integration₁ {Y : Scheme.{u}} (family : Family l Y)
    (E : PadicAlgCl.FiniteIntermediateField l) :
    (family.rational E).support₁.hom ≫ (family.rational E).R₁.R.map (family.rational E).delta ≫
      (family.rational E).trace₁ = 𝟙 _ :=
  (family.rational E).integration₁

/-- With `E`-coefficients, `Tr_{p₂} ∘ Rp_{2*}(δ_E) = 1`. -/
theorem Family.rational_integration₂ {Y : Scheme.{u}} (family : Family l Y)
    (E : PadicAlgCl.FiniteIntermediateField l) :
    (family.rational E).support₂.hom ≫ (family.rational E).R₂.R.map (family.rational E).delta ≫
      (family.rational E).trace₂ = 𝟙 _ :=
  (family.rational E).integration₂

/-! ### `ℚ̄_ℓ`-coefficients -/

/-- The class `δ_{ℚ̄_ℓ} : Δ_* ℚ̄_ℓ ⟶ ℚ̄_ℓ(1)[2]` is the extension of scalars of `δ_E` for every
finite stage `E`. -/
theorem Family.closure_delta_eq {Y : Scheme.{u}} (family : Family l Y)
    (E : PadicAlgCl.FiniteIntermediateField l) :
    (derivedScalars (Profinite.padicSubfieldRingObjToPadicAlgCl l E) (diagonalSurface Y)).map
        (family.rational E).delta ≫ (family.toClosure E).lineW.shift _ =
      (family.toClosure E).supported.iso.hom ≫ family.closure.delta :=
  (family.toClosure E).delta

/-- The trace `Tr_q : Rq_* ℚ̄_ℓ(1)[2] ⟶ ℚ̄_ℓ` is the extension of scalars of the `E`-trace for every
finite stage `E`. -/
theorem Family.closure_traceq_eq {Y : Scheme.{u}} (family : Family l Y)
    (E : PadicAlgCl.FiniteIntermediateField l) :
    (derivedScalars (Profinite.padicSubfieldRingObjToPadicAlgCl l E) Y).map
        (family.rational E).traceq ≫ ((family.toClosure E).units Y).iso.hom =
      ((family.toClosure E).q.square.mate _).app _ ≫
        family.closure.Rq.R.map ((family.toClosure E).lineP.shift _) ≫ family.closure.traceq :=
  (family.toClosure E).q.trace

/-- With `ℚ̄_ℓ`-coefficients, `Tr_{p₁} ∘ Rp_{1*}(δ_{ℚ̄_ℓ}) = 1`. -/
theorem Family.closure_integration₁ {Y : Scheme.{u}} (family : Family l Y) :
    family.closure.support₁.hom ≫ family.closure.R₁.R.map family.closure.delta ≫
      family.closure.trace₁ = 𝟙 _ :=
  family.closure.integration₁

/-- With `ℚ̄_ℓ`-coefficients, `Tr_{p₂} ∘ Rp_{2*}(δ_{ℚ̄_ℓ}) = 1`. -/
theorem Family.closure_integration₂ {Y : Scheme.{u}} (family : Family l Y) :
    family.closure.support₂.hom ≫ family.closure.R₂.R.map family.closure.delta ≫
      family.closure.trace₂ = 𝟙 _ :=
  family.closure.integration₂

/-! ### Base change -/

/-- The diagonal class of `d'` over `Y'` is the inverse image of the diagonal class of `d` over
`Y` along `g : Y' ⟶ Y`, through the canonical supported-source comparison and the line
comparison `mW`. -/
def DiagramClassPullback
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) (L : ∀ X : Scheme.{u}, Modules R X)
    (d : Diagram R Y L) (d' : Diagram R Y' L)
    (mP : (upperStar Ab.{u + 1} (baseP g)).obj (L (ProjectiveLine Y)).X ⟶
      (L (ProjectiveLine Y')).X)
    (mW : (upperStar Ab.{u + 1} (baseW g)).obj (L (diagonalSurface Y)).X ⟶
      (L (diagonalSurface Y')).X) : Prop :=
  ∃ data : SourcePullback R g L mP mW,
    (derivedUpper R (baseW g)).map d.delta ≫ data.endpoints.lineW.shift =
      (singlePullback R (baseW g) (source R Y)).hom ≫
        (DerivedCategory.singleFunctor (Modules R (diagonalSurface Y')) 0).map
          data.supported.hom ≫ d'.delta

/-- The three traces `Tr_q, Tr_{p₁}, Tr_{p₂}` of `d'` over `Y'` are the inverse images of
those of `d` over `Y` along `g : Y' ⟶ Y`, through the (invertible) base change maps of the
direct images and the line comparisons `mP`, `mW`. -/
def DiagramTracePullback
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) (L : ∀ X : Scheme.{u}, Modules R X)
    (d : Diagram R Y L) (d' : Diagram R Y' L)
    (mP : (upperStar Ab.{u + 1} (baseP g)).obj (L (ProjectiveLine Y)).X ⟶
      (L (ProjectiveLine Y')).X)
    (mW : (upperStar Ab.{u + 1} (baseW g)).obj (L (diagonalSurface Y)).X ⟶
      (L (diagonalSurface Y')).X) : Prop :=
  ∃ data : SourcePullback R g L mP mW,
    TracePullback R (ProjectiveLine Y ↘ Y) (ProjectiveLine Y' ↘ Y')
      (baseP g) g (ProjectiveSpace.map_over (ULift.{u} (Fin 2)) g).symm
      d.Rq d'.Rq d.q_canonical d'.q_canonical
      data.endpoints.lineP data.endpoints.cY d.traceq d'.traceq ∧
    TracePullback R
      (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
      (pullback.fst (ProjectiveLine Y' ↘ Y') (ProjectiveLine Y' ↘ Y'))
      (baseW g) (baseP g) data.geometry.first_square d.R₁ d'.R₁ d.p₁_canonical d'.p₁_canonical
      data.endpoints.lineW data.endpoints.cP d.trace₁ d'.trace₁ ∧
    TracePullback R
      (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
      (pullback.snd (ProjectiveLine Y' ↘ Y') (ProjectiveLine Y' ↘ Y'))
      (baseW g) (baseP g) data.geometry.second_square d.R₂ d'.R₂ d.p₂_canonical
      d'.p₂_canonical data.endpoints.lineW data.endpoints.cP d.trace₂ d'.trace₂

/-- The diagonal classes of the canonical families are compatible with base change along a morphism
`g : Y' ⟶ Y` of separated `k`-schemes of finite type: for `𝒪_E`-coefficients through the canonical
comparison of the Tate twists, and for `E`- and `ℚ̄_ℓ`-coefficients through some comparison of the
Tate twists. -/
theorem Family.IsCanonical.delta_pullback (k : Type u) [Field k] [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ l)] {Y Y' : Scheme.{u}} [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [IsNoetherian Y] [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
    [IsSeparated (Y' ↘ Spec (.of k))] [IsNoetherian Y'] (g : Y' ⟶ Y)
    [g.IsOver (Spec (.of k))] {family : Family l Y} {family' : Family l Y'}
    (_h : family.IsCanonical l Y) (_h' : family'.IsCanonical l Y') :
    (∀ E : PadicAlgCl.FiniteIntermediateField l,
      DiagramClassPullback (Profinite.padicIntegersRingObj.{u} l E.1) g
        (fun X ↦ spIntegralTwist X l E) (family.integral E) (family'.integral E)
        (spIntegralComparison (baseP g) l E) (spIntegralComparison (baseW g) l E)) ∧
    (∀ E : PadicAlgCl.FiniteIntermediateField l, ∃ mP mW,
      DiagramClassPullback (Profinite.continuousMapRingObj.{u} E.1) g
        (fun X ↦ spRationalTwist X l E) (family.rational E) (family'.rational E) mP mW) ∧
    ∃ mP mW, DiagramClassPullback (Profinite.padicAlgClRingObj.{u} l) g
      (fun X ↦ spQbarTwist X l) family.closure family'.closure mP mW := by
  sorry

/-- The traces of the canonical families are compatible with base change along a morphism
`g : Y' ⟶ Y` of separated `k`-schemes of finite type: for `𝒪_E`-coefficients through the
canonical comparison of the Tate twists, and for `E`- and `ℚ̄_ℓ`-coefficients through some
comparison of the Tate twists. -/
theorem Family.IsCanonical.trace_pullback (k : Type u) [Field k] [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ l)] {Y Y' : Scheme.{u}} [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [IsNoetherian Y] [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
    [IsSeparated (Y' ↘ Spec (.of k))] [IsNoetherian Y'] (g : Y' ⟶ Y)
    [g.IsOver (Spec (.of k))] {family : Family l Y} {family' : Family l Y'}
    (_h : family.IsCanonical l Y) (_h' : family'.IsCanonical l Y') :
    (∀ E : PadicAlgCl.FiniteIntermediateField l,
      DiagramTracePullback (Profinite.padicIntegersRingObj.{u} l E.1) g
        (fun X ↦ spIntegralTwist X l E) (family.integral E) (family'.integral E)
        (spIntegralComparison (baseP g) l E) (spIntegralComparison (baseW g) l E)) ∧
    (∀ E : PadicAlgCl.FiniteIntermediateField l, ∃ mP mW,
      DiagramTracePullback (Profinite.continuousMapRingObj.{u} E.1) g
        (fun X ↦ spRationalTwist X l E) (family.rational E) (family'.rational E) mP mW) ∧
    ∃ mP mW, DiagramTracePullback (Profinite.padicAlgClRingObj.{u} l) g
      (fun X ↦ spQbarTwist X l) family.closure family'.closure mP mW := by
  sorry

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
