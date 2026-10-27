/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.Paper.SystemTensorMateArrows
public import Sheaf.SixFunctors.ProperOpenProjectionMate
public import Sheaf.SixFunctors.AmbientExactClopenComparison
public import Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows
import all Sheaf.Paper.SystemTensorMateArrows
import Sheaf.SixFunctors.SemilinearProperOpenMatePasting
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Identification of the intrinsic system clopen arrow and its proper mate

Source: Stacks Project, more-etale.tex, Tag 0F7B (lemma-shriek-proper-and-open),
open case, and sites-cohomology.tex, Tag 07A7 (remark-base-change).
The strict-system identification is agent-formulated, rather than quoted from Stacks
(blueprint: lem-pur-system-clopen-mate-identification).

The first statement uses the universe convention of SystemTensorMate. The realization
statement uses its recorded coefficient universe. All comparisons are canonical adjoint
comparisons on whole systems, before finite evaluation or inverse limit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open WeilConjectures

namespace WeilConjectures.SystemClopenMate

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The positive quotient sequence, in the diagram-arrow interface's universe.
This is only the specialization of the coefficient datum, with exponent n+1.
Source: Stacks 0941; the coefficient convention
(blueprint: lem-pur-system-clopen-mate-identification). -/
abbrev coefficients (n : ℕ) : CommRingCat.{u + 1} :=
  CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))

/-- The actual adjacent quotient maps, with their common universe lift.
Source: Stacks 0941; the coefficient convention
(blueprint: lem-pur-system-clopen-mate-identification). -/
abbrev transitions (n : ℕ) : coefficients l E (n + 1) ⟶ coefficients l E n :=
  CommRingCat.ofHom (Padic.coefficientExtensionTransition l E (n + 1)).ulift

/-- Direct images in the two presentations are the same sectionwise construction.
Source: Stacks 0941, 03D7; agent presentation comparison
(blueprint: lem-pur-system-clopen-mate-identification).
Proof: both base functors keep the sequence index and apply pro-etale base change.
Their coefficient maps agree on constant sections by the sheafification Hom bijection;
these sections determine the maps. Thus continuous module pushforward is the same functor,
including all quotient transitions, rather than merely agreeing after evaluation. -/
theorem direct_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    SystemTensorMate.direct l E f =
      ProEtale.VaryingRing.push (coefficients l E) (transitions l E) f := by
  exact SystemTensorMate.direct_eq_varying l E f

/-- The unique inverse-image comparison preserving the specified ordinary adjunction.
Source: Stacks 07A7, 03D7
(blueprint: lem-pur-system-clopen-mate-identification). -/
def ordinaryPullComparison (o : SystemTensorMate.Operations l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (o.adj f).leftAdjointUniq
    ((ProEtale.VaryingRing.moduleAdj (coefficients l E) (transitions l E) f).ofNatIsoRight
      (eqToIso (direct_eq l E f)).symm)

/-- The open-extension comparison is fixed by the ordinary open adjunction units.
Source: Stacks 03DI, 07A7
(blueprint: lem-pur-system-clopen-mate-identification). -/
def ordinaryOpenComparison (o : SystemTensorMate.Operations l E)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :=
  ((o.openAdj j).ofNatIsoRight (ordinaryPullComparison l E o j)).leftAdjointUniq
    (ProEtale.VaryingRing.moduleJAdj (coefficients l E) (transitions l E) j)

/-- Exact localization of the canonical inverse-image comparison.
Source: Stacks 015F, 07A7
(blueprint: lem-pur-system-clopen-mate-identification). -/
def pullComparison (o : SystemTensorMate.Operations l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  letI := ProEtale.VaryingRing.pullAdditive (coefficients l E) (transitions l E) f
  letI := ProEtale.VaryingRing.pullLimits (coefficients l E) (transitions l E) f
  letI := ProEtale.VaryingRing.pullColimits (coefficients l E) (transitions l E) f
  Functor.mapDerivedCategoryNatIso (ordinaryPullComparison l E o f)

/-- Exact localization of the canonical open-extension comparison.
Source: Stacks 015F, 03DI
(blueprint: lem-pur-system-clopen-mate-identification). -/
def openComparison (o : SystemTensorMate.Operations l E)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :=
  letI := ProEtale.VaryingRing.extensionAdditive (coefficients l E) (transitions l E) j
  letI := ProEtale.VaryingRing.extensionLimits (coefficients l E) (transitions l E) j
  letI := ProEtale.VaryingRing.extensionColimits (coefficients l E) (transitions l E) j
  Functor.mapDerivedCategoryNatIso (ordinaryOpenComparison l E o j)

/-- The actual clopen composite in the diagram-arrow coordinates. Its middle arrow is
localization of beta, then b_! of the identity/zero projector, then the canonical open
and inverse-image compositors. The comparisons on either end are uniquely adjoint-normalized.
Source: Stacks 0F7B, 07A7
(blueprint: lem-pur-system-clopen-mate-identification). -/
def a (o : SystemTensorMate.Operations l E)
    {A B C D : Scheme.{u}} (k : A ⟶ B) (r : A ⟶ C) (p : B ⟶ D) (i : C ⟶ D)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    o.J i ⋙ o.P p ⟶ o.P r ⋙ o.J k :=
  (Functor.isoWhiskerRight (openComparison l E o i) _).hom ≫
    (Functor.isoWhiskerLeft _ (pullComparison l E o p)).hom ≫
    ProEtale.VaryingRing.alpha (coefficients l E) (transitions l E) k r p i h ≫
    (Functor.isoWhiskerRight (pullComparison l E o r).symm _).hom ≫
    (Functor.isoWhiskerLeft _ (openComparison l E o k).symm).hom

/-- Localized identity/zero projector with the canonical identity and composition casts.
Source: Stacks 015F, 09AE
(blueprint: lem-pur-system-clopen-mate-identification). -/
def rho {X Y : Scheme.{u}} (s : X ⟶ Y) [IsOpenImmersion s] [IsClosedImmersion s] :=
  letI := ProEtale.VaryingRing.pullAdditive (coefficients l E) (transitions l E) s
  letI := ProEtale.VaryingRing.pullLimits (coefficients l E) (transitions l E) s
  letI := ProEtale.VaryingRing.pullColimits (coefficients l E) (transitions l E) s
  letI := ProEtale.VaryingRing.extensionAdditive (coefficients l E) (transitions l E) s
  letI := ProEtale.VaryingRing.extensionLimits (coefficients l E) (transitions l E) s
  letI := ProEtale.VaryingRing.extensionColimits (coefficients l E) (transitions l E) s
  (Functor.mapDerivedCategoryIdIso _).inv ≫
    ProEtale.AmbientClopen.localize
      (ProEtale.VaryingRing.modulePi (coefficients l E) (transitions l E) s) ≫
    (Functor.mapDerivedCategoryCompIso _ _).hom

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor HasDerivedCategory.standard rho a
  ProEtale.SemilinearProperOpen.pi ProEtale.SemilinearProperOpen.beta
  ProEtale.SemilinearProperOpen.alpha ProEtale.VaryingRing.alpha
  ProEtale.VaryingRing.moduleBeta ProEtale.AmbientClopen.localizeSquare

/-- Identification of the projector, normalized beta, clopen composite, localized
open-restriction arrow and its proper mate on arbitrary unbounded quotient systems.
`HEq` expresses equality between the recorded presentations of the same canonical
functors; the diagram-arrow equality uses the explicit adjoint comparisons above.
Source: Stacks 0F7B and 07A7; agent-formulated identification
(blueprint: lem-pur-system-clopen-mate-identification).

Proof: (1) Reindex positive levels by n-1. Both ordinary projectors act by (identity,zero)
on the clopen decomposition. These maps commute with every semilinear transition, so their
termwise localizations agree intrinsically, without testing derived evaluation.
(2) Open tensor normalization fixes beta inverse by its open-unit transpose. Therefore
both beta maps agree. Substitute this and the projector equality in the clopen word;
use exactly bs=k and qs=r with the adjunction-normalized compositors to identify alpha.
(3) Ambient exact clopen localization identifies that word with the localization of the
unique ordinary arrow whose restriction is the open-unit/square word of ordinaryAlpha.
The canonical adjoint comparisons preserve those units and the square, hence preserve
that characterization and give o.alpha=a.
(4) Semilinear proper/open mate pasting identifies the intrinsic Gamma with the proper
mate of alpha. The mate bijection sends the localized arrow, now equal to a, to eta_p,
then R_p(a R_r), then R_p(k_! epsilon_r). This is the displayed formula. No inversion of
the proper mate, cartesian-input restriction or faithfulness of evaluation is used. -/
theorem systemClopenMateIdentification
    (F : FiniteFieldDatum.{u}) (_hl : l ≠ F.p)
    (o : SystemTensorMate.Operations l E)
    {A B C D : Scheme.{u}}
    [A.Over (Spec (.of F.k))] [B.Over (Spec (.of F.k))]
    [C.Over (Spec (.of F.k))] [D.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (A ↘ Spec (.of F.k))] [QuasiCompact (A ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (B ↘ Spec (.of F.k))] [QuasiCompact (B ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (C ↘ Spec (.of F.k))] [QuasiCompact (C ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (D ↘ Spec (.of F.k))] [QuasiCompact (D ↘ Spec (.of F.k))]
    [IsSeparated (A ↘ Spec (.of F.k))] [IsSeparated (B ↘ Spec (.of F.k))]
    [IsSeparated (C ↘ Spec (.of F.k))] [IsSeparated (D ↘ Spec (.of F.k))]
    (k : A ⟶ B) (r : A ⟶ C) (p : B ⟶ D) (i : C ⟶ D)
    [k.IsOver (Spec (.of F.k))] [r.IsOver (Spec (.of F.k))]
    [p.IsOver (Spec (.of F.k))] [i.IsOver (Spec (.of F.k))]
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    HEq (rho l E (ProEtale.StrictTower.squareLift k r p i h))
      (ProEtale.SemilinearProperOpen.pi (coefficients l E) (transitions l E)
        (ProEtale.StrictTower.squareLift k r p i h)) ∧
    HEq (ProEtale.AmbientClopen.localizeSquare _ _ _ _
      (ProEtale.VaryingRing.moduleBeta (coefficients l E) (transitions l E)
        (pullback.snd p i) (pullback.fst p i) i p pullback.condition.symm
        (IsPullback.of_hasPullback p i).flip).hom)
      (ProEtale.SemilinearProperOpen.beta (coefficients l E) (transitions l E)
        (pullback.snd p i) (pullback.fst p i) i p pullback.condition.symm
        (IsPullback.of_hasPullback p i).flip).hom ∧
    HEq (ProEtale.VaryingRing.alpha (coefficients l E) (transitions l E) k r p i h)
      (ProEtale.SemilinearProperOpen.alpha (coefficients l E) (transitions l E) k r p i h) ∧
    o.alpha k r p i h = a l E o k r p i h ∧
    (∀ M : SystemTensorMate.D l E A,
      (o.gamma k r p i h).app M =
        (o.derivedAdj p).unit.app ((o.J i).obj ((SystemTensorMate.pushDerived l E r).obj M)) ≫
        (SystemTensorMate.pushDerived l E p).map
          ((a l E o k r p i h).app ((SystemTensorMate.pushDerived l E r).obj M)) ≫
        (SystemTensorMate.pushDerived l E p).map
          ((o.J k).map ((o.derivedAdj r).counit.app M))) := by
  sorry

end WeilConjectures.SystemClopenMate

namespace WeilConjectures.IntegralSystemRealization

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor HasDerivedCategory.standard CategoryTheory.constantSheaf
  ProEtale.AmbientClopen.realizationAlpha WeilConjectures.pullbackTensorSequenceDerived

/-- The intrinsic Gamma used in the system projection-mate theorem and the proper
mate of the same actual clopen arrow both have the stipulated unit--a--counit formula.
The realization coordinates use only their canonical section-preserving bridge.
Source: Stacks 0F7B and 07A7; agent-formulated intrinsic system identification
(blueprint: lem-pur-system-clopen-mate-identification).

Proof: the projector and open-unit-normalized beta comparisons of
systemClopenMateIdentification identify the clopen word in the two presentations.
Ambient exact localization identifies it with the localized ordinary open-restriction
arrow. Use semilinear proper/open mate pasting: its mate is the open adjunct of
lambda inverse. The canonical bridge preserves adjunction units and counits and the
pullback compositors, so this is precisely the adjunct characterization of
z.properOpen.gamma in lem-sf-proper-open-projection-mate. Injectivity of the open
adjunction Hom bijection gives equality of transformations. Finally expand mateEquiv:
its component is eta_p, followed by R_p(a R_r), followed by R_p(k_! epsilon_r).
All arguments occur in the ordinary unbounded derived category of systems, without
finite evaluation, an inverse limit, a cartesian square, or invertibility of Gamma. -/
theorem systemClopenRealizationMateIdentification
    (F : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (o : Operations l E) (z : Realizations l E F o)
    {A B C D : Scheme.{u}}
    [A.Over (Spec (.of F.k))] [B.Over (Spec (.of F.k))]
    [C.Over (Spec (.of F.k))] [D.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (A ↘ Spec (.of F.k))] [QuasiCompact (A ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (B ↘ Spec (.of F.k))] [QuasiCompact (B ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (C ↘ Spec (.of F.k))] [QuasiCompact (C ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (D ↘ Spec (.of F.k))] [QuasiCompact (D ↘ Spec (.of F.k))]
    [IsSeparated (A ↘ Spec (.of F.k))] [IsSeparated (B ↘ Spec (.of F.k))]
    [IsSeparated (C ↘ Spec (.of F.k))] [IsSeparated (D ↘ Spec (.of F.k))]
    (k : A ⟶ B) (r : A ⟶ C) (p : B ⟶ D) (i : C ⟶ D)
    [k.IsOver (Spec (.of F.k))] [r.IsOver (Spec (.of F.k))]
    [p.IsOver (Spec (.of F.k))] [i.IsOver (Spec (.of F.k))]
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    z.properOpen.gamma k r p i h =
      (mateEquiv (o.direct r).adj (o.direct p).adj
        (TwoSquare.mk _ _ _ _
          (ProEtale.AmbientClopen.realizationAlpha l E o z.canonicalBridge k r p i h))).natTrans ∧
    (∀ M : System l E A,
      (z.properOpen.gamma k r p i h).app M =
        (o.direct p).adj.unit.app
          ((Operations.shriek l E o i).obj ((Operations.push l E o r).obj M)) ≫
        (Operations.push l E o p).map
          ((ProEtale.AmbientClopen.realizationAlpha l E o z.canonicalBridge k r p i h).app
            ((Operations.push l E o r).obj M)) ≫
        (Operations.push l E o p).map
          ((Operations.shriek l E o k).map ((o.direct r).adj.counit.app M))) := by
  sorry

end WeilConjectures.IntegralSystemRealization
