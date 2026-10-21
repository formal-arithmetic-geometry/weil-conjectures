/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.Paper.IntegralDerivedCoefficientData
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier
import Sheaf.AlgebraicGeometry.FiniteTypeNoetherianSpectrum
import Sheaf.Paper.CartesianCoefficients
import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.CategoryTheory.ExactOpenClosedUnboundedCalculus
import Sheaf.CategoryTheory.ExactDerivedComposition
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Bounded integral base change for a stratum extension

Source: Stacks Project, Tags 09AA, 09BM, 09BN and 09AH; blueprint main-20261015,
`det-lem-int-tensor-pullback.proof.md`, Local models.
(blueprint: lem-sfb-integral-bounded-stratum-base-change)

All derived functors here apply the exact module functors termwise. Exactness of a closed
pushforward is returned as a witness, rather than assumed. The bounded inclusions retain
all bounded inputs, without a constructibility or completeness condition.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralBoundedStratumBaseChange

section Maps

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {S' S T' T : Scheme.{u}} {hS : S' ⟶ S} {a' : S' ⟶ T'}
  {a : S ⟶ T} {h : T' ⟶ T}

/-- The exact module pullback applied termwise, with its structural arguments shared.
Source: Stacks 09AA/09BN, bounded module pullback
(blueprint: lem-sfb-integral-bounded-stratum-base-change). -/
def pullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (CondensedRing.upperStar Λ f).mapDerivedCategory

/-- Open extension by zero applied termwise.
Source: Stacks 09BN/09AH
(blueprint: lem-sfb-integral-bounded-stratum-base-change). -/
def openExtension {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :=
  (CondensedRing.openImmersionLowerShriek Λ f).mapDerivedCategory

/-- The actual localized open adjunction, with the preceding named functors.
Source: Stacks 09BN, adjunction j_! to j^*
(blueprint: lem-sfb-integral-bounded-stratum-base-change). -/
def openAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    openExtension Λ f ⊣ pullback Λ f :=
  CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ f

/-- Closed direct image applied termwise using its exactness witness.
Source: Stacks 09BM
(blueprint: lem-sfb-integral-bounded-stratum-base-change). -/
def closedDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    [PreservesFiniteColimits (CondensedRing.lowerStar Λ f)] :=
  (CondensedRing.lowerStar Λ f).mapDerivedCategory

/-- The actual localized closed adjunction.
Source: Stacks 09AA/09BM
(blueprint: lem-sfb-integral-bounded-stratum-base-change). -/
def closedAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y)
    [PreservesFiniteColimits (CondensedRing.lowerStar Λ f)] :
    pullback Λ f ⊣ closedDirectImage Λ f :=
  (CondensedRing.upperStarLowerStarAdjunction Λ f).mapDerivedCategoryAdjunction

/-- Pullback composition around the given commutative square, localized termwise.
Source: Stacks 09AA/09BN, pullback composition in the base-change construction
(blueprint: lem-sfb-integral-bounded-stratum-base-change). -/
def pullbackSquare (sq : CommSq hS a' a h) :
    (pullback Λ a) ⋙
        (pullback Λ hS) ≅
      (pullback Λ h) ⋙
        (pullback Λ a') :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      ((CondensedRing.upperStarComp Λ hS a).symm ≪≫
        eqToIso (congrArg (CondensedRing.upperStar Λ) sq.w) ≪≫
          CondensedRing.upperStarComp Λ a' h) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The open exchange map beta, the mate of the actual pullback-composition comparison.
Source: Stacks 09BN/09AH and the node proof, Step 4
(blueprint: lem-sfb-integral-bounded-stratum-base-change). -/
def openMate [IsOpenImmersion a] [IsOpenImmersion a'] (sq : CommSq hS a' a h) :
    (pullback Λ hS) ⋙
        (openExtension Λ a') ⟶
      (openExtension Λ a) ⋙
        (pullback Λ h) :=
  Adjunction.exchangeLeft
    (openAdjunction Λ a)
    (openAdjunction Λ a')
    (pullbackSquare Λ sq)

/-- The closed exchange map gamma, unit insertion followed by square transport and counit.
The exactness witnesses merely allow the specified termwise derived functors to be named.
Source: Stacks 09AA/09BM/09AH and the node proof, Step 4
(blueprint: lem-sfb-integral-bounded-stratum-base-change). -/
def closedMate [PreservesFiniteColimits (CondensedRing.lowerStar Λ a)]
    [PreservesFiniteColimits (CondensedRing.lowerStar Λ a')] (sq : CommSq hS a' a h) :
    (closedDirectImage Λ a) ⋙
        (pullback Λ h) ⟶
      (pullback Λ hS) ⋙
        (closedDirectImage Λ a') :=
  Adjunction.exchangeRight
    (closedAdjunction Λ a)
    (closedAdjunction Λ a')
    (pullbackSquare Λ sq).symm

end Maps

open CondensedRing (integralCoefficientRing)

/-- The canonical open and closed mates are natural isomorphisms on all bounded inputs,
with identity restrictions on their own stratum and zero restrictions on its complement.
The existential exactness witnesses supply the termwise closed derived functors.
Source: Stacks 09AA, 09BM, 09BN and 09AH; node proof, Steps 1--6
(blueprint: lem-sfb-integral-bounded-stratum-base-change).

Proof:
1. Finite type over the field gives Noetherian underlying spaces by the finite affine
cover argument of `lem-sfb-finite-type-noetherian-spectrum`; all the opens are retrocompact.
Open and closed immersions survive base change, and their ranges stay complementary
by the base-change image lemma.
2. Cartesian coefficients make pullback exact. Transport the actual module operations
and adjunctions to section-ring modules using the internal-module-operations transport
lemma. Tags 09AA/09BM/09BN/09AH give exact extension and closed direct image, mixed zero
restrictions and the localization short exact sequence. Apply the restrictions to this
sequence and use triangle identities to see that the actual open units and closed
counits are invertible; transfer back through the coefficient transport equivalences.
3. Apply exact-open-closed-unbounded calculus. The localized adjunctions have the actual
units and counits, the mixed restrictions vanish, and complementary restrictions jointly
reflect isomorphisms. Exact-functor cohomology identifies H^q(FK) with F(H^q K), so every
functor here preserves both cohomological bounds.
4. Descend pullback composition via exact-derived composition and natural-isomorphism
localization. The definitions `openMate` and `closedMate` are precisely the open transpose
and the closed unit--square--counit mate, and are natural before imposing bounds.
5. The open transpose identity gives the displayed open restriction equation. Both
units and the square comparison are invertible, so this is the identity after canonical
identification. Its closed restriction has zero source and target by mixed vanishing
and the square comparison. Joint reflection makes beta invertible.
6. The closed triangle identity gives the displayed closed restriction equation.
The counits identify this with the identity. Its open restriction is between zero
objects by mixed vanishing and square transport. Joint reflection makes gamma invertible.
Restriction along the full bounded inclusions gives the two asserted natural isomorphisms.
-/
theorem integral_bounded_open_closed_base_change
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    {U : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    {Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    {T : Over (Spec (.of k))}
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    {Up : Over (Spec (.of k))}
    [LocallyOfFiniteType Up.hom] [QuasiCompact Up.hom] [IsSeparated Up.hom]
    {Zp : Over (Spec (.of k))}
    [LocallyOfFiniteType Zp.hom] [QuasiCompact Zp.hom] [IsSeparated Zp.hom]
    {Tp : Over (Spec (.of k))}
    [LocallyOfFiniteType Tp.hom] [QuasiCompact Tp.hom] [IsSeparated Tp.hom]
    (h : Tp ⟶ T) (j : U ⟶ T) (i : Z ⟶ T)
    (hU : Up ⟶ U) (jp : Up ⟶ Tp) (hZ : Zp ⟶ Z) (ip : Zp ⟶ Tp)
    [IsOpenImmersion j.left] [IsClosedImmersion i.left]
    [IsOpenImmersion jp.left] [IsClosedImmersion ip.left]
    (hcomp : Set.range j.left = (Set.range i.left)ᶜ)
    (sqU : IsPullback hU.left jp.left j.left h.left)
    (sqZ : IsPullback hZ.left ip.left i.left h.left) :
    Exists fun [_hi : PreservesFiniteColimits (CondensedRing.lowerStar (integralCoefficientRing l
            E) i.left)] ↦
    Exists fun [_hip : PreservesFiniteColimits (CondensedRing.lowerStar (integralCoefficientRing l
            E)
            ip.left)] ↦
      (∃ beta : DerivedCategory.Bounded.ι ⋙ ((pullback (integralCoefficientRing l E) hU.left) ⋙
            (openExtension (integralCoefficientRing l E) jp.left)) ≅
          DerivedCategory.Bounded.ι ⋙ ((openExtension (integralCoefficientRing l E) j.left) ⋙
            (pullback (integralCoefficientRing l E) h.left)),
        beta.hom = Functor.whiskerLeft DerivedCategory.Bounded.ι (openMate
            (integralCoefficientRing l E)
            sqU.toCommSq)) ∧
      (∃ gamma : DerivedCategory.Bounded.ι ⋙ ((closedDirectImage (integralCoefficientRing l E)
            i.left) ⋙
            (pullback (integralCoefficientRing l E) h.left)) ≅
          DerivedCategory.Bounded.ι ⋙ ((pullback (integralCoefficientRing l E) hZ.left) ⋙
            (closedDirectImage (integralCoefficientRing l E) ip.left)),
        gamma.hom = Functor.whiskerLeft DerivedCategory.Bounded.ι (closedMate
            (integralCoefficientRing l E)
            sqZ.toCommSq)) ∧
      (∀ N : DerivedCategory.Bounded
          (Mod (Sheaf (Scheme.ProEt.topology U.left) Ab.{u + 1})
            (condensedRingObj (integralCoefficientRing l E) U.left)),
        DerivedCategory.TStructure.t.bounded
            (((pullback (integralCoefficientRing l E) hU.left) ⋙
            (openExtension (integralCoefficientRing l E) jp.left)).obj N.obj) ∧
        DerivedCategory.TStructure.t.bounded
            (((openExtension (integralCoefficientRing l E) j.left)
            ⋙ (pullback (integralCoefficientRing l E) h.left)).obj N.obj) ∧
        IsIso ((openAdjunction (integralCoefficientRing l E) jp.left).unit.app ((pullback
            (integralCoefficientRing l E) hU.left).obj
            N.obj)) ∧
        IsIso ((openAdjunction (integralCoefficientRing l E) j.left).unit.app N.obj) ∧
        (openAdjunction (integralCoefficientRing l E) jp.left).unit.app
            ((pullback (integralCoefficientRing l E) hU.left).obj N.obj) ≫
            (pullback (integralCoefficientRing l E) jp.left).map
            ((openMate
            (integralCoefficientRing l
            E) sqU.toCommSq).app N.obj) =
          (pullback (integralCoefficientRing l E) hU.left).map
            ((openAdjunction (integralCoefficientRing l E) j.left).unit.app N.obj) ≫
            (pullbackSquare (integralCoefficientRing l E) sqU.toCommSq).hom.app
            ((openExtension (integralCoefficientRing l E) j.left).obj N.obj) ∧
        IsZero ((pullback (integralCoefficientRing l E) ip.left).obj
          (((pullback (integralCoefficientRing l E) hU.left) ⋙
            (openExtension (integralCoefficientRing l E) jp.left)).obj N.obj)) ∧
        IsZero ((pullback (integralCoefficientRing l E) ip.left).obj
          (((openExtension (integralCoefficientRing l E) j.left) ⋙
            (pullback (integralCoefficientRing l E) h.left)).obj N.obj)) ∧
        (pullback (integralCoefficientRing l E) ip.left).map
            ((openMate
            (integralCoefficientRing l E)
            sqU.toCommSq).app N.obj) = 0) ∧
      (∀ N : DerivedCategory.Bounded
          (Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
            (condensedRingObj (integralCoefficientRing l E) Z.left)),
        DerivedCategory.TStructure.t.bounded
            (((closedDirectImage (integralCoefficientRing l E) i.left) ⋙
            (pullback (integralCoefficientRing l E) h.left)).obj N.obj) ∧
        DerivedCategory.TStructure.t.bounded
            (((pullback (integralCoefficientRing l E) hZ.left) ⋙
            (closedDirectImage (integralCoefficientRing l E) ip.left)).obj N.obj) ∧
        IsIso ((closedAdjunction (integralCoefficientRing l E) i.left).counit.app N.obj) ∧
        IsIso ((closedAdjunction (integralCoefficientRing l E) ip.left).counit.app ((pullback
            (integralCoefficientRing l E) hZ.left).obj N.obj)) ∧
        (pullback (integralCoefficientRing l E) ip.left).map
            ((closedMate
            (integralCoefficientRing l
            E) sqZ.toCommSq).app N.obj) ≫
            (closedAdjunction (integralCoefficientRing l E) ip.left).counit.app ((pullback
            (integralCoefficientRing l E) hZ.left).obj N.obj) =
          (pullbackSquare (integralCoefficientRing l E) sqZ.toCommSq).inv.app
            ((closedDirectImage (integralCoefficientRing l E) i.left).obj N.obj) ≫
            (pullback (integralCoefficientRing l E) hZ.left).map
            ((closedAdjunction (integralCoefficientRing l E) i.left).counit.app N.obj) ∧
        IsZero ((pullback (integralCoefficientRing l E) jp.left).obj
          (((closedDirectImage (integralCoefficientRing l E) i.left) ⋙
            (pullback (integralCoefficientRing l E) h.left)).obj N.obj)) ∧
        IsZero ((pullback (integralCoefficientRing l E) jp.left).obj
          (((pullback (integralCoefficientRing l E) hZ.left) ⋙
            (closedDirectImage (integralCoefficientRing l E) ip.left)).obj N.obj)) ∧
        (pullback (integralCoefficientRing l E) jp.left).map
            ((closedMate
            (integralCoefficientRing l
            E) sqZ.toCommSq).app N.obj) = 0) := by
  sorry

/-- Locally closed base change is the composite of the open beta and the inverse closed
gamma, with a fixed open--closed factorization. The displayed equation specifies that
composite without choosing any unrelated isomorphism.
Source: blueprint `det-lem-int-tensor-pullback.proof.md`, Local models; node proof, Step 7
(blueprint: lem-sfb-integral-bounded-stratum-base-change).

Proof: Apply the preceding open result to u inside the closure and the closed result
to i, using the bounded input u_!M. Its boundedness follows from exact-functor cohomology.
First apply i'_* to beta_u,M, then compose with the inverse of gamma_i,u_!M. These maps
are natural in M; every factor is invertible, and exactness keeps both ends bounded.
The composite satisfies the displayed cancellation equation by the inverse identity.
No independence of factorization, constructibility, or derived completeness is used.
-/
theorem integral_bounded_locally_closed_base_change
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    {S : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    {C : Over (Spec (.of k))}
    [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
    {T : Over (Spec (.of k))}
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    {Sp : Over (Spec (.of k))}
    [LocallyOfFiniteType Sp.hom] [QuasiCompact Sp.hom] [IsSeparated Sp.hom]
    {Cp : Over (Spec (.of k))}
    [LocallyOfFiniteType Cp.hom] [QuasiCompact Cp.hom] [IsSeparated Cp.hom]
    {Tp : Over (Spec (.of k))}
    [LocallyOfFiniteType Tp.hom] [QuasiCompact Tp.hom] [IsSeparated Tp.hom]
    (h : Tp ⟶ T) (u₀ : S ⟶ C) (i : C ⟶ T)
    (hS : Sp ⟶ S) (up : Sp ⟶ Cp) (hC : Cp ⟶ C) (ip : Cp ⟶ Tp)
    [IsOpenImmersion u₀.left] [IsClosedImmersion i.left]
    [IsOpenImmersion up.left] [IsClosedImmersion ip.left]
    (sqU : IsPullback hS.left up.left u₀.left hC.left)
    (sqI : IsPullback hC.left ip.left i.left h.left) :
    Exists fun [_hi : PreservesFiniteColimits (CondensedRing.lowerStar (integralCoefficientRing l
            E) i.left)] ↦
    Exists fun [_hip : PreservesFiniteColimits (CondensedRing.lowerStar (integralCoefficientRing l
            E)
            ip.left)] ↦
      ∃ e : DerivedCategory.Bounded.ι ⋙
          ((pullback (integralCoefficientRing l E) hS.left) ⋙
            (openExtension (integralCoefficientRing l E) up.left) ⋙ (closedDirectImage
            (integralCoefficientRing l E) ip.left)) ≅
        DerivedCategory.Bounded.ι ⋙
          ((openExtension (integralCoefficientRing l E) u₀.left) ⋙
            (closedDirectImage (integralCoefficientRing l E) i.left) ⋙ (pullback
            (integralCoefficientRing l E) h.left)),
        ∀ M : DerivedCategory.Bounded
            (Mod (Sheaf (Scheme.ProEt.topology S.left) Ab.{u + 1})
              (condensedRingObj (integralCoefficientRing l E) S.left)),
          DerivedCategory.TStructure.t.bounded
              (((pullback (integralCoefficientRing l E) hS.left) ⋙
            (openExtension (integralCoefficientRing l E) up.left)
            ⋙ (closedDirectImage (integralCoefficientRing l E) ip.left)).obj M.obj) ∧
          DerivedCategory.TStructure.t.bounded
              (((openExtension (integralCoefficientRing l E) u₀.left) ⋙
            (closedDirectImage (integralCoefficientRing l E) i.left) ⋙
            (pullback (integralCoefficientRing l E) h.left)).obj M.obj) ∧
          e.hom.app M ≫
              (closedMate (integralCoefficientRing l E) sqI.toCommSq).app
            ((openExtension (integralCoefficientRing l E) u₀.left).obj M.obj) =
            (closedDirectImage (integralCoefficientRing l E) ip.left).map
            ((openMate
            (integralCoefficientRing l
            E) sqU.toCommSq).app M.obj) := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralBoundedStratumBaseChange
