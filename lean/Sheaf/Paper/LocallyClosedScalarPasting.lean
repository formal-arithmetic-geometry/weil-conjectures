/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.Paper.FiniteClosedShriek
public import Sheaf.Paper.NormalizedOriginScalarComparisons

/-! # Pasting supplied closed and open scalar comparisons

Source: Weil blueprint, sec-six-functors/sk-prop-sf-biduality-general,
lem-coef-finite-closed-shriek.md, proof paragraph 3
(blueprint: lem-coef-locally-closed-scalar-pasting).

The existing fixed-coefficient operations are reused. In contrast to the canonical
comparison in FiniteClosedShriek, the closed comparison here is supplied and is not
assumed invertible. Domains are actual full subcategories of the same ambient derived
categories. Component families only require naturality on their chosen full domains.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures.LocallyClosedScalarPasting

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Finite A] [Finite B] [Finite C]
  {W V X : Scheme.{u}} (t : W ⟶ V) (j : V ⟶ X)
  [IsClosedImmersion t] [IsOpenImmersion j]

/-- The chosen full domains, with precisely the operations needed for the paste.
Bounded constructibility is the recorded etale-origin predicate, not a replacement
for finite Tor amplitude; the domains may be any full subdomains on which the
indicated operations are defined.
Source: blueprint proof paragraph 3, chosen full domains
(blueprint: lem-coef-locally-closed-scalar-pasting). -/
structure Domains (A : Type u) [CommRing A] [Finite A] where
  onX : ObjectProperty (finiteClosedDerived X A)
  onV : ObjectProperty (finiteClosedDerived V A)
  onW : ObjectProperty (finiteClosedDerived W A)
  boundedX : ∀ K, onX K → ProEtale.DerivedCategory.boundedConstructible
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X K
  boundedV : ∀ K, onV K → ProEtale.DerivedCategory.boundedConstructible
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) V K
  boundedW : ∀ K, onW K → ProEtale.DerivedCategory.boundedConstructible
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) W K
  closedPush : ∀ K, onW K → onV ((finiteClosedPush A t).obj K)
  closedExceptional : ∀ K, onV K → onW ((finiteClosedExceptional A t).obj K)
  openPush : ∀ K, onV K → onX ((finiteClosedOpenPush A j).obj K)
  openPull : ∀ K, onX K → onV ((finiteClosedPull A j).obj K)

variable {t j}

/-- Supplied natural comparison families with the two assumed counit normalizations.
The scalar and restriction functors are the published uncompleted scalar extension
and canonical open comparison. Every arrow lies in the B-linear derived category.
No invertibility field is imposed on b.
Source: blueprint proof paragraph 3, closed and open counit hypotheses
(blueprint: lem-coef-locally-closed-scalar-pasting). -/
structure Comparison (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B)
    (dA : Domains t j A) (dB : Domains t j B) where
  scalarX : ∀ K, dA.onX K → dB.onX ((finiteClosedScalar φ X).obj K)
  scalarV : ∀ K, dA.onV K → dB.onV ((finiteClosedScalar φ V).obj K)
  scalarW : ∀ K, dA.onW K → dB.onW ((finiteClosedScalar φ W).obj K)
  b : ∀ (K : finiteClosedDerived V A) (_hK : dA.onV K),
    (finiteClosedScalar φ W).obj ((finiteClosedExceptional A t).obj K) ⟶
      (finiteClosedExceptional B t).obj ((finiteClosedScalar φ V).obj K)
  c : ∀ (K : finiteClosedDerived W A) (_hK : dA.onW K),
    (finiteClosedScalar φ V).obj ((finiteClosedPush A t).obj K) ⟶
      (finiteClosedPush B t).obj ((finiteClosedScalar φ W).obj K)
  cIso : ∀ K hK, IsIso (c K hK)
  e : ∀ (K : finiteClosedDerived V A) (_hK : dA.onV K),
    (finiteClosedScalar φ X).obj ((finiteClosedOpenPush A j).obj K) ⟶
      (finiteClosedOpenPush B j).obj ((finiteClosedScalar φ V).obj K)
  eIso : ∀ K hK, IsIso (e K hK)
  bNatural : ∀ K L (hK : dA.onV K) (hL : dA.onV L) (f : K ⟶ L),
    (finiteClosedScalar φ W).map ((finiteClosedExceptional A t).map f) ≫ b L hL =
      b K hK ≫ (finiteClosedExceptional B t).map ((finiteClosedScalar φ V).map f)
  cNatural : ∀ K L (hK : dA.onW K) (hL : dA.onW L) (f : K ⟶ L),
    (finiteClosedScalar φ V).map ((finiteClosedPush A t).map f) ≫ c L hL =
      c K hK ≫ (finiteClosedPush B t).map ((finiteClosedScalar φ W).map f)
  eNatural : ∀ K L (hK : dA.onV K) (hL : dA.onV L) (f : K ⟶ L),
    (finiteClosedScalar φ X).map ((finiteClosedOpenPush A j).map f) ≫ e L hL =
      e K hK ≫ (finiteClosedOpenPush B j).map ((finiteClosedScalar φ V).map f)
  closedCounit : ∀ K (hK : dA.onV K),
    c _ (dA.closedExceptional K hK) ≫
        (finiteClosedPush B t).map (b K hK) ≫
        finiteClosedCounit B t ((finiteClosedScalar φ V).obj K) =
      (finiteClosedScalar φ V).map (finiteClosedCounit A t K)
  openCounit : ∀ M (hM : dA.onX M),
    e _ (dA.openPull M hM) ≫
        (finiteClosedOpenPush B j).map ((finiteClosedScalarPullIso φ j).inv.app M) ≫
        (ProEtale.fixedScalarOpenAdjunction (ULift.{u + 1, u} B) j).counit.app
          ((finiteClosedScalar φ X).obj M) =
      (finiteClosedScalar φ X).map
        ((ProEtale.fixedScalarOpenAdjunction (ULift.{u + 1, u} A) j).counit.app M)

variable {φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B}
  {dA : Domains t j A} {dB : Domains t j B}

/-- The specified b_h: b_t at j^*M followed by Rt_B^! of canonical restriction.
Source: blueprint proof paragraph 3, definition of b_h
(blueprint: lem-coef-locally-closed-scalar-pasting). -/
def pastedB (q : Comparison φ dA dB) (M : finiteClosedDerived X A) (hM : dA.onX M) :
    (finiteClosedScalar φ W).obj ((finiteLocallyClosedExceptional A t j).obj M) ⟶
      (finiteLocallyClosedExceptional B t j).obj ((finiteClosedScalar φ X).obj M) :=
  q.b _ (dA.openPull M hM) ≫
    (finiteClosedExceptional B t).map ((finiteClosedScalarPullIso φ j).inv.app M)

/-- The specified c_h: open scalar comparison followed by j_! of c_t.
Source: blueprint proof paragraph 3, definition of c_h
(blueprint: lem-coef-locally-closed-scalar-pasting). -/
def pastedC (q : Comparison φ dA dB) (Q : finiteClosedDerived W A) (hQ : dA.onW Q) :
    (finiteClosedScalar φ X).obj ((finiteLocallyClosedPush A t j).obj Q) ⟶
      (finiteLocallyClosedPush B t j).obj ((finiteClosedScalar φ W).obj Q) :=
  q.e _ (dA.closedPush Q hQ) ≫ (finiteClosedOpenPush B j).map (q.c Q hQ)

/-- The canonical tensor associator in the same fixed constant-coefficient presentation.
Source: blueprint proof paragraph 3, canonical scalar associators
(blueprint: lem-coef-locally-closed-scalar-pasting). -/
def associator (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B)
    (ψ : ULift.{u + 1, u} B →+* ULift.{u + 1, u} C) (T : Scheme.{u}) :
    finiteClosedScalar φ T ⋙ finiteClosedScalar ψ T ≅
      finiteClosedScalar (ψ.comp φ) T :=
  @ProEtale.pbcFixedScalarExtensionComp.{u} T.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology T)
    _ _ _ _ _ _ φ ψ (ψ.comp φ) rfl

/-- The assumed successive-scalar cocycles, with their actual canonical tensor
associators retained rather than treated as definitional equalities.
Source: blueprint proof paragraph 3, coefficient-chain hypotheses
(blueprint: lem-coef-locally-closed-scalar-pasting). -/
structure ScalarCocycle
    {ψ : ULift.{u + 1, u} B →+* ULift.{u + 1, u} C}
    {dC : Domains t j C}
    (q : Comparison φ dA dB) (r : Comparison ψ dB dC)
    (s : Comparison (ψ.comp φ) dA dC) : Prop where
  closed : ∀ K (hK : dA.onV K),
    (finiteClosedScalar ψ W).map (q.b K hK) ≫
        r.b _ (q.scalarV K hK) ≫
        (finiteClosedExceptional C t).map ((associator φ ψ V).hom.app K) =
      (associator φ ψ W).hom.app ((finiteClosedExceptional A t).obj K) ≫ s.b K hK
  direct : ∀ Q (hQ : dA.onW Q),
    (finiteClosedScalar ψ V).map (q.c Q hQ) ≫
        r.c _ (q.scalarW Q hQ) ≫
        (finiteClosedPush C t).map ((associator φ ψ W).hom.app Q) =
      (associator φ ψ V).hom.app ((finiteClosedPush A t).obj Q) ≫ s.c Q hQ
  restriction : ∀ M (_hM : dA.onX M),
    (finiteClosedScalar ψ V).map ((finiteClosedScalarPullIso φ j).inv.app M) ≫
        (finiteClosedScalarPullIso ψ j).inv.app ((finiteClosedScalar φ X).obj M) ≫
        (finiteClosedPull C j).map ((associator φ ψ X).hom.app M) =
      (associator φ ψ V).hom.app ((finiteClosedPull A j).obj M) ≫
        (finiteClosedScalarPullIso (ψ.comp φ) j).inv.app M
  openComparison : ∀ K (hK : dA.onV K),
    (finiteClosedScalar ψ X).map (q.e K hK) ≫
        r.e _ (q.scalarV K hK) ≫
        (finiteClosedOpenPush C j).map ((associator φ ψ V).hom.app K) =
      (associator φ ψ X).hom.app ((finiteClosedOpenPush A j).obj K) ≫ s.e K hK

/-- The canonical self-extension unit, in the same fixed scalar coordinates.
Source: blueprint proof paragraph 3, identity coefficient changes
(blueprint: lem-coef-locally-closed-scalar-pasting). -/
def unitIso (A : Type u) [CommRing A] (T : Scheme.{u}) :
    finiteClosedScalar (RingHom.id (ULift.{u + 1, u} A)) T ≅ 𝟭 (finiteClosedDerived T A) :=
  @ProEtale.normalizedOriginScalarUnit.{u} T.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology T)
    _ _ (RingHom.id (ULift.{u + 1, u} A)) rfl

/-- The assumed identity normalizations for the closed and open comparison families.
Source: blueprint proof paragraph 3, identity hypotheses
(blueprint: lem-coef-locally-closed-scalar-pasting). -/
structure IdentityCocycle
    (q : Comparison (RingHom.id (ULift.{u + 1, u} A)) dA dA) : Prop where
  closed : ∀ K (hK : dA.onV K),
    q.b K hK ≫ (finiteClosedExceptional A t).map ((unitIso A V).hom.app K) =
      (unitIso A W).hom.app ((finiteClosedExceptional A t).obj K)
  direct : ∀ Q (hQ : dA.onW Q),
    q.c Q hQ ≫ (finiteClosedPush A t).map ((unitIso A W).hom.app Q) =
      (unitIso A V).hom.app ((finiteClosedPush A t).obj Q)
  restriction : ∀ M (_hM : dA.onX M),
    (finiteClosedScalarPullIso (RingHom.id (ULift.{u + 1, u} A)) j).inv.app M ≫
        (finiteClosedPull A j).map ((unitIso A X).hom.app M) =
      (unitIso A V).hom.app ((finiteClosedPull A j).obj M)
  openComparison : ∀ K (hK : dA.onV K),
    q.e K hK ≫ (finiteClosedOpenPush A j).map ((unitIso A V).hom.app K) =
      (unitIso A X).hom.app ((finiteClosedOpenPush A j).obj K)

/-- The given closed-composition cocycle, in the chained exceptional adjunction
coordinates specified by the node. Thus b_tu has target Ru_B^! Rt_B^!, rather
than an unrelated choice of a right adjoint for the composite.
Source: blueprint proof paragraph 3, composition of closed immersions
(blueprint: lem-coef-locally-closed-scalar-pasting). -/
structure ClosedCocycle {W' : Scheme.{u}} (u : W' ⟶ W) [IsClosedImmersion u]
    (q : Comparison φ dA dB) where
  onSource : ObjectProperty (finiteClosedDerived W' A)
  onTarget : ObjectProperty (finiteClosedDerived W' B)
  boundedSource : ∀ K, onSource K → ProEtale.DerivedCategory.boundedConstructible
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) W' K
  boundedTarget : ∀ K, onTarget K → ProEtale.DerivedCategory.boundedConstructible
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) W' K
  pushSource : ∀ K, onSource K → dA.onW ((finiteClosedPush A u).obj K)
  pushTarget : ∀ K, onTarget K → dB.onW ((finiteClosedPush B u).obj K)
  exceptionalSource : ∀ K, dA.onW K → onSource ((finiteClosedExceptional A u).obj K)
  exceptionalTarget : ∀ K, dB.onW K → onTarget ((finiteClosedExceptional B u).obj K)
  scalarSource : ∀ K, onSource K → onTarget ((finiteClosedScalar φ W').obj K)
  b_u : ∀ (K : finiteClosedDerived W A) (_hK : dA.onW K),
    (finiteClosedScalar φ W').obj ((finiteClosedExceptional A u).obj K) ⟶
      (finiteClosedExceptional B u).obj ((finiteClosedScalar φ W).obj K)
  b_tu : ∀ (K : finiteClosedDerived V A) (_hK : dA.onV K),
    (finiteClosedScalar φ W').obj
        ((finiteClosedExceptional A u).obj ((finiteClosedExceptional A t).obj K)) ⟶
      (finiteClosedExceptional B u).obj
        ((finiteClosedExceptional B t).obj ((finiteClosedScalar φ V).obj K))
  c_u : ∀ (Q : finiteClosedDerived W' A) (_hQ : onSource Q),
    (finiteClosedScalar φ W).obj ((finiteClosedPush A u).obj Q) ⟶
      (finiteClosedPush B u).obj ((finiteClosedScalar φ W').obj Q)
  c_tu : ∀ (Q : finiteClosedDerived W' A) (_hQ : onSource Q),
    (finiteClosedScalar φ V).obj ((finiteClosedPush A t).obj ((finiteClosedPush A u).obj Q)) ⟶
      (finiteClosedPush B t).obj ((finiteClosedPush B u).obj ((finiteClosedScalar φ W').obj Q))
  c_uIso : ∀ Q hQ, IsIso (c_u Q hQ)
  c_tuIso : ∀ Q hQ, IsIso (c_tu Q hQ)
  c_uNatural : ∀ Q R (hQ : onSource Q) (hR : onSource R) (f : Q ⟶ R),
    (finiteClosedScalar φ W).map ((finiteClosedPush A u).map f) ≫ c_u R hR =
      c_u Q hQ ≫ (finiteClosedPush B u).map ((finiteClosedScalar φ W').map f)
  c_tuNatural : ∀ Q R (hQ : onSource Q) (hR : onSource R) (f : Q ⟶ R),
    (finiteClosedScalar φ V).map
        ((finiteClosedPush A t).map ((finiteClosedPush A u).map f)) ≫ c_tu R hR =
      c_tu Q hQ ≫ (finiteClosedPush B t).map
        ((finiteClosedPush B u).map ((finiteClosedScalar φ W').map f))
  uCounit : ∀ K (hK : dA.onW K),
    c_u _ (exceptionalSource K hK) ≫ (finiteClosedPush B u).map (b_u K hK) ≫
        finiteClosedCounit B u ((finiteClosedScalar φ W).obj K) =
      (finiteClosedScalar φ W).map (finiteClosedCounit A u K)
  tuCounit : ∀ K (hK : dA.onV K),
    c_tu _ (exceptionalSource _ (dA.closedExceptional K hK)) ≫
        (finiteClosedPush B t).map ((finiteClosedPush B u).map (b_tu K hK)) ≫
        (finiteClosedPush B t).map
          (finiteClosedCounit B u ((finiteClosedExceptional B t).obj
            ((finiteClosedScalar φ V).obj K))) ≫
        finiteClosedCounit B t ((finiteClosedScalar φ V).obj K) =
      (finiteClosedScalar φ V).map
        ((finiteClosedPush A t).map
            (finiteClosedCounit A u ((finiteClosedExceptional A t).obj K)) ≫
          finiteClosedCounit A t K)
  directComp : ∀ Q (hQ : onSource Q),
    c_tu Q hQ = q.c _ (pushSource Q hQ) ≫ (finiteClosedPush B t).map (c_u Q hQ)
  uNatural : ∀ K L (hK : dA.onW K) (hL : dA.onW L) (f : K ⟶ L),
    (finiteClosedScalar φ W').map ((finiteClosedExceptional A u).map f) ≫ b_u L hL =
      b_u K hK ≫ (finiteClosedExceptional B u).map ((finiteClosedScalar φ W).map f)
  tuNatural : ∀ K L (hK : dA.onV K) (hL : dA.onV L) (f : K ⟶ L),
    (finiteClosedScalar φ W').map
        ((finiteClosedExceptional A u).map ((finiteClosedExceptional A t).map f)) ≫
        b_tu L hL = b_tu K hK ≫ (finiteClosedExceptional B u).map
          ((finiteClosedExceptional B t).map ((finiteClosedScalar φ V).map f))
  comp : ∀ K (hK : dA.onV K),
    b_tu K hK = b_u _ (dA.closedExceptional K hK) ≫
      (finiteClosedExceptional B u).map (q.b K hK)

/-- The specified locally closed paste for j(tu), using the given closed composite
and the chained exceptional adjunction identifications.
Source: blueprint proof paragraph 3, definition of b_jtu
(blueprint: lem-coef-locally-closed-scalar-pasting). -/
def pastedTripleB {W' : Scheme.{u}} {u : W' ⟶ W} [IsClosedImmersion u]
    {q : Comparison φ dA dB} (z : ClosedCocycle u q)
    (M : finiteClosedDerived X A) (hM : dA.onX M) :
    (finiteClosedScalar φ W').obj
        ((finiteClosedExceptional A u).obj ((finiteLocallyClosedExceptional A t j).obj M)) ⟶
      (finiteClosedExceptional B u).obj
        ((finiteLocallyClosedExceptional B t j).obj ((finiteClosedScalar φ X).obj M)) :=
  z.b_tu _ (dA.openPull M hM) ≫ (finiteClosedExceptional B u).map
    ((finiteClosedExceptional B t).map ((finiteClosedScalarPullIso φ j).inv.app M))

/-- Counit of the chained u_*, t_*, j_! adjunction, first composing the two closed
adjunctions and then the open adjunction. Its formula uses the actual closed counits
and the actual open adjunction, and contains no choice of a comparison arrow.
Source: blueprint proof paragraph 3; Stacks 0DV0, compose-counits
(blueprint: lem-coef-locally-closed-scalar-pasting). -/
def tripleCounit (A : Type u) [CommRing A] [Finite A]
    {W' : Scheme.{u}} (u : W' ⟶ W) [IsClosedImmersion u]
    (M : finiteClosedDerived X A) :
    (finiteClosedOpenPush A j).obj ((finiteClosedPush A t).obj
      ((finiteClosedPush A u).obj ((finiteClosedExceptional A u).obj
        ((finiteLocallyClosedExceptional A t j).obj M)))) ⟶ M :=
  (finiteClosedOpenPush A j).map
      ((finiteClosedPush A t).map
          (finiteClosedCounit A u ((finiteLocallyClosedExceptional A t j).obj M)) ≫
        finiteClosedCounit A t ((finiteClosedPull A j).obj M)) ≫
    (ProEtale.fixedScalarOpenAdjunction (ULift.{u + 1, u} A) j).counit.app M

/-- The naturality, ordinary isomorphism and locally closed counit clauses.
Source: blueprint proof paragraph 3, steps 1--3
(blueprint: lem-coef-locally-closed-scalar-pasting). -/
def PastingStatement (q : Comparison φ dA dB) : Prop :=
    (∀ M N (hM : dA.onX M) (hN : dA.onX N) (f : M ⟶ N),
      (finiteClosedScalar φ W).map
          ((finiteLocallyClosedExceptional A
            t j).map f) ≫ pastedB q N hN =
        pastedB q M hM ≫
          (finiteLocallyClosedExceptional B t j).map
            ((finiteClosedScalar φ X).map f)) ∧
    (∀ Q R (hQ : dA.onW Q) (hR : dA.onW R) (f : Q ⟶ R),
      (finiteClosedScalar φ X).map
          ((finiteLocallyClosedPush A t j).map f) ≫
          pastedC q R hR =
        pastedC q Q hQ ≫
          (finiteLocallyClosedPush B t j).map
            ((finiteClosedScalar φ W).map f)) ∧
    (∀ Q (hQ : dA.onW Q), IsIso (pastedC q Q hQ)) ∧
    (∀ M (hM : dA.onX M),
      pastedC q _ (dA.closedExceptional _ (dA.openPull M hM)) ≫
          (finiteLocallyClosedPush B t j).map
            (pastedB q M hM) ≫
          finiteLocallyClosedCounit B t j
            ((finiteClosedScalar φ X).obj M) =
        (finiteClosedScalar φ X).map
          (finiteLocallyClosedCounit A t j M))

/-- The successive-scalar clause with the actual canonical tensor associators.
Source: blueprint proof paragraph 3, step 4
(blueprint: lem-coef-locally-closed-scalar-pasting). -/
def ScalarStatement
    {ψ : ULift.{u + 1, u} B →+* ULift.{u + 1, u} C} {dC : Domains t j C}
    (q : Comparison φ dA dB) (r : Comparison ψ dB dC)
    (z : Comparison (ψ.comp φ) dA dC) : Prop :=
    ∀ M (hM : dA.onX M),
      (finiteClosedScalar ψ W).map (pastedB q M hM) ≫
          pastedB r _ (q.scalarX M hM) ≫
          (finiteLocallyClosedExceptional C t j).map
            ((associator φ ψ X).hom.app M) =
        (associator φ ψ W).hom.app
            ((finiteLocallyClosedExceptional A
              t j).obj M) ≫ pastedB z M hM

/-- The further-closed-immersion clause in the specified chained coordinates.
Source: blueprint proof paragraph 3, step 5
(blueprint: lem-coef-locally-closed-scalar-pasting). -/
def ClosedStatement {W' : Scheme.{u}} {u : W' ⟶ W} [IsClosedImmersion u]
    {q : Comparison φ dA dB} (z : ClosedCocycle u q) : Prop :=
    ∀ M (hM : dA.onX M),
      pastedTripleB z M hM =
        z.b_u _ (dA.closedExceptional _ (dA.openPull M hM)) ≫
          (finiteClosedExceptional B u).map
            (pastedB q M hM)

/-- The explicit triple composite counit formula and its other parenthesization.
Source: blueprint proof paragraph 3, step 6; Stacks 0DV0
(blueprint: lem-coef-locally-closed-scalar-pasting). -/
def TripleCounitStatement {W' : Scheme.{u}} (u : W' ⟶ W) [IsClosedImmersion u]
    (dA : Domains t j A) : Prop :=
    ∀ (M : finiteClosedDerived X A) (_hM : dA.onX M),
    tripleCounit (t := t) (j := j)
        A u M =
      (finiteClosedOpenPush A j).map
          ((finiteClosedPush A t).map
            (finiteClosedCounit A u
              ((finiteLocallyClosedExceptional A
                t j).obj M))) ≫
        finiteLocallyClosedCounit A t j M

private theorem closedCounit_naturality
    {K L : finiteClosedDerived V B}
    (hK : _root_.DerivedCategory.TStructure.t.plus K)
    (hL : _root_.DerivedCategory.TStructure.t.plus L) (f : K ⟶ L) :
    (finiteClosedPush B t).map ((finiteClosedExceptional B t).map f) ≫
        finiteClosedCounit B t L = finiteClosedCounit B t K ≫ f := by
  classical
  by_cases hV : CompactSpace V
  · let _ := hV
    let _ := (Compactification.ofIsProper t).hasCompactification
    simp only [finiteClosedCounit, dif_pos hV, dif_pos hK, dif_pos hL]
    rw [← Category.assoc,
      (ProEtale.rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) t).inv.naturality,
      Category.assoc]
    erw [ProEtale.rightDerivedUpperShriekCounit_naturality t hK hL]
    exact (Category.assoc _ _ _).symm
  · simp [finiteClosedCounit, hV]

private theorem pasting (q : Comparison φ dA dB) : PastingStatement q := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro M N hM hN f
    dsimp only [pastedB, finiteLocallyClosedExceptional, Functor.comp_map]
    rw [← Category.assoc, q.bNatural _ _ (dA.openPull M hM) (dA.openPull N hN)]
    simp only [Category.assoc]
    have hn := (finiteClosedScalarPullIso φ j).inv.naturality f
    dsimp only [Functor.comp_map] at hn
    rw [← Functor.map_comp, hn]
    simp only [Functor.map_comp]
  · intro Q R hQ hR f
    dsimp only [pastedC, finiteLocallyClosedPush, Functor.comp_map]
    rw [← Category.assoc, q.eNatural _ _ (dA.closedPush Q hQ) (dA.closedPush R hR)]
    simp only [Category.assoc]
    rw [← Functor.map_comp, q.cNatural Q R hQ hR f]
    simp only [Functor.map_comp]
  · intro Q hQ
    have := q.eIso _ (dA.closedPush Q hQ)
    have := q.cIso Q hQ
    dsimp only [pastedC]
    infer_instance
  · intro M hM
    let K := (finiteClosedPull A j).obj M
    have hK := dA.openPull M hM
    let a := (finiteClosedScalarPullIso φ j).inv.app M
    have hn := closedCounit_naturality (t := t)
      (dB.boundedV _ (q.scalarV K hK)).plusEtaleOrigin.plus
      (dB.boundedV _ (dB.openPull _ (q.scalarX M hM))).plusEtaleOrigin.plus a
    have hclosed :
        q.c _ (dA.closedExceptional K hK) ≫
            (finiteClosedPush B t).map (q.b K hK) ≫
            (finiteClosedPush B t).map ((finiteClosedExceptional B t).map a) ≫
            finiteClosedCounit B t _ =
          (finiteClosedScalar φ V).map (finiteClosedCounit A t K) ≫ a := by
      dsimp only [Functor.comp_obj]
      erw [hn]
      simpa only [Category.assoc] using
        congrArg (fun f ↦ f ≫ a) (q.closedCounit K hK)
    dsimp only [pastedC, pastedB, finiteLocallyClosedPush, Functor.comp_map,
      finiteLocallyClosedCounit]
    calc
      _ = q.e _ (dA.closedPush _ (dA.closedExceptional K hK)) ≫
          (finiteClosedOpenPush B j).map
            (q.c _ (dA.closedExceptional K hK) ≫
              (finiteClosedPush B t).map (q.b K hK) ≫
              (finiteClosedPush B t).map ((finiteClosedExceptional B t).map a) ≫
              finiteClosedCounit B t _) ≫
          (ProEtale.fixedScalarOpenAdjunction (ULift.{u + 1, u} B) j).counit.app _ := by
        simp only [K, a, Functor.comp_obj, Functor.map_comp, Category.assoc]
      _ = q.e _ (dA.closedPush _ (dA.closedExceptional K hK)) ≫
          (finiteClosedOpenPush B j).map
            ((finiteClosedScalar φ V).map (finiteClosedCounit A t K) ≫ a) ≫
          (ProEtale.fixedScalarOpenAdjunction (ULift.{u + 1, u} B) j).counit.app _ := by
        rw [hclosed]
      _ = (finiteClosedScalar φ X).map
          ((finiteClosedOpenPush A j).map (finiteClosedCounit A t K)) ≫
          (q.e K hK ≫ (finiteClosedOpenPush B j).map a ≫
            (ProEtale.fixedScalarOpenAdjunction (ULift.{u + 1, u} B) j).counit.app _) := by
        simp only [Functor.map_comp, Category.assoc]
        rw [← Category.assoc, ← Category.assoc,
          ← q.eNatural _ K (dA.closedPush _ (dA.closedExceptional K hK)) hK
            (finiteClosedCounit A t K)]
        simp only [Category.assoc]
      _ = _ := by
        rw [q.openCounit M hM, ← Functor.map_comp]

private theorem scalar
    {ψ : ULift.{u + 1, u} B →+* ULift.{u + 1, u} C} {dC : Domains t j C}
    (q : Comparison φ dA dB) (r : Comparison ψ dB dC)
    (z : Comparison (ψ.comp φ) dA dC) (hc : ScalarCocycle q r z) :
    ScalarStatement q r z := by
  intro M hM
  dsimp only [pastedB, finiteLocallyClosedExceptional, Functor.comp_obj, Functor.comp_map]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (r.bNatural _ _ (q.scalarV _ (dA.openPull M hM))
    (dB.openPull _ (q.scalarX M hM)) ((finiteClosedScalarPullIso φ j).inv.app M))]
  rw [← Functor.map_comp, ← Functor.map_comp, hc.restriction M hM, Functor.map_comp]
  simpa only [Category.assoc] using
    congrArg (fun f ↦ f ≫ (finiteClosedExceptional C t).map
      ((finiteClosedScalarPullIso (ψ.comp φ) j).inv.app M))
      (hc.closed _ (dA.openPull M hM))

private theorem closed {W' : Scheme.{u}} {u : W' ⟶ W} [IsClosedImmersion u]
    {q : Comparison φ dA dB} (z : ClosedCocycle u q) : ClosedStatement z := by
  intro M hM
  dsimp only [pastedTripleB, pastedB]
  rw [z.comp _ (dA.openPull M hM), Functor.map_comp, Category.assoc]

private theorem triple (R : Type u) [CommRing R] [Finite R]
    {W' : Scheme.{u}} (u : W' ⟶ W) [IsClosedImmersion u]
    (dR : Domains t j R) : TripleCounitStatement u dR := by
  intro M _
  simp only [tripleCounit, finiteLocallyClosedCounit, Functor.map_comp, Category.assoc]

section FiniteStages

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E L : Type u) [Field E] [Field L]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (m n : ℕ)
  (X V W : Over (Spec (CommRingCat.of D.k)))
  [sepX : IsSeparated X.hom] [ftX : LocallyOfFiniteType X.hom] [qcX : QuasiCompact X.hom]
  [sepV : IsSeparated V.hom] [ftV : LocallyOfFiniteType V.hom] [qcV : QuasiCompact V.hom]
  [sepW : IsSeparated W.hom] [ftW : LocallyOfFiniteType W.hom] [qcW : QuasiCompact W.hom]
  (t : W ⟶ V) (j : V ⟶ X) [IsClosedImmersion t.left] [IsOpenImmersion j.left]
  (φ : ULift.{u + 1, u} (finiteClosedCoefficient l E m) →+*
    ULift.{u + 1, u} (finiteClosedCoefficient l L n))
  (dA : Domains t.left j.left (finiteClosedCoefficient l E m))
  (dB : Domains t.left j.left (finiteClosedCoefficient l L n))
  (q : Comparison φ dA dB)

include hl sepX ftX qcX sepV ftV qcV sepW ftW qcW

variable (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
  (s : ℕ) (ψ : ULift.{u + 1, u} (finiteClosedCoefficient l L n) →+*
    ULift.{u + 1, u} (finiteClosedCoefficient l F s))
  (dC : Domains t.left j.left (finiteClosedCoefficient l F s))
  (r : Comparison ψ dB dC) (z : Comparison (ψ.comp φ) dA dC)

variable (W' : Over (Spec (CommRingCat.of D.k)))
  [sepW' : IsSeparated W'.hom] [ftW' : LocallyOfFiniteType W'.hom]
  [qcW' : QuasiCompact W'.hom]
  (u : W' ⟶ W) [IsClosedImmersion u.left]

include sepW' ftW' qcW'

set_option linter.unusedSectionVars false in
/-- Pasting supplied closed and open coefficient comparisons preserves naturality,
the ordinary isomorphism, the actual composite exceptional counit,
successive coefficients and further closed composition. All operations act on the
chosen full bounded constructible domains of etale origin. No exceptional b is
assumed or concluded invertible.

Source: Weil blueprint, sec-six-functors/sk-prop-sf-biduality-general,
lem-coef-finite-closed-shriek.md, proof paragraph 3
(blueprint: lem-coef-locally-closed-scalar-pasting).

Proof, following the six steps of the DAG:
1. Expand pastedB and pastedC. Naturality of r_j followed by b_t gives the first
naturality equation; naturality of c_t and e_j gives the second. The inverse of
c_h is j_!(c_t^{-1}) followed by e_j^{-1}, so precisely the ordinary map is invertible.
2. Put K=j_A^*M and N=Rt_A^!K. Expand epsilon_h using
 def-weil-pbc-composite-adjunction. Naturality of epsilon_t at r_j moves that
arrow past epsilon_t. Substitute the assumed closed counit equation at K.
3. Naturality of e_j at epsilon_t moves scalar extension of that counit past
e_j. The assumed open counit equation gives scalar extension of epsilon_j
composed after j_!epsilon_t, which is exactly scalar extension of epsilon_h.
4. Expand the A-to-C comparison using the two assumed cocycles. Naturality of
the B-to-C b_t at the A-to-B r_j interchanges the two middle factors, giving
the asserted scalar-chain equation with exactly the input tensor associators.
5. Substitute the assumed closed-composition cocycle at j_A^*M. Functoriality
of Ru_B^! collects its last two factors as Ru_B^!(b_jt). For identity change,
substitute the restriction and closed identity normalizations using the
canonical self-extension units; no definitional identity of scalar functors is used.
6. Apply the composite-adjunction counit formula first to u_* and t_*, then to
j_!. The result is tripleCounit. Applying it in the other order gives
j_!t_*(epsilon_u) followed by epsilon_jt. Functoriality and associativity
identify both with epsilon_j after j_!epsilon_t after j_!t_*epsilon_u.
Every calculation uses actual B-linear arrows, and none cancels or inverts b.
-/
theorem locallyClosedScalarPasting
    (qid : Comparison (RingHom.id (ULift.{u + 1, u} (finiteClosedCoefficient l E m))) dA dA)
    (_hi : IdentityCocycle qid) (_hc : ScalarCocycle q r z)
    (cu : ClosedCocycle u.left q) :
    PastingStatement q ∧ ScalarStatement q r z ∧
      ClosedStatement cu ∧
      (TripleCounitStatement u.left dA ∧ TripleCounitStatement u.left dB) := by
  exact ⟨pasting q, scalar q r z _hc, closed cu, triple _ u.left dA, triple _ u.left dB⟩

end FiniteStages

end WeilConjectures.LocallyClosedScalarPasting
