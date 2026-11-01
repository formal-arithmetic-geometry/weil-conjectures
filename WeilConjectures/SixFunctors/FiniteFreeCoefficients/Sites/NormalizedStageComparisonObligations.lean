/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData

/-! # Separate invertibility and coherence obligations for the fixed stage comparisons

The arrows in these propositions are the published counit and evaluation transposes.
The records contain proofs only; neither changes a functor nor chooses a comparison map.
Source: blueprint latest, lem-coef-finite-free-extension.proof.md, paragraphs 1--3.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.FiniteCoefficientAdjoints
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients.Sites

/-- The stage closed comparison is the etale counit transpose or its fixed site transport.
Source: blueprint latest, lem-coef-finite-free-extension.proof.md, paragraphs 1 and 3.
(blueprint: def-sf-normalized-stage-comparison-obligations). -/
def stageClosedMap (pro : Bool) {l : ℕ} [Fact l.Prime]
    {E : Type (u + 1)} [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {s t : Stage l E} (a : Arrow s t)
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (M : D pro s.ring X) :
    (scalar pro a.ringMap Z).obj ((exceptional pro s.ring i).obj M) ⟶
      (exceptional pro t.ring i).obj ((scalar pro a.ringMap X).obj M) := by
  cases pro
  · exact FiniteFreeCoefficients.closedMap a.ringMap i M
  · exact proClosedMap a.ringMap i M

/-- The stage dualizing comparison is the etale compact-support transpose or its transport.
Source: blueprint latest, lem-coef-finite-free-extension.proof.md, paragraphs 1 and 3.
(blueprint: def-sf-normalized-stage-comparison-obligations). -/
def stageOmegaMap (pro : Bool) {l : ℕ} [Fact l.Prime]
    {E : Type (u + 1)} [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {s t : Stage l E} (a : Arrow s t)
    {X S : Scheme.{u}} {aX : X ⟶ S} (c : Compactification aX) :
    (scalar pro a.ringMap X).obj (omega pro s.ring c) ⟶ omega pro t.ring c := by
  cases pro
  · exact FiniteFreeCoefficients.omegaMap a.ringMap c
  · exact proOmegaMap a.ringMap c

/-- Pointwise invertibility of the remaining geometric stage comparisons.
Source: blueprint latest, lem-coef-finite-free-extension.proof.md.
(blueprint: def-sf-normalized-stage-comparison-obligations). -/
structure StageComparisonIsomorphisms (pro : Bool)
    (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T X Z S : Scheme.{u}} (f : T ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    {aX : X ⟶ S} (c : Compactification aX)
    (μ : ∀ {s t : Stage l E} (a : Arrow s t), TensorComparison pro a.ringMap X) : Prop where
  closed_iso : ∀ {s t : Stage l E} (a : Arrow s t) (M : D pro s.ring X),
    Ctf pro s.ring X M → IsIso (stageClosedMap pro a i M)
  omega_iso : ∀ {s t : Stage l E} (a : Arrow s t), IsIso (stageOmegaMap pro a c)
  hom_iso : ∀ {s t : Stage l E} (a : Arrow s t) (K M : D pro s.ring X),
    Ctf pro s.ring X K → Ctf pro s.ring X M →
      IsIso (homMap pro a.ringMap X (μ a) K M)
  omega_ctf : ∀ s : Stage l E, Ctf pro s.ring X (omega pro s.ring c)

/-- Invertibility needed to compare the fixed etale and transported pro-etale arrows.
Source: blueprint latest, lem-coef-finite-free-extension.proof.md.
(blueprint: def-sf-normalized-stage-comparison-obligations). -/
structure StageComparisonSiteIsomorphisms
    (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T X Z S : Scheme.{u}} (f : T ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    {aX : X ⟶ S} (c : Compactification aX)
    [HasCompactification aX] : Prop where
  compact_support_iso : ∀ {s t : Stage l E} (a : Arrow s t),
    IsIso (Etale.ExceptionalCoefficients.compactSupportMap a.ringMap
      (HasCompactification.compactification aX)
      (FiniteFreeCoefficients.omega s.ring c))
  closed_direct_iso : ∀ {s t : Stage l E} (a : Arrow s t) (M : Cat s.ring X),
    FiniteFreeCoefficients.Ctf s.ring X M →
      IsIso (Etale.finiteCoefficientDirectImageMap a.ringMap i ((closedUpper s.ring i).obj M))
  hom_site_iso : ∀ (s : Stage l E) (K M : Cat s.ring X),
    FiniteFreeCoefficients.Ctf s.ring X K → FiniteFreeCoefficients.Ctf s.ring X M →
      IsIso (siteHom s.ring X K M)

/-- The four site squares for the canonical closed, dualizing, Hom and Verdier maps.
Source: blueprint latest, lem-coef-finite-free-extension.proof.md.
(blueprint: def-sf-normalized-stage-comparison-obligations). -/
structure StageComparisonSiteEquations
    (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T X Z S : Scheme.{u}} (f : T ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    {aX : X ⟶ S} (c : Compactification aX)
    (μet : ∀ {s t : Stage l E} (a : Arrow s t), TensorComparison false a.ringMap X)
    (μpro : ∀ {s t : Stage l E} (a : Arrow s t), TensorComparison true a.ringMap X) : Prop where
  closed_site : ∀ {s t : Stage l E} (a : Arrow s t) (M : Cat s.ring X),
    FiniteFreeCoefficients.Ctf s.ring X M →
      (scalar true a.ringMap Z).map (closedBridge s.ring i M) ≫
        stageClosedMap true a i ((nu s.ring X).obj M) ≫
          (exceptional true t.ring i).map ((scalarSite a.ringMap X).hom.app M) =
      (scalarSite a.ringMap Z).hom.app ((closedUpper s.ring i).obj M) ≫
        (nu t.ring Z).map (stageClosedMap false a i M) ≫
          closedBridge t.ring i ((Etale.scalarExtension a.ringMap X).obj M)
  omega_site : ∀ {s t : Stage l E} (a : Arrow s t),
    (scalar true a.ringMap X).map (omegaBridge s.ring c) ≫ stageOmegaMap true a c =
      (scalarSite a.ringMap X).hom.app
          (FiniteFreeCoefficients.omega s.ring c) ≫
        (nu t.ring X).map (stageOmegaMap false a c) ≫ omegaBridge t.ring c
  hom_site : ∀ {s t : Stage l E} (a : Arrow s t) (K M : Cat s.ring X),
    FiniteFreeCoefficients.Ctf s.ring X K → FiniteFreeCoefficients.Ctf s.ring X M →
      (scalar true a.ringMap X).map
          (siteHom s.ring X K M) ≫
        homMap true a.ringMap X (μpro a) ((nu s.ring X).obj K) ((nu s.ring X).obj M) ≫
        homAction (hom true t.ring X)
          ((scalarSite a.ringMap X).inv.app K)
          ((scalarSite a.ringMap X).hom.app M) =
      (scalarSite a.ringMap X).hom.app
          (((hom false s.ring X).obj (op K)).obj M) ≫
        (nu t.ring X).map (homMap false a.ringMap X (μet a) K M) ≫
        siteHom t.ring X
          ((Etale.scalarExtension a.ringMap X).obj K) ((Etale.scalarExtension a.ringMap X).obj M)
  dual_site : ∀ {s t : Stage l E} (a : Arrow s t) (K : Cat s.ring X),
    FiniteFreeCoefficients.Ctf s.ring X K →
      (scalar true a.ringMap X).map (dualBridge s.ring c K) ≫
        dualMap true a.ringMap c (μpro a) (stageOmegaMap true a c)
          ((nu s.ring X).obj K) ≫
        (dual true t.ring c).map
          ((scalarSite a.ringMap X).inv.app K).op =
      (scalarSite a.ringMap X).hom.app
          ((FiniteFreeCoefficients.dual s.ring c).obj (op K)) ≫
        (nu t.ring X).map
          (dualMap false a.ringMap c (μet a) (stageOmegaMap false a c) K) ≫
        dualBridge t.ring c ((Etale.scalarExtension a.ringMap X).obj K)

end WeilConjectures.FiniteFreeCoefficients.Sites
