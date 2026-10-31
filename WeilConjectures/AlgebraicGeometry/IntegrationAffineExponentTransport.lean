/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegrationExponentTransposeData
import WeilConjectures.AlgebraicGeometry.OrderedAffineTraceExponent
import WeilConjectures.AlgebraicGeometry.OrderedIntegrationComparison

/-! # Affine exponent transport from projective trace transport

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
thm-amb-vector-bundle-purity.proof.md, paragraph 2; accepted parent proof, Steps 8--9;
Stacks Project, Tag 0B65, lemma-transformation-between-functors-and-adjoints.
(blueprint: lem-pur-affine-exponent-transport)
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

/-- The projective exponent equations on every Noetherian base imply the two actual
open-chart trace equations and both ordered affine counit equations at every tower length.
Source: blueprint latest, thm-amb-vector-bundle-purity.proof.md, paragraph 2;
accepted parent proof Steps 8--9; Stacks Project Tag 0B65.
(blueprint: lem-pur-affine-exponent-transport)

Proof:
1. Apply ordinary open-counit naturality to the shifted line transition, then apply
pushforward and compose with the ordinary projective inverse-trace equation at S.
2. Identify the inverses of the two projective isomorphisms supplied by the hypothesis
with the canonical projective trace arrows. Apply pro-etale open-counit naturality and
compose with the supplied pro-etale projective inverse-trace equation.
3. Specialize affineTraceCounit_exponentTransition to the canonical projective trace
transport and data at r and s. This gives the ordered ordinary equation at every tower
length. Apply the comparison functor and orderedIntegration_comparison to obtain the
compared pro-etale equation. -/
theorem integrationAffineExponentTransport
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (h : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (l : Γ(T, ⊤))),
      IntegrationProjectiveEquations l E n T hT r s hrs hr hs) :
    IntegrationAffineEquations l E n S hS r s hrs hr hs := by
  let A := Scheme.finiteTateCoefficient l E n
  let j := ProjectiveLine.affineChart S
  let v := (integrationLineTransition l E n (ProjectiveLine S)
    (by simpa using hS.map (ProjectiveLine S ↘ S).appTop.hom)
    r s hrs hr hs).hom
  have ht (d : ℕ) :
      (Etale.affineTraceLeft A S d).map
        (integrationTowerTransition l E n S hS r s hrs hr hs d).hom ≫
        integrationOrdinaryOrdered l E n S hS r hr d =
      integrationOrdinaryOrdered l E n S hS s hs d := by
    unfold integrationOrdinaryOrdered integrationTowerTransition
    exact affineTraceCounit_exponentTransition l E n S hS r s hrs hr hs
      (Etale.projectiveLineTraceTransport _ (pow_pos (Fact.out : l.Prime).pos _) _ hr)
      (fun Y _ hY ↦ Etale.projectiveLineTraceDatum _
        (pow_pos (Fact.out : l.Prime).pos _) _ hr Y hY)
      (Etale.projectiveLineTraceTransport _ (pow_pos (Fact.out : l.Prime).pos _) _ hs)
      (fun Y _ hY ↦ Etale.projectiveLineTraceDatum _
        (pow_pos (Fact.out : l.Prime).pos _) _ hs Y hY) d
  refine ⟨?_, ?_, fun d ↦ ⟨ht d, ?_⟩⟩
  · let a := (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j).ofNatIsoRight
        (Etale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} A) j).symm
    have hn := a.counit.naturality v
    simp only [Functor.comp_map, Functor.id_map] at hn
    unfold kummerTraceEtaleAffine kummerTraceEtaleOpenCounit
    rw [← Functor.map_comp_assoc, hn]
    simp only [Functor.map_comp, Category.assoc]
    rw [(h S hS).1.2.2]
  · obtain ⟨br, bs, hbr, hbs, hp⟩ := (h S hS).2
    let := projectiveB_isIso l E n S hS (infinityCartier S) r hr
    let := projectiveB_isIso l E n S hS (infinityCartier S) s hs
    have htr : projectiveTrace l E n S hS (infinityCartier S) r hr =
        br.inv ≫ biprod.snd := by
      unfold projectiveTrace
      change (asIso (projectiveB l E n S hS (infinityCartier S) r hr)).inv ≫
        biprod.snd = br.inv ≫ biprod.snd
      have he : asIso (projectiveB l E n S hS (infinityCartier S) r hr) = br :=
        Iso.ext hbr.symm
      rw [he]
    have hts : projectiveTrace l E n S hS (infinityCartier S) s hs =
        bs.inv ≫ biprod.snd := by
      unfold projectiveTrace
      change (asIso (projectiveB l E n S hS (infinityCartier S) s hs)).inv ≫
        biprod.snd = bs.inv ≫ biprod.snd
      have he : asIso (projectiveB l E n S hS (infinityCartier S) s hs) = bs :=
        Iso.ext hbs.symm
      rw [he]
    have hn := (openAdjunction A j).counit.naturality
      ((comparison A (ProjectiveLine S)).map v)
    simp only [Functor.comp_map, Functor.id_map] at hn
    unfold kummerTraceProAffine
    rw [htr, hts, ← Functor.map_comp_assoc, hn]
    simp only [Functor.map_comp, Category.assoc]
    rw [hp.2.2]
  · rw [orderedIntegration_comparison, orderedIntegration_comparison]
    simpa only [A, Functor.map_comp, integrationOrdinaryOrdered, Etale.affineTraceCounit] using
      congrArg ((comparison A S).map) (ht d)

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
