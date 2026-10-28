/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G9
-/
module

public import Sheaf.SixFunctors.IntegralBrownAdjoint
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.Paper.RestrictionLocal
import Sheaf.SixFunctors.IntegralRestrictionLine
import Sheaf.SixFunctors.IntegralRestrictionClosed
import Sheaf.Paper.MateOpenRestriction
import Sheaf.SixFunctors.CompactificationOverBase
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Adjunction.Restrict

/-! # Finite-open descent for integral restriction

Source: blueprint main-20261015, sk-thm-int-restriction-glue.proof.md,
expanded by det-thm-int-restriction-glue.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.IntegralRestriction

private def space (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] : Spaces k :=
  ⟨Over.mk (X ↘ Spec (.of k)),
    (show IsSeparated (X ↘ Spec (.of k)) from inferInstance),
    (show LocallyOfFiniteType (X ↘ Spec (.of k)) from inferInstance),
    (show QuasiCompact (X ↘ Spec (.of k)) from inferInstance)⟩

private def pullLift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ K, localizing Λ Y K → localizing Λ X ((pull Λ f).obj K)) :
    (localizing Λ Y).FullSubcategory ⥤ (localizing Λ X).FullSubcategory :=
  (localizing Λ X).lift ((localizing Λ Y).ι ⋙ pull Λ f)
    (fun K ↦ h K.obj K.property)

private def openAdj
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j]
    (h : ∀ K, localizing Λ X K → localizing Λ Y
      ((image Λ (Compactification.ofIsOpenImmersion j)).obj K))
    (hp : ∀ K, localizing Λ Y K → localizing Λ X ((pull Λ j).obj K)) :
    lowerShriek Λ (Compactification.ofIsOpenImmersion j) h ⊣ pullLift Λ j hp := by
  let a := (openAdjunction Λ j).ofNatIsoLeft (mateOpenTrivialLowerShriek Λ j).symm
  exact a.restrictFullyFaithful (ObjectProperty.fullyFaithfulι _)
    (ObjectProperty.fullyFaithfulι _)
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; simp; rfl))
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; simp; rfl))

private theorem pull_generators
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (K : Ambient (Profinite.padicIntegersRingObj ℓ E.val) Y)
    (hK : generators (Profinite.padicIntegersRingObj ℓ E.val) Y K) :
    generators (Profinite.padicIntegersRingObj ℓ E.val) X
      ((pull (Profinite.padicIntegersRingObj ℓ E.val) f).obj K) := by
  obtain ⟨h, φ, μ, hc⟩ := integralLocalizingCompactSupport ℓ E k
  exact hc.constructible_pull
    (X := space k X) (Y := space k Y)
    (ObjectProperty.homMk (f.asOver (Spec (.of k)))) K hK

private theorem boundedConstructible_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} {K L : Ambient Λ X}
    (e : K ≅ L) (hK : generators Λ X K) : generators Λ X L := by
  refine ⟨(DerivedCategory.TStructure.t.bounded).prop_of_iso e hK.1, ?_⟩
  intro n
  let eh := (DerivedCategory.homologyFunctor _ n).mapIso e
  have hi {X : Scheme.{u}}
      {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
      (e : M ≅ N) (hM : IsFiniteConstantStratified Λ X M) :
      IsFiniteConstantStratified Λ X N := by
    obtain ⟨S, hS⟩ := hM
    refine ⟨S, fun a ↦ ?_⟩
    obtain ⟨U, hU⟩ := hS a
    refine ⟨U, fun b ↦ ?_⟩
    obtain ⟨P, hP, ⟨eP⟩⟩ := hU b
    exact ⟨P, hP, ⟨((upperStar Λ (U.f b)).mapIso
      ((upperStar Λ (S.immersion a)).mapIso e)).symm ≪≫ eP⟩⟩
  have hk := hK.2 n
  unfold IsConstantModelConstructible at hk ⊢
  by_cases hqc : CompactSpace X ∧ QuasiSeparatedSpace X
  · rw [if_pos hqc] at hk ⊢
    exact hi eh hk
  · rw [if_neg hqc] at hk ⊢
    intro U hU
    exact hi ((upperStar Λ U.ι).mapIso eh) (hk U hU)

private theorem brown_exists
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (c : Compactification.BoundaryCompactification f) :
    ∃ (h : ∀ K, localizing (Profinite.padicIntegersRingObj ℓ E.val) X K →
      localizing (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((image (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj).obj K))
      (G : (localizing (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory ⥤
        (localizing (Profinite.padicIntegersRingObj ℓ E.val) X).FullSubcategory),
      Nonempty (lowerShriek (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj h ⊣ G) := by
  obtain ⟨_, _, h, hX, hY, hb⟩ := exists_integralBrownAdjoint ℓ E k f c
  let := hX
  let := hY
  obtain ⟨G, s, hs⟩ := hb
  let := s
  obtain ⟨_, adj, _⟩ := hs
  exact ⟨h, G, ⟨adj⟩⟩


private def lowerCompIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (k : Type u) [Field k] (μ : Compositions Λ k)
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    (c : Compactification.BoundaryCompactification f)
    (d : Compactification.BoundaryCompactification g)
    (e : Compactification.BoundaryCompactification (f ≫ g))
    (hf : ∀ K, localizing Λ X K → localizing Λ Y ((image Λ c.obj.obj).obj K))
    (hg : ∀ K, localizing Λ Y K → localizing Λ Z ((image Λ d.obj.obj).obj K))
    (hgf : ∀ K, localizing Λ X K → localizing Λ Z ((image Λ e.obj.obj).obj K)) :
    lowerShriek Λ c.obj.obj hf ⋙ lowerShriek Λ d.obj.obj hg ≅
      lowerShriek Λ e.obj.obj hgf := by
  let f' : space k X ⟶ space k Y := ObjectProperty.homMk (f.asOver (Spec (.of k)))
  let g' : space k Y ⟶ space k Z := ObjectProperty.homMk (g.asOver (Spec (.of k)))
  let e0 := μ f' g' c.obj d.obj e.obj
  refine NatIso.ofComponents (fun K ↦ (localizing Λ Z).isoMk (e0.app K)) ?_
  intro K L m
  apply ObjectProperty.hom_ext
  exact e0.hom.naturality m


private theorem image_localizing
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (k : Type u) [Field k] (h : Preservation Λ k)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (c : Compactification.BoundaryCompactification f) :
    ∀ K, localizing Λ X K → localizing Λ Y ((image Λ c.obj.obj).obj K) := by
  exact h.maps_localizing (X := space k X) (Y := space k Y)
    (f := ObjectProperty.homMk (f.asOver (Spec (.of k)))) c.obj

private theorem pull_localizing
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (k : Type u) [Field k] {h : Preservation Λ k} {φ : Comparisons Λ k}
    {μ : Compositions Λ k} (hc : Coherence Λ k h φ μ)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] :
    ∀ K, localizing Λ Y K → localizing Λ X ((pull Λ f).obj K) := by
  exact hc.localizing_pull (X := space k X) (Y := space k Y)
    (ObjectProperty.homMk (f.asOver (Spec (.of k))))

private theorem affine_preserves
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] (d : ℕ)
    (c : Compactification.BoundaryCompactification (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y))
    (h : ∀ K, localizing (Profinite.padicIntegersRingObj ℓ E.val)
        (AffineSpace (ULift.{u} (Fin d)) Y) K →
      localizing (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((image (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj).obj K))
    (G : (localizing (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory ⥤
      (localizing (Profinite.padicIntegersRingObj ℓ E.val)
        (AffineSpace (ULift.{u} (Fin d)) Y)).FullSubcategory)
    (adj : lowerShriek (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj h ⊣ G)
    (K : (localizing (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory)
    (hK : generators (Profinite.padicIntegersRingObj ℓ E.val) Y K.obj) :
    generators (Profinite.padicIntegersRingObj ℓ E.val)
      (AffineSpace (ULift.{u} (Fin d)) Y) (G.obj K).obj := by
  obtain ⟨hq, hp, hr, _, _, hb, _, hpres⟩ :=
    CondensedRing.IntegralRestriction.integralRestrictionLine ℓ E k Y d
  obtain ⟨e⟩ := hb c h G ⟨adj⟩
  exact boundedConstructible_iso _
    (((localizing (Profinite.padicIntegersRingObj ℓ E.val) _).ι).mapIso (e.app K)).symm
    (hpres K.obj hK)

private theorem closed_preserves
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsClosedImmersion f]
    (c : Compactification.BoundaryCompactification f)
    (h : ∀ K, localizing (Profinite.padicIntegersRingObj ℓ E.val) X K →
      localizing (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((image (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj).obj K))
    (G : (localizing (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory ⥤
      (localizing (Profinite.padicIntegersRingObj ℓ E.val) X).FullSubcategory)
    (adj : lowerShriek (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj h ⊣ G)
    (K : (localizing (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory)
    (hK : generators (Profinite.padicIntegersRingObj ℓ E.val) Y K.obj) :
    generators (Profinite.padicIntegersRingObj ℓ E.val) X (G.obj K).obj := by
  obtain ⟨hadd, hgen, hpres, hcomp⟩ := integralRestrictionClosed ℓ E k f
  let := hadd
  obtain ⟨e⟩ := hcomp c h G adj
  exact boundedConstructible_iso _ (e.app ⟨K.obj, hK⟩).symm (hpres K.obj hK)


private theorem local_preserves
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y U V : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [U.Over (Spec (.of k))] [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (c : Compactification.BoundaryCompactification f)
    (h : ∀ K, localizing (Profinite.padicIntegersRingObj ℓ E.val) X K →
      localizing (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((image (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj).obj K))
    (G : (localizing (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory ⥤
      (localizing (Profinite.padicIntegersRingObj ℓ E.val) X).FullSubcategory)
    (adj : lowerShriek (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj h ⊣ G)
    (u : U ⟶ X) [IsOpenImmersion u] [QuasiCompact u] [u.IsOver (Spec (.of k))]
    (v : V ⟶ Y) [IsOpenImmersion v] [QuasiCompact v] [v.IsOver (Spec (.of k))]
    (d : ℕ) (i : U ⟶ AffineSpace (ULift.{u} (Fin d)) V)
    [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
    (hgeom : (i ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V)) ≫ v = u ≫ f)
    (K : (localizing (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory)
    (hK : generators (Profinite.padicIntegersRingObj ℓ E.val) Y K.obj) :
    generators (Profinite.padicIntegersRingObj ℓ E.val) U
      ((pull (Profinite.padicIntegersRingObj ℓ E.val) u).obj (G.obj K).obj) := by
  let Λ := Profinite.padicIntegersRingObj ℓ E.val
  let P := AffineSpace (ULift.{u} (Fin d)) V
  let p : P ⟶ V := P ↘ V
  obtain ⟨h0, φ, μ, hc⟩ := integralLocalizingCompactSupport ℓ E k
  have : IsSeparated (P ↘ Spec (.of k)) :=
    (show IsSeparated (p ≫ (V ↘ Spec (.of k))) from inferInstance)
  have : LocallyOfFiniteType (P ↘ Spec (.of k)) :=
    (show LocallyOfFiniteType (p ≫ (V ↘ Spec (.of k))) from inferInstance)
  have : QuasiCompact (P ↘ Spec (.of k)) :=
    (show QuasiCompact (p ≫ (V ↘ Spec (.of k))) from inferInstance)
  obtain ⟨ci⟩ := AlgebraicGeometry.compactification_over_base (S := Spec (.of k)) i
  obtain ⟨cp⟩ := AlgebraicGeometry.compactification_over_base (S := Spec (.of k)) p
  obtain ⟨cq⟩ := AlgebraicGeometry.compactification_over_base (S := Spec (.of k)) (i ≫ p)
  let cu : Compactification.BoundaryCompactification u :=
    ⟨⟨Compactification.ofIsOpenImmersion u, (show QuasiCompact u from inferInstance)⟩⟩
  let cv : Compactification.BoundaryCompactification v :=
    ⟨⟨Compactification.ofIsOpenImmersion v, (show QuasiCompact v from inferInstance)⟩⟩
  let cuf : Compactification.BoundaryCompactification (u ≫ f) :=
    ⟨⟨c.obj.obj.precomp u, (c.obj.obj.precomp u).quasiCompact_openImmersion inferInstance⟩⟩
  let cr : Compactification.BoundaryCompactification ((i ≫ p) ≫ v) :=
    ⟨⟨cuf.obj.obj.copy hgeom,
      (cuf.obj.obj.copy hgeom).quasiCompact_openImmersion inferInstance⟩⟩
  obtain ⟨hi, Gi, ⟨ai⟩⟩ := brown_exists ℓ E k i ci
  obtain ⟨hp, Gp, ⟨ap⟩⟩ := brown_exists ℓ E k p cp
  let hu := image_localizing Λ k h0 u cu
  let hv := image_localizing Λ k h0 v cv
  let hq := image_localizing Λ k h0 (i ≫ p) cq
  let huf := image_localizing Λ k h0 (u ≫ f) cuf
  let hr := image_localizing Λ k h0 ((i ≫ p) ≫ v) cr
  let pu := pull_localizing Λ k hc u
  let pv := pull_localizing Λ k hc v
  let au := openAdj Λ u hu pu
  let av := openAdj Λ v hv pv
  let eu : lowerShriek Λ cu.obj.obj hu ⋙ lowerShriek Λ c.obj.obj h ≅
      lowerShriek Λ cr.obj.obj hr :=
    lowerCompIso Λ k μ u f cu c cuf hu h huf
  let eip := lowerCompIso Λ k μ i p ci cp cq hi hp hq
  let eipv := lowerCompIso Λ k μ (i ≫ p) v cq cv cr hq hv hr
  let eleft := (Functor.isoWhiskerRight eip (lowerShriek Λ cv.obj.obj hv)) ≪≫ eipv ≪≫ eu.symm
  let ac := ((ai.comp ap).comp av).ofNatIsoLeft eleft
  let er := (au.comp adj).rightAdjointUniq ac
  have hV : generators Λ V ((pullLift Λ v pv).obj K).obj :=
    pull_generators ℓ E k v K.obj hK
  have hP : generators Λ P (Gp.obj ((pullLift Λ v pv).obj K)).obj :=
    affine_preserves ℓ E k V d cp hp Gp ap _ hV
  have hU := closed_preserves ℓ E k i ci hi Gi ai _ hP
  exact boundedConstructible_iso Λ
    (((localizing Λ U).ι).mapIso (er.app K)).symm hU


private theorem affineCharts
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (c : Compactification.BoundaryCompactification f) :
    ∃ (n : ℕ) (U : Fin n → Scheme.{u}) (u : ∀ a, U a ⟶ X),
      (∀ a, IsAffine (U a) ∧ IsOpenImmersion (u a)) ∧
      (∀ x : X, ∃ a : Fin n, ∃ y : U a, (u a).base y = x) ∧
      (∀ a, ∃ (V : Scheme.{u}) (v : V ⟶ Y),
        IsAffine V ∧ IsOpenImmersion v ∧
        ∃ (d : ℕ) (i : U a ⟶ AffineSpace (ULift.{u} (Fin d)) V)
          (_hi : IsClosedImmersion i) (q : U a ⟶ V),
          i ≫ (AffineSpace.over (ULift.{u} (Fin d)) V).hom = q ∧ q ≫ v = u a ≫ f) := by
  let Λ := Profinite.continuousMapRingObj E.val
  have hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ :=
    Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩)))
  obtain ⟨h, hX, hY, hc⟩ := exists_localizingExceptionalAdjoint Λ ℓ k f c hΛ
  let := hX
  let := hY
  obtain ⟨_, _, _, _, G, s, hs⟩ := hc
  let := s
  obtain ⟨_, _, adj, _⟩ := hs
  exact (restrictionLocal Λ ℓ k (Or.inl ⟨E, ⟨Iso.refl _⟩⟩) f c h G adj).2


/-- The integral Brown right adjoint is constructible on a finite affine-chart cover.
This is a local conclusion only, prior to finite-open descent.
Source: det-thm-int-restriction-glue, proof steps 5--7; blueprint
sk-thm-int-restriction-glue.proof.md, paragraph (2).
(blueprint: lem-int-restriction-chart-cover).

Proof: The standing schemes are Noetherian. Choose finite affine source opens U
mapping into affine target opens V; finite generators of their coordinate algebras
give closed immersions i:U into A^d_V with f u = v p i. All chart maps are separated
of finite type, since opens in Noetherian schemes are quasi-compact. Work in the
integral localizing closure of Dbc. The open extension/restriction
adjunctions identify the exceptional pullback on an open with ordinary pullback.
Composition of integral compact-support functors and uniqueness of right adjoints
then identify u^* G with i^! p^! v^*. Pullback takes the finite constant scalar
presentations of K to the same presentations on V. The integral affine-space
restriction theorem takes this object to Dbc(A^d_V); the integral closed-immersion
restriction theorem takes the result to Dbc(U). Transfer along the comparison
isomorphism (constant-model constructibility is invariant under isomorphism).
Identify each affine open immersion with the inclusion of its open image and
transport the local conclusions through that scheme isomorphism. Their images
still cover X. No global boundedness or constructibility of G K is used here.
The empty-source case uses the empty family. -/
theorem integralRestriction_chartCover
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (c : Compactification.BoundaryCompactification f)
    (h : ∀ K, localizing (Profinite.padicIntegersRingObj ℓ E.val) X K →
      localizing (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((image (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj).obj K))
    (G : (localizing (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory ⥤
      (localizing (Profinite.padicIntegersRingObj ℓ E.val) X).FullSubcategory)
    (adj : lowerShriek (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj h ⊣ G)
    (K : (localizing (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory)
    (hK : generators (Profinite.padicIntegersRingObj ℓ E.val) Y K.obj) :
    ∃ (n : ℕ) (U : Fin n → X.Opens), iSup U = ⊤ ∧
      ∀ a : Fin n, generators (Profinite.padicIntegersRingObj ℓ E.val) (U a).toScheme
        ((pull (Profinite.padicIntegersRingObj ℓ E.val) (U a).ι).obj (G.obj K).obj) := by
  classical
  let Λ := Profinite.padicIntegersRingObj ℓ E.val
  have noeth (Z : Scheme.{u}) [Z.Over (Spec (.of k))]
      [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))] :
      IsNoetherian Z := by
    have : IsLocallyNoetherian Z :=
      LocallyOfFiniteType.isLocallyNoetherian (Z ↘ Spec (.of k))
    have : CompactSpace Z :=
      QuasiCompact.compactSpace_of_compactSpace (Z ↘ Spec (.of k))
    exact ⟨⟩
  have : IsNoetherian X := noeth X
  have : IsNoetherian Y := noeth Y
  obtain ⟨n, A, u, hA, hcov, hfac⟩ := affineCharts ℓ E k f c
  have hu : ∀ a, IsOpenImmersion (u a) := fun a ↦ (hA a).2
  let O : Fin n → X.Opens := fun a ↦ (u a).opensRange
  refine ⟨n, O, ?_, ?_⟩
  · apply top_unique
    intro x _
    obtain ⟨a, y, hy⟩ := hcov x
    apply TopologicalSpace.Opens.mem_iSup.mpr
    exact ⟨a, y, hy⟩
  · intro a
    have : IsAffine (A a) := (hA a).1
    obtain ⟨V, v, hV, hv, d, i, hi, q, hqi, hq⟩ := hfac a
    let : (A a).Over (Spec (.of k)) := ⟨u a ≫ (X ↘ Spec (.of k))⟩
    let : V.Over (Spec (.of k)) := ⟨v ≫ (Y ↘ Spec (.of k))⟩
    have : IsAffine V := hV
    have : IsOpenImmersion v := hv
    have : IsClosedImmersion i := hi
    have : TopologicalSpace.NoetherianSpace (A a) :=
      (u a).isOpenEmbedding.isInducing.noetherianSpace
    have : TopologicalSpace.NoetherianSpace V := v.isOpenEmbedding.isInducing.noetherianSpace
    have : (u a).IsOver (Spec (.of k)) := ⟨rfl⟩
    have : v.IsOver (Spec (.of k)) := ⟨rfl⟩
    have : IsSeparated (A a ↘ Spec (.of k)) :=
      (show IsSeparated (u a ≫ (X ↘ Spec (.of k))) from inferInstance)
    have : LocallyOfFiniteType (A a ↘ Spec (.of k)) :=
      (show LocallyOfFiniteType (u a ≫ (X ↘ Spec (.of k))) from inferInstance)
    have : QuasiCompact (A a ↘ Spec (.of k)) :=
      (show QuasiCompact (u a ≫ (X ↘ Spec (.of k))) from inferInstance)
    have : IsSeparated (V ↘ Spec (.of k)) :=
      (show IsSeparated (v ≫ (Y ↘ Spec (.of k))) from inferInstance)
    have : LocallyOfFiniteType (V ↘ Spec (.of k)) :=
      (show LocallyOfFiniteType (v ≫ (Y ↘ Spec (.of k))) from inferInstance)
    have : QuasiCompact (V ↘ Spec (.of k)) :=
      (show QuasiCompact (v ≫ (Y ↘ Spec (.of k))) from inferInstance)
    have hgeom : (i ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V)) ≫ v = u a ≫ f := by
      exact (congrArg (fun t ↦ t ≫ v) hqi).trans hq
    have : i.IsOver (Spec (.of k)) := ⟨by
      simpa only [Category.assoc, comp_over] using
        congrArg (fun t ↦ t ≫ (Y ↘ Spec (.of k))) hgeom⟩
    have hlocal := local_preserves ℓ E k f c h G adj (u a) v d i hgeom K hK
    let e := (u a).isoOpensRange
    have : e.hom.IsOver (Spec (.of k)) := ⟨by
      change e.hom ≫ ((O a).ι ≫ (X ↘ Spec (.of k))) = u a ≫ (X ↘ Spec (.of k))
      rw [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]⟩
    have : IsSeparated ((O a).toScheme ↘ Spec (.of k)) :=
      (show IsSeparated ((O a).ι ≫ (X ↘ Spec (.of k))) from inferInstance)
    have : LocallyOfFiniteType ((O a).toScheme ↘ Spec (.of k)) :=
      (show LocallyOfFiniteType ((O a).ι ≫ (X ↘ Spec (.of k))) from inferInstance)
    have : QuasiCompact ((O a).toScheme ↘ Spec (.of k)) :=
      (show QuasiCompact ((O a).ι ≫ (X ↘ Spec (.of k))) from inferInstance)
    have htrans := pull_generators ℓ E k e.inv _ hlocal
    let ec := (leftDerivedUpperStarComp Λ e.inv (u a)).app (G.obj K).obj
    have heq : e.inv ≫ u a = (O a).ι := by
      exact (Iso.inv_comp_eq e).mpr (Scheme.Hom.isoOpensRange_hom_ι (u a)).symm
    exact boundedConstructible_iso Λ
      (ec.symm ≪≫ eqToIso (congrArg (fun t ↦ (pull Λ t).obj (G.obj K).obj) heq)) htrans



end AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.IntegralRestriction
