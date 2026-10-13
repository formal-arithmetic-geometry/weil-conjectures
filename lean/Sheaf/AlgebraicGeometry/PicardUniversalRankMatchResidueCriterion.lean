/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.PicardUniversalRankMatch
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.ResidueField
import Sheaf.AlgebraicGeometry.FlatBaseChangeResolutionIso
import Sheaf.AlgebraicGeometry.FlatBaseChangeMapSectionsLift
import all Sheaf.AlgebraicGeometry.PicardPullbackLocalRanks
import all Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFiniteRanks
import Sheaf.AlgebraicGeometry.FiniteLocallyFreeStalkFinrank

/-! # Residue-field criterion for universal Picard rank matching

Source: Stacks Project, Tag 0BDP, second and third proof paragraphs, and Tag 0BCD.
(blueprint: lem-sc-picard-universal-rank-match-residue-criterion).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private noncomputable def tensorComparison {A B : Scheme.{u}} (a : A ⟶ B) :
    Modules.tensorPullback a ≅ Modules.pullback a :=
  (Modules.nonempty_tensorPullbackAdjunction a).some.leftAdjointUniq
    (Modules.pullbackPushforwardAdjunction a)

private theorem tensor_rank_of_isIso {A B : Scheme.{u}} (a : A ⟶ B) [IsIso a]
    (M : B.Modules) (r : ℕ)
    (hr : ((Modules.tensorPullback a).obj M).IsFiniteLocallyFreeOfRank r) :
    M.IsFiniteLocallyFreeOfRank r := by
  let := hr
  have h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Modules.tensorPullback a ⋙ Modules.tensorPullback (inv a)).obj M) r :=
    tensor_rank (inv a) ((Modules.tensorPullback a).obj M) r
  let := h
  let e := (Modules.nonempty_tensorPullbackComp (inv a) a).some.symm.app M ≪≫
    eqToIso (congrArg (fun k ↦ (Modules.tensorPullback k).obj M) (IsIso.inv_hom_id a)) ≪≫
      (Modules.nonempty_tensorPullbackId B).some.app M
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} e

-- Transport ordinary direct image along an isomorphism of cartesian-square models.
private noncomputable def image_iso {A B T X : Scheme.{u}} (a : A ⟶ B) [IsIso a]
    (p : B ⟶ T) (q : B ⟶ X) (E : X.Modules) :
    (Modules.pushforward (a ≫ p)).obj ((Modules.tensorPullback (a ≫ q)).obj E) ≅
      (Modules.pushforward p).obj ((Modules.tensorPullback q).obj E) :=
  (Modules.pushforwardComp a p).symm.app _ ≪≫
    (Modules.pushforward p).mapIso
      ((Modules.pushforward a).mapIso
        ((Modules.nonempty_tensorPullbackComp a q).some.app E ≪≫
          (tensorComparison a).app _ ≪≫
            (Modules.pullbackIsoPushforwardInv a).app _) ≪≫
        (Modules.pushforwardComp (inv a) a).app _ ≪≫
        (Modules.pushforwardCongr (IsIso.inv_hom_id a)).app _ ≪≫
        (Modules.pushforwardId B).app _)

private theorem flat_image_iso {X S T Y : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [Flat g]
    (q : Y ⟶ X) (p : Y ⟶ T) (sq : IsPullback q p f g)
    (E : X.Modules) [E.IsQuasicoherent] :
    Nonempty ((Modules.tensorPullback g).obj ((Modules.pushforward f).obj E) ≅
      (Modules.pushforward p).obj ((Modules.tensorPullback q).obj E)) := by
  classical
  let := Modules.enoughInjectives X
  let := Modules.enoughInjectives (pullback g f)
  let I := injectiveResolution E
  let J := injectiveResolution ((Modules.tensorPullback (pullback.snd g f)).obj E)
  obtain ⟨t, ht⟩ := Modules.flatBaseChangeResolutionLift f g I J
  have := Modules.flatBaseChangeResolutionBeta_isIso f g E I J t ht 0
  let e₀ := (Modules.tensorPullback g).mapIso
      ((Modules.pushforward f).rightDerivedZeroIsoSelf.symm.app E) ≪≫
    asIso (Modules.flatBaseChangeResolutionBeta f g I J t 0) ≪≫
      (Modules.pushforward (pullback.fst g f)).rightDerivedZeroIsoSelf.app _
  let a := sq.flip.isoPullback
  have haq : a.hom ≫ pullback.snd g f = q := sq.flip.isoPullback_hom_snd
  have hap : a.hom ≫ pullback.fst g f = p := sq.flip.isoPullback_hom_fst
  exact ⟨e₀ ≪≫ (image_iso a.hom (pullback.fst g f) (pullback.snd g f) E).symm ≪≫
    eqToIso (by rw [haq, hap])⟩

private theorem zero_rank {T : Scheme.{u}} (M : T.Modules) (hM : IsZero M) :
    M.IsFiniteLocallyFreeOfRank 0 := by
  let N := SheafOfModules.free (R := T.ringCatSheaf) (ULift.{u} (Fin 0))
  have hN : IsZero N := (IsZero.iff_id_eq_zero N).mpr (by
    apply Sigma.hom_ext
    intro i
    exact Fin.elim0 i.down)
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} (hN.iso hM)

private noncomputable def fibreMap {X S T T' : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (h : T' ⟶ T) :
    pullback f (h ≫ g) ⟶ pullback f g :=
  pullback.lift (pullback.fst f (h ≫ g)) (pullback.snd f (h ≫ g) ≫ h)
    (by simp only [Category.assoc, pullback.condition])

private theorem fibreMap_square {X S T T' : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (h : T' ⟶ T) :
    IsPullback (fibreMap f g h) (pullback.snd f (h ≫ g)) (pullback.snd f g) h := by
  have hq : fibreMap f g h ≫ pullback.fst f g = pullback.fst f (h ≫ g) := by
    simp [fibreMap]
  apply IsPullback.of_right (hq.symm ▸ IsPullback.of_hasPullback f (h ≫ g))
    (by simp [fibreMap]) (IsPullback.of_hasPullback f g)

private theorem fibre_rank {X S T T' : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (h : T' ⟶ T) (E : X.Modules) (r : ℕ)
    (hr : ((Modules.tensorPullback (pullback.fst f g)).obj E).IsFiniteLocallyFreeOfRank r) :
    ((Modules.tensorPullback (pullback.fst f (h ≫ g))).obj E).IsFiniteLocallyFreeOfRank r := by
  let := hr
  let b := fibreMap f g h
  have hb : b ≫ pullback.fst f g = pullback.fst f (h ≫ g) := by
    simp [b, fibreMap]
  have h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Modules.tensorPullback (pullback.fst f g) ⋙ Modules.tensorPullback b).obj E) r :=
    tensor_rank b ((Modules.tensorPullback (pullback.fst f g)).obj E) r
  let := h
  let e := (Modules.nonempty_tensorPullbackComp b (pullback.fst f g)).some.symm.app E ≪≫
    eqToIso (congrArg (fun k ↦ (Modules.tensorPullback k).obj E) hb)
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} e

private theorem fibre_empty {X S T T' : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) [IsEmpty (pullback f g : Scheme.{u})] (h : T' ⟶ T) :
    IsEmpty (pullback f (h ≫ g) : Scheme.{u}) :=
  ⟨fun x ↦ isEmptyElim ((fibreMap f g h) x)⟩

private theorem fibre_image_rank {X S T T' : Scheme.{u}}
    (f : X ⟶ S) [IsProper f] (g : T ⟶ S) (h : T' ⟶ T) [Flat h]
    (E : X.Modules) [E.IsQuasicoherent] (r : ℕ)
    (hr : ((Modules.pushforward (pullback.snd f g)).obj
      ((Modules.tensorPullback (pullback.fst f g)).obj E)).IsFiniteLocallyFreeOfRank r) :
    ((Modules.pushforward (pullback.snd f (h ≫ g))).obj
      ((Modules.tensorPullback (pullback.fst f (h ≫ g))).obj E)).IsFiniteLocallyFreeOfRank r := by
  let N := (Modules.tensorPullback (pullback.fst f g)).obj E
  have : N.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent.{u, u, u} (pullback f g).ringCatSheaf).prop_of_iso
      ((tensorComparison (pullback.fst f g)).app E).symm inferInstance
  obtain ⟨e⟩ := flat_image_iso (pullback.snd f g) h (fibreMap f g h)
    (pullback.snd f (h ≫ g)) (fibreMap_square f g h) N
  let := hr
  let := tensor_rank h ((Modules.pushforward (pullback.snd f g)).obj N) r
  have hb : fibreMap f g h ≫ pullback.fst f g = pullback.fst f (h ≫ g) := by
    simp [fibreMap]
  let e' := (Modules.nonempty_tensorPullbackComp (fibreMap f g h)
      (pullback.fst f g)).some.symm.app E ≪≫
    eqToIso (congrArg (fun k ↦ (Modules.tensorPullback k).obj E) hb)
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    (e ≪≫ (Modules.pushforward (pullback.snd f (h ≫ g))).mapIso e')

/-- For a fixed-rank fibre, universal rank matching is tested by its two ordinary
residue-field direct images. Empty fibres satisfy universality independently of r.
Source: Stacks Project, Tag 0BDP, second and third proof paragraphs (perfect direct
images and arbitrary base change), and Tag 0BCD (minimal finite-free residue models).
(blueprint: lem-sc-picard-universal-rank-match-residue-criterion).

Proof:
1. If X_s is empty, every further pullback is empty. Both ordinary direct images
   are zero and finite locally free of rank zero. The pullback of E on the empty
   scheme has rank zero, so the universal condition holds using the whole open.
2. Suppose X_s is nonempty. If the universal condition holds, test it on the
   identity of Spec kappa(s). The open neighbourhood of its unique point is the
   whole spectrum. Its chosen rank equals r, since E has rank r and the fibre has
   a point. Thus both ordinary direct images have rank r.
3. Conversely suppose those direct images have rank r. Perfect direct image and
   arbitrary base change for E and E dual identify them with degree-zero derived
   fibres. Over the field choose minimal finite-free models (Tag 0BCD): they have
   no negative terms, their degree-zero terms have rank r, and every differential
   is zero. In particular their outgoing degree-zero differentials are zero.
4. Pulling these models to any scheme over Spec kappa(s) keeps those differentials
   zero and computes ordinary direct images by derived base change. Their degree-zero
   cohomology is free of rank r, and pullback preserves the constant rank r of E.
   Restricting to the whole open gives the universal condition at every point.
   Composition of pullback squares identifies these modules with the ones in the
   definition of PicardUniversalRankMatch. -/
theorem picardUniversalRankMatch_residue_iff {X S : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E : X.Modules) [E.IsFiniteLocallyFree] (r : ℕ) (s : S)
    (hEr : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj E) r) :
    PicardUniversalRankMatch f E (S.fromSpecResidueField s) ↔
      IsEmpty (pullback f (S.fromSpecResidueField s) : Scheme.{u}) ∨
        (SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Modules.pushforward (pullback.snd f (S.fromSpecResidueField s))).obj
            ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj E)) r ∧
        SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Modules.pushforward (pullback.snd f (S.fromSpecResidueField s))).obj
            ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj
              (Modules.dual E))) r) := by
  classical
  let T := Spec (S.residueField s)
  let g := S.fromSpecResidueField s
  constructor
  · intro hmatch
    by_cases he : IsEmpty (pullback f g : Scheme.{u})
    · exact Or.inl he
    · right
      have hne : Nonempty (pullback f g : Scheme.{u}) := not_isEmpty_iff.mp he
      obtain ⟨U, ht, n, hP, hD, hN⟩ :=
        hmatch (𝟙 T) (IsLocalRing.closedPoint (S.residueField s))
      have hU : U = ⊤ := by
        apply eq_top_iff.mpr
        intro t _
        rwa [Subsingleton.elim t (IsLocalRing.closedPoint (S.residueField s))]
      subst U
      have : IsIso (⊤ : T.Opens).ι := inferInstanceAs (IsIso T.topIso.hom)
      change ((Modules.tensorPullback (⊤ : T.Opens).ι).obj
        ((Modules.pushforward (pullback.snd f g)).obj
          ((Modules.tensorPullback (pullback.fst f g)).obj E))).IsFiniteLocallyFreeOfRank n
        at hP
      change SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback (⊤ : T.Opens).ι).obj
          ((Modules.pushforward (pullback.snd f g)).obj
            ((Modules.tensorPullback (pullback.fst f g)).obj (Modules.dual E)))) n at hD
      have hPn := tensor_rank_of_isIso (⊤ : T.Opens).ι _ n hP
      have hDn := tensor_rank_of_isIso (⊤ : T.Opens).ι _ n hD
      let a := pullback.map f ((⊤ : T.Opens).ι ≫ 𝟙 T ≫ g) f g
        (𝟙 X) (⊤ : T.Opens).ι (𝟙 S) (by simp) (by simp)
      have : IsIso a := by dsimp [a]; infer_instance
      have ha : a ≫ pullback.fst f g =
          pullback.fst f ((⊤ : T.Opens).ι ≫ 𝟙 T ≫ g) := by simp [a]
      have hn : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Modules.tensorPullback (pullback.fst f g)).obj E) n := by
        let := hN
        let e := (Modules.nonempty_tensorPullbackComp a (pullback.fst f g)).some.app E
        let := SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} (r := n)
          (eqToIso (congrArg (fun k ↦ (Modules.tensorPullback k).obj E) ha)).symm
        apply tensor_rank_of_isIso a _ n
        exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} e
      obtain ⟨z⟩ := hne
      let N := (Modules.tensorPullback (pullback.fst f g)).obj E
      let := hn
      have hn' := Modules.finiteLocallyFreeOfRank_stalk_finrank N n z
      let := hEr
      have hr' := Modules.finiteLocallyFreeOfRank_stalk_finrank N r z
      have hnr : n = r := hn'.symm.trans hr'
      exact hnr ▸ ⟨hPn, hDn⟩
  · intro h
    rcases h with he | ⟨hP, hD⟩
    · let := he
      intro T' h t
      have hem := fibre_empty f g h
      let := hem
      have hz (F : X.Modules) : IsZero ((Modules.pushforward (pullback.snd f (h ≫ g))).obj
          ((Modules.tensorPullback (pullback.fst f (h ≫ g))).obj F)) :=
        Functor.map_isZero _ (Modules.isZero_of_isEmpty _)
      refine ⟨⊤, trivial, 0, ?_, ?_, ?_⟩
      · let := zero_rank _ (hz E)
        exact tensor_rank (⊤ : T'.Opens).ι _ 0
      · let := zero_rank _ (hz (Modules.dual E))
        exact tensor_rank (⊤ : T'.Opens).ι _ 0
      · have := fibre_empty f g ((⊤ : T'.Opens).ι ≫ h)
        change SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Modules.tensorPullback (pullback.fst f ((⊤ : T'.Opens).ι ≫ h ≫ g))).obj E) 0
        rw [← Category.assoc]
        exact finiteLocallyFreeOfRank_of_isEmpty ((Modules.tensorPullback
            (pullback.fst f (((⊤ : T'.Opens).ι ≫ h) ≫ g))).obj E) 0
    · intro T' h t
      have := Modules.IsFiniteLocallyFree.dual E
      have hPr := fibre_image_rank f g h E r hP
      have hDr := fibre_image_rank f g h (Modules.dual E) r hD
      refine ⟨⊤, trivial, r, ?_, ?_, ?_⟩
      · let := hPr
        exact tensor_rank (⊤ : T'.Opens).ι _ r
      · let := hDr
        exact tensor_rank (⊤ : T'.Opens).ι _ r
      · change SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Modules.tensorPullback (pullback.fst f ((⊤ : T'.Opens).ι ≫ h ≫ g))).obj E) r
        rw [← Category.assoc]
        exact fibre_rank f g ((⊤ : T'.Opens).ι ≫ h) E r hEr

end AlgebraicGeometry.Scheme
