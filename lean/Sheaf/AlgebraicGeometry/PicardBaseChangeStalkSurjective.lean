/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.AlgebraicGeometry.PicardUniversalRankMatch
public import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData
import Sheaf.AlgebraicGeometry.PerfectUniversalH0TruncationPullback

/-! # Stalk surjectivity of canonical Picard base change

Source: Stacks Project, Tags 0BDP, 0BDL, and 0B91.
(blueprint: lem-sc-picard-base-change-stalk-surjective).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The canonical Picard base-change map is surjective on each stalk.
This is only surjectivity; no injectivity or isomorphism is asserted.
Source: Stacks Project, Tag 0BDP, omitted base-change detail in the third paragraph;
Tag 0BDL, finite-free residue model and matrix-zero locus; Tag 0B91(2).
(blueprint: lem-sc-picard-base-change-stalk-surjective)

Proof:
1. Work near h(t) on a common-rank neighbourhood from hR for the identity of T.
   Proper flat finite presentation and finite local freeness of E and its dual imply
   that each derived direct image is perfect and commutes with arbitrary derived base
   change (Tag 0B91). Its Tor amplitude starts at zero: every scalar extension is a
   derived direct image of a module in degree zero and has no negative cohomology.
2. Shrink this neighbourhood. The universal tests in hR give constant lowest fibre
   dimension r. The ranks agree on nonempty fibres because E has rank r on X_V;
   empty fibres have zero direct image on an open neighbourhood by properness.
   Apply the residue-model construction in Tag 0BDL. After cancelling contractible
   summands its first term is free of rank r and there are no negative terms.
3. On the lowest-cohomology locus the outgoing degree-zero matrix is zero. The
   universal rank condition forces the map into this locus, including nonreduced
   test schemes. Hence H^0 is precisely the first free term; further scalar extension
   retains the zero matrix. The natural comparison from scalar extension of H^0 to
   H^0 of scalar extension is the identity on this term, and in particular surjective.
4. The degree-zero direct-image comparison identifies this specific morphism with
   moduleBaseChangeMap: transpose it under tensorPullback adjoint to pushforward.
   Naturality of the comparison and the adjunction triangle identities give the unit,
   pushforward-composition and square-commutation composite defining that map.
   The associativity comparison of the iterated pullbacks identifies the tested
   direct image with the target displayed here. An arbitrary object isomorphism
   would not suffice for this step.
5. Restriction to an open square commutes with the canonical base-change map. Pass
   from the local identity calculation to the stalk at t, where restriction leaves
   the stalk unchanged. This proves surjectivity for either F = E or F = dual E.
   Rank zero gives the unique map between zero stalks; an empty T' has no stalks. -/
theorem picardRankMatch_baseChange_stalk_surjective {X S T : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E : X.Modules) [E.IsFiniteLocallyFree] (g : T ⟶ S)
    (hR : PicardUniversalRankMatch f E g) {T' : Scheme.{u}} (h : T' ⟶ T)
    (F : X.Modules) (hF : F = E ∨ F = Modules.dual E) (t : T') :
    Function.Surjective
      ((Modules.moduleBaseChangeMap (pullback.snd f g)
        (pullback.snd (pullback.snd f g) h) h (pullback.fst (pullback.snd f g) h)
        pullback.condition ((Modules.tensorPullback (pullback.fst f g)).obj F)).stalkLinearMap t)
    := by
  classical
  let : ∀ Y : Scheme.{u},
      HasDerivedCategory.{u + 1} (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    fun Y ↦ HasDerivedCategory.standard _
  let : ∀ U : T.Opens, HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} ((moduleRings T.toRingedSpace).over U)) :=
    fun U ↦ HasDerivedCategory.standard _
  obtain ⟨K, a, hK, hnegative, hloc, ha, hcomp⟩ :=
    picardRankMatch_derived_truncation_data f E g hR F hF
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) 0
  let M := (Modules.pushforward (pullback.snd f g)).obj
    ((Modules.tensorPullback (pullback.fst f g)).obj F)
  let c := H.map ((derivedPullback h).map a)
  have : IsIso c :=
    perfect_universalH0_truncation_pullback_isIso T K hK hnegative hloc M a ha h
  obtain ⟨e0, e1, hc⟩ := hcomp T' h
  let B := SheafOfModules.forget T'.ringCatSheaf ⋙
    PresheafOfModules.toPresheaf T'.ringCatSheaf.obj ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} t
  let beta := Modules.moduleBaseChangeMap (pullback.snd f g)
    (pullback.snd (pullback.snd f g) h) h (pullback.fst (pullback.snd f g) h)
    pullback.condition ((Modules.tensorPullback (pullback.fst f g)).obj F)
  have hstalk : B.map beta ≫ B.map e1.inv = B.map e0.hom ≫ B.map c := by
    simpa only [Functor.map_comp] using congrArg (fun q ↦ B.map q) hc
  change Function.Surjective (B.map beta)
  intro y
  obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso (B.map c)).2 (B.map e1.inv y)
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (B.map e0.hom)).2 z
  refine ⟨x, (ConcreteCategory.bijective_of_isIso (B.map e1.inv)).1 ?_⟩
  have heq := congrArg (fun q ↦ q x) hstalk
  calc
    B.map e1.inv (B.map beta x) = B.map c (B.map e0.hom x) := heq
    _ = B.map c z := congrArg (fun q ↦ B.map c q) hx
    _ = B.map e1.inv y := hz

end AlgebraicGeometry.Scheme
