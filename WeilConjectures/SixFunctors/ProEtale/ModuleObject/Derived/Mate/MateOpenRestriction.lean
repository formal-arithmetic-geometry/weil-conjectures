/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestrictionMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.BrownExceptionalAdjoint
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.Compactification.BaseChange
public import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoverRestrictionConservative
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenPullbackGenerators
import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionLocalizing
import WeilConjectures.Compactification.BoundaryRefinement
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenCompactSupportExchange
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing

/-!
# Open restriction of the Brown exceptional inverse image

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-sf-mate,
det-sf-mate-open-restriction, clauses (1)--(3) and proof
(blueprint: det-sf-mate-open-restriction).

The exceptional functors are arbitrary right adjoints of the recorded compactification
lower shrieks, hence include the compactification-independent Brown adjoints. All comparison
isomorphisms below are characterized by explicit adjunction equations. The target equation
uses the ordinary open base-change mate, defined before any invertibility assertion.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private theorem conjugate_hom
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (e : L₂ ≅ L₁)
    (T : C) (B : D) (f : T ⟶ R₁.obj B) :
    f ≫ ((conjugateIsoEquiv a₁ a₂ e).hom.app B) =
      a₂.homEquiv T B (e.hom.app T ≫ (a₁.homEquiv T B).symm f) := by
  apply (a₂.homEquiv T B).symm.injective
  simp only [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, Functor.map_comp,
    Category.assoc]
  rw [conjugateIsoEquiv_apply_hom, conjugateEquiv_counit]
  rw [← e.hom.naturality_assoc]

private theorem normalized_conjugate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {E : A ⥤ B} {R : B ⥤ A} {F : B ⥤ D} {G : D ⥤ B}
    {Q : A ⥤ C} {J : C ⥤ A} {V : C ⥤ D} {W : D ⥤ C}
    (ae : E ⊣ R) (af : F ⊣ G) (aq : Q ⊣ J) (av : V ⊣ W)
    (β : Q ⋙ V ≅ E ⋙ F)
    (T : ∀ M, W.obj (F.obj (E.obj M)) ⟶ Q.obj M)
    (hβ : ∀ M, T M ≫ av.unit.app (Q.obj M) ≫ W.map (β.hom.app M) = 𝟙 _)
    (M : A) (N : D) (b : M ⟶ R.obj (G.obj N)) :
    T M ≫ (aq.homEquiv M (W.obj N)).symm
        (b ≫ (conjugateIsoEquiv (ae.comp af) (aq.comp av) β).hom.app N) =
      W.map ((af.homEquiv (E.obj M) N).symm ((ae.homEquiv M (G.obj N)).symm b)) := by
  rw [conjugate_hom (ae.comp af) (aq.comp av)]
  simp only [Adjunction.comp_homEquiv, Equiv.symm_trans_apply]
  change T M ≫ (aq.homEquiv M (W.obj N)).symm
    ((aq.homEquiv M (W.obj N)) ((av.homEquiv (Q.obj M) N)
      (β.hom.app M ≫ (af.homEquiv (E.obj M) N).symm
        ((ae.homEquiv M (G.obj N)).symm b)))) = _
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_unit, W.map_comp]
  have hb := hβ M
  rw [← Category.assoc] at hb
  rw [← Category.assoc, ← Category.assoc, hb, Category.id_comp]

/-- Open extension is left adjoint to exact restriction on precisely Loc(Dctf). The Hom
bijection is the restriction of the existing termwise open adjunction. Every Brown right
adjoint is identified with restriction by the unique counit-compatible isomorphism.
Source: blueprint det-sf-mate-open-restriction (1)
(blueprint: det-sf-mate-open-restriction).

Proof: The existing exact derived open adjunction already supplies the ambient Hom
bijections. Obtain open-extension preservation from openImmersionLowerShriek_localizing.
For pullback, use openPullback_generators and the defining intersection of the localizing
closure: inverse images of the replete triangulated sum-closed candidates are again such
candidates, since exact termwise pullback is also a left adjoint. Restrict the ambient
adjunction using restrictFullyFaithful, retaining its Hom formula. Transport extension
preservation and the adjunction along mateOpenTrivialLowerShriek for (j,id). The canonical
rightAdjointUniq has precisely the displayed counit equation; injectivity of the inverse
Hom equivalence proves that it is the only such isomorphism. -/
theorem mateOpenImmersion
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpℓ : p ≠ ℓ)
    (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {U X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] :
    ∃ (he : ∀ K : (localizingClosureProEtale Λ U).FullSubcategory,
          localizingClosureProEtale Λ X
            ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj K.obj))
      (hs : ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
          localizingClosureProEtale Λ U ((upperStar Λ j).mapDerivedCategory.obj K.obj))
      (ht : ∀ K, localizingClosureProEtale Λ U K → localizingClosureProEtale Λ X
        ((rightDerivedLowerShriekOfCompactification Λ
          (Compactification.ofIsOpenImmersion j)).obj K))
      (adj : mateOpenExtension Λ j he ⊣ mateOpenPullback Λ j hs),
      (∀ (M : (localizingClosureProEtale Λ U).FullSubcategory)
        (N : (localizingClosureProEtale Λ X).FullSubcategory)
        (b : (mateOpenExtension Λ j he).obj M ⟶ N),
        (adj.homEquiv M N b).hom =
          (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).homEquiv M.obj N.obj b.hom) ∧
      ∀ (G : (localizingClosureProEtale Λ X).FullSubcategory ⥤
          (localizingClosureProEtale Λ U).FullSubcategory)
        (adjG : localizingLowerShriek Λ (Compactification.ofIsOpenImmersion j) ht ⊣ G),
        ∃! e : G ≅ mateOpenPullback Λ j hs,
          ∀ N,
            ((localizingLowerShriek Λ (Compactification.ofIsOpenImmersion j) ht).map
                (e.hom.app N)).hom ≫
              (mateOpenTrivialLowerShriek Λ j).hom.app
                ((mateOpenPullback Λ j hs).obj N).obj ≫
              (adj.counit.app N).hom = (adjG.counit.app N).hom := by
  let : U.Over (Spec (.of k)) := ⟨j ≫ (X ↘ Spec (.of k))⟩
  have : j.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : LocallyOfFiniteType (U ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (j ≫ (X ↘ Spec (.of k))))
  have : QuasiCompact (U ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (j ≫ (X ↘ Spec (.of k))))
  have : IsSeparated (U ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated (j ≫ (X ↘ Spec (.of k))))
  obtain ⟨_, _, he, _⟩ :=
    (openImmersionLowerShriek_localizing ℓ k p _hp _hpℓ Λ _hΛ j).2.2
  have hs : ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
      localizingClosureProEtale Λ U ((upperStar Λ j).mapDerivedCategory.obj K.obj) := by
    let F := (upperStar Λ j).mapDerivedCategory
    have : F.IsLeftAdjoint :=
      ((derivedUpperStarLowerStarAdjunction Λ j).ofNatIsoLeft
        (leftDerivedUpperStarIsoMapDerivedCategory Λ j)).isLeftAdjoint
    intro K P hP hS
    let := hP.1
    let := hP.2.1
    have hR : IsLocalizingSubcategory (P.inverseImage F) := by
      refine ⟨inferInstance, inferInstance, ?_⟩
      intro I D hD hobj
      let := hD
      have : HasColimit (D ⋙ F) := inferInstance
      exact P.prop_of_iso (preservesColimitIso F D).symm
        (hP.2.2 (D ⋙ F) inferInstance hobj)
    exact K.property (P.inverseImage F) hR (fun L hL ↦
      hS _ (openPullback_generators Λ ℓ k p _hp _hpℓ _hΛ j ⟨L, hL⟩))
  have ht : ∀ K, localizingClosureProEtale Λ U K → localizingClosureProEtale Λ X
      ((rightDerivedLowerShriekOfCompactification Λ
        (Compactification.ofIsOpenImmersion j)).obj K) := by
    intro K hK P hP hS
    let := hP.2.1
    exact P.prop_of_iso ((mateOpenTrivialLowerShriek Λ j).app K).symm
      (he ⟨K, hK⟩ P hP hS)
  let adj : mateOpenExtension Λ j he ⊣ mateOpenPullback Λ j hs :=
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).restrictFullyFaithful
      (localizingClosureProEtale Λ U).fullyFaithfulι
      (localizingClosureProEtale Λ X).fullyFaithfulι (Iso.refl _) (Iso.refl _)
  have hadj : ∀ (M : (localizingClosureProEtale Λ U).FullSubcategory)
      (N : (localizingClosureProEtale Λ X).FullSubcategory)
      (b : (mateOpenExtension Λ j he).obj M ⟶ N),
      (adj.homEquiv M N b).hom =
        (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).homEquiv M.obj N.obj
          b.hom := by
    intro M N b
    dsimp only [adj]
    rw [Adjunction.restrictFullyFaithful_homEquiv_apply]
    simp [Adjunction.homEquiv_apply]
  let t : localizingLowerShriek Λ (Compactification.ofIsOpenImmersion j) ht ≅
      mateOpenExtension Λ j he := NatIso.ofComponents
    (fun M ↦ (localizingClosureProEtale Λ X).isoMk
      ((mateOpenTrivialLowerShriek Λ j).app M.obj))
    (by intro M N b; ext; exact (mateOpenTrivialLowerShriek Λ j).hom.naturality b.hom)
  let adjT := adj.ofNatIsoLeft t.symm
  refine ⟨he, hs, ht, adj, hadj, ?_⟩
  intro G adjG
  refine ⟨adjG.rightAdjointUniq adjT, ?_, ?_⟩
  · intro N
    exact congrArg (fun b ↦ b.hom) (adjG.rightAdjointUniq_hom_app_counit adjT N)
  · intro e heq
    apply Iso.ext
    apply NatTrans.ext
    funext N
    apply (adjT.homEquiv _ N).symm.injective
    exact (show _ = (adjG.counit.app N) by
      ext
      exact heq N).trans
        (adjG.homEquiv_symm_rightAdjointUniq_hom_app adjT N).symm

/-- Source-open restriction of f! is the exceptional inverse image of fj. The induced
adjunction is normalized by the actual composite of open extensions in the same
compactification, and the comparison to any Brown adjoint is uniquely counit-compatible.
The arguments G and adjF range over all right adjoints supplied by det-sf-existence-brown;
no exceptional-adjunction assumption on an ambient derived category is made.
Source: blueprint det-sf-mate-open-restriction (2), source-open comparison
(blueprint: det-sf-mate-open-restriction).

Proof: X is Noetherian because its structure map is of finite type over a field.
Thus j is quasi-compact and mateOpenImmersion gives he, hs and the normalized open
adjunction. Transport hf after he along the actual mateOpenSourceLowerShriek to obtain
hjf. Lift that same compositor to the full localizing categories, and transport the
composite of the open adjunction and adjF along it. comp_homEquiv and the open Hom formula
give the displayed normalization. rightAdjointUniq supplies the comparison to any adjJ;
injectivity of the inverse Hom equivalence gives uniqueness. This source-open argument
needs no general rational or nonrational lower-shriek composition theorem. -/
theorem mateOpenSourceRestriction
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpℓ : p ≠ ℓ)
    (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (c : Compactification f)
    (hf : ∀ K, localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
      ((rightDerivedLowerShriekOfCompactification Λ c).obj K))
    (G : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
      (localizingClosureProEtale Λ X).FullSubcategory)
    (adjF : localizingLowerShriek Λ c hf ⊣ G)
    {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    ∃ (he : ∀ K : (localizingClosureProEtale Λ U).FullSubcategory,
          localizingClosureProEtale Λ X
            ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj K.obj))
      (hs : ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
          localizingClosureProEtale Λ U ((upperStar Λ j).mapDerivedCategory.obj K.obj))
      (hjf : ∀ K, localizingClosureProEtale Λ U K → localizingClosureProEtale Λ Y
        ((rightDerivedLowerShriekOfCompactification Λ (c.precomp j)).obj K))
      (adjS : localizingLowerShriek Λ (c.precomp j) hjf ⊣ G ⋙ mateOpenPullback Λ j hs),
      (∀ (M : (localizingClosureProEtale Λ U).FullSubcategory)
        (N : (localizingClosureProEtale Λ Y).FullSubcategory)
        (b : (localizingLowerShriek Λ (c.precomp j) hjf).obj M ⟶ N),
        (adjS.homEquiv M N b).hom =
          (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).homEquiv M.obj (G.obj N).obj
            ((adjF.homEquiv ((mateOpenExtension Λ j he).obj M) N)
              ⟨(mateOpenSourceLowerShriek Λ c j).hom.app M.obj ≫ b.hom⟩).hom) ∧
      ∀ (J : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
          (localizingClosureProEtale Λ U).FullSubcategory)
        (adjJ : localizingLowerShriek Λ (c.precomp j) hjf ⊣ J),
        ∃! e : G ⋙ mateOpenPullback Λ j hs ≅ J,
          ∀ N, (localizingLowerShriek Λ (c.precomp j) hjf).map (e.hom.app N) ≫
            adjJ.counit.app N = adjS.counit.app N := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have : QuasiCompact j := inferInstance
  obtain ⟨he, hs, _, adj, hadj, _⟩ := mateOpenImmersion Λ ℓ k p _hp _hpℓ _hΛ j
  have hjf : ∀ K, localizingClosureProEtale Λ U K → localizingClosureProEtale Λ Y
      ((rightDerivedLowerShriekOfCompactification Λ (c.precomp j)).obj K) := by
    intro K hK P hP hS
    let := hP.2.1
    exact P.prop_of_iso ((mateOpenSourceLowerShriek Λ c j).app K)
      (hf _ (he ⟨K, hK⟩) P hP hS)
  let s : mateOpenExtension Λ j he ⋙ localizingLowerShriek Λ c hf ≅
      localizingLowerShriek Λ (c.precomp j) hjf := NatIso.ofComponents
    (fun M ↦ (localizingClosureProEtale Λ Y).isoMk
      ((mateOpenSourceLowerShriek Λ c j).app M.obj))
    (by intro M N b; ext; exact (mateOpenSourceLowerShriek Λ c j).hom.naturality b.hom)
  let adjS := (adj.comp adjF).ofNatIsoLeft s
  refine ⟨he, hs, hjf, adjS, ?_, ?_⟩
  · intro M N b
    rw [Adjunction.homEquiv_ofNatIsoLeft_apply, Adjunction.comp_homEquiv]
    exact hadj M (G.obj N) _
  · intro J adjJ
    refine ⟨adjS.rightAdjointUniq adjJ,
      fun N ↦ adjS.rightAdjointUniq_hom_app_counit adjJ N, ?_⟩
    intro e heq
    apply Iso.ext
    apply NatTrans.ext
    funext N
    apply (adjJ.homEquiv _ N).symm.injective
    exact (heq N).trans (adjS.homEquiv_symm_rightAdjointUniq_hom_app adjJ N).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- Elaborating the restricted composite adjunctions requires additional heartbeats.
/-- Target-open restriction u* f! = f_V! v*, with its precise mate normalization.
The inverse-image scheme U is expressed by an arbitrary Cartesian open square, including
its identity and empty cases. The base-changed compactification is the recorded upstream
construction c.ofIsPullback. The equation is in the ambient derived module category and
thus, by fullness, also in its localizing subcategory. It fixes e uniquely.
Source: blueprint det-sf-mate-open-restriction (2), target-open comparison
(blueprint: det-sf-mate-open-restriction).

Proof: Restrict the open extension/restriction adjunctions to the localizing categories.
Finite type over the field makes the targets Noetherian, so the open immersions are
quasi-compact. Brown representability on the base-changed compactification supplies hq
and a right adjoint. The normalized compact-support comparison
mateOpenCompactSupportExchange identifies the two composite left adjoints. Conjugating
this isomorphism under the composite adjunctions gives the asserted right-adjoint
comparison. Its normalization follows from the open unit equation of that comparison
and the component formula for conjugation. The specified target lower-shriek mate is
invertible, so cancellation and injectivity of the adjunction Hom equivalence prove
uniqueness. This uses proper/open interchange on the given Cartesian compactification,
without invoking general lower-shriek composition. -/
theorem mateOpenTargetRestriction
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpℓ : p ≠ ℓ)
    (hcd : AlgebraicGeometry.ProEtale.BaseFieldFiniteCD ℓ k)
    (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (c : Compactification f)
    (hf : ∀ K, localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
      ((rightDerivedLowerShriekOfCompactification Λ c).obj K))
    (G : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
      (localizingClosureProEtale Λ X).FullSubcategory)
    (adjF : localizingLowerShriek Λ c hf ⊣ G)
    {U V : Scheme.{u}} (a : U ⟶ X) (q : U ⟶ V) (v : V ⟶ Y)
    [IsOpenImmersion a] [IsOpenImmersion v] (sq : IsPullback a q f v) :
    ∃ (he : ∀ K : (localizingClosureProEtale Λ U).FullSubcategory,
          localizingClosureProEtale Λ X
            ((openImmersionLowerShriek Λ a).mapDerivedCategory.obj K.obj))
      (hs : ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
          localizingClosureProEtale Λ U ((upperStar Λ a).mapDerivedCategory.obj K.obj))
      (hv : ∀ K : (localizingClosureProEtale Λ Y).FullSubcategory,
          localizingClosureProEtale Λ V ((upperStar Λ v).mapDerivedCategory.obj K.obj))
      (hq : ∀ K, localizingClosureProEtale Λ U K → localizingClosureProEtale Λ V
        ((rightDerivedLowerShriekOfCompactification Λ (c.ofIsPullback sq)).obj K)),
      (∃ J : (localizingClosureProEtale Λ V).FullSubcategory ⥤
          (localizingClosureProEtale Λ U).FullSubcategory,
        Nonempty (localizingLowerShriek Λ (c.ofIsPullback sq) hq ⊣ J)) ∧
      ∀ (J : (localizingClosureProEtale Λ V).FullSubcategory ⥤
          (localizingClosureProEtale Λ U).FullSubcategory)
        (adjJ : localizingLowerShriek Λ (c.ofIsPullback sq) hq ⊣ J),
        ∃! e : G ⋙ mateOpenPullback Λ a hs ≅ mateOpenPullback Λ v hv ⋙ J,
          ∀ (M : (localizingClosureProEtale Λ U).FullSubcategory)
            (N : (localizingClosureProEtale Λ Y).FullSubcategory)
            (b : M ⟶ (mateOpenPullback Λ a hs).obj (G.obj N)),
            mateOpenTargetLowerShriek Λ sq c M.obj ≫
                ((adjJ.homEquiv M ((mateOpenPullback Λ v hv).obj N)).symm
                  (b ≫ e.hom.app N)).hom =
              (upperStar Λ v).mapDerivedCategory.map
                (((adjF.homEquiv ((mateOpenExtension Λ a he).obj M) N).symm
                  ⟨((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ a).homEquiv
                    M.obj (G.obj N).obj).symm b.hom⟩).hom) := by
  classical
  have hchar : ringChar k = p := ringChar.eq k p
  have : Fact (ringChar k).Prime := ⟨by
    rw [hchar]
    exact (CharP.char_is_prime_or_zero k p).resolve_right (Nat.ne_of_gt _hp)⟩
  have : Fact (ringChar k ≠ ℓ) := ⟨by simpa only [hchar] using _hpℓ⟩
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : IsNoetherian Y := ⟨⟩
  have : QuasiCompact a := inferInstance
  have : QuasiCompact v := inferInstance
  let : U.Over (Spec (.of k)) := ⟨a ≫ (X ↘ Spec (.of k))⟩
  let : V.Over (Spec (.of k)) := ⟨v ≫ (Y ↘ Spec (.of k))⟩
  have : a.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : v.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : q.IsOver (Spec (.of k)) := ⟨by
    change q ≫ v ≫ (Y ↘ Spec (.of k)) = a ≫ (X ↘ Spec (.of k))
    rw [← Category.assoc, ← sq.w, Category.assoc, comp_over]⟩
  have : LocallyOfFiniteType (U ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (a ≫ (X ↘ Spec (.of k))))
  have : QuasiCompact (U ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (a ≫ (X ↘ Spec (.of k))))
  have : IsSeparated (U ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated (a ≫ (X ↘ Spec (.of k))))
  have : LocallyOfFiniteType (V ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (v ≫ (Y ↘ Spec (.of k))))
  have : QuasiCompact (V ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (v ≫ (Y ↘ Spec (.of k))))
  have : IsSeparated (V ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated (v ≫ (Y ↘ Spec (.of k))))
  have : LocallyOfFiniteType q := MorphismProperty.of_isPullback sq inferInstance
  have : QuasiCompact q := MorphismProperty.of_isPullback sq inferInstance
  have : IsSeparated q := MorphismProperty.of_isPullback sq inferInstance
  obtain ⟨he, hs, _, adjA, hadjA, _⟩ := mateOpenImmersion Λ ℓ k p _hp _hpℓ _hΛ a
  obtain ⟨hev, hv, _, adjV, hadjV, _⟩ := mateOpenImmersion Λ ℓ k p _hp _hpℓ _hΛ v
  let d := c.ofIsPullback sq
  have : IsLocallyNoetherian V :=
    LocallyOfFiniteType.isLocallyNoetherian (V ↘ Spec (.of k))
  have : IsLocallyNoetherian d.Z := LocallyOfFiniteType.isLocallyNoetherian d.g
  have : QuasiCompact d.i := inferInstance
  let bd : Compactification.BoundaryCompactification q := ⟨⟨d, inferInstance⟩⟩
  obtain ⟨hq, hU, hV, hQ⟩ := exists_localizingExceptionalAdjoint (hcd := hcd) Λ ℓ k q bd _hΛ
  let := hU
  let := hV
  obtain ⟨J₀, sJ, hJ⟩ := hQ.2.2.2.2
  let := sJ
  obtain ⟨_, _, adjJ₀, _⟩ := hJ
  refine ⟨he, hs, hv, hq, ⟨J₀, ⟨adjJ₀⟩⟩, ?_⟩
  intro J adjJ
  obtain ⟨β, hβ⟩ := mateOpenCompactSupportExchange Λ ℓ k p _hp _hpℓ _hΛ f c a q v sq
  let βL : localizingLowerShriek Λ d hq ⋙ mateOpenExtension Λ v hev ≅
      mateOpenExtension Λ a he ⋙ localizingLowerShriek Λ c hf := NatIso.ofComponents
    (fun M ↦ (localizingClosureProEtale Λ Y).isoMk (β.app M))
    (by intro M N b; ext; exact β.hom.naturality b)
  let e := conjugateIsoEquiv (adjA.comp adjF) (adjJ.comp adjV) βL
  have heq : ∀ M N b,
      mateOpenTargetLowerShriek Λ sq c M.obj ≫
          ((adjJ.homEquiv M ((mateOpenPullback Λ v hv).obj N)).symm
            (b ≫ e.hom.app N)).hom =
        (upperStar Λ v).mapDerivedCategory.map
          (((adjF.homEquiv ((mateOpenExtension Λ a he).obj M) N).symm
            ⟨((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ a).homEquiv
              M.obj (G.obj N).obj).symm b.hom⟩).hom) := by
    intro M N b
    have hnorm : ∀ M,
        (⟨mateOpenTargetLowerShriek Λ sq c M.obj⟩ :
          (mateOpenPullback Λ v hv).obj
              ((localizingLowerShriek Λ c hf).obj ((mateOpenExtension Λ a he).obj M)) ⟶
            (localizingLowerShriek Λ d hq).obj M) ≫
          adjV.unit.app ((localizingLowerShriek Λ d hq).obj M) ≫
          (mateOpenPullback Λ v hv).map (βL.hom.app M) = 𝟙 _ := by
      intro M
      ext
      change mateOpenTargetLowerShriek Λ sq c M.obj ≫
        (adjV.unit.app ((localizingLowerShriek Λ d hq).obj M)).hom ≫
        (upperStar Λ v).mapDerivedCategory.map (β.hom.app M) = 𝟙 _
      have hunit := hadjV ((localizingLowerShriek Λ d hq).obj M)
        ((mateOpenExtension Λ v hev).obj ((localizingLowerShriek Λ d hq).obj M)) (𝟙 _)
      rw [Adjunction.homEquiv_id] at hunit
      change (adjV.unit.app _).hom =
        (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ v).homEquiv _ _ (𝟙 _) at hunit
      rw [Adjunction.homEquiv_id] at hunit
      rw [hunit]
      exact hβ M
    have hh := normalized_conjugate adjA adjF adjJ adjV βL
      (fun M ↦ ⟨mateOpenTargetLowerShriek Λ sq c M.obj⟩) hnorm M N b
    have ha : (((adjA.homEquiv M (G.obj N)).symm b).hom) =
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ a).homEquiv
          M.obj (G.obj N).obj).symm b.hom := by
      have h := hadjA M (G.obj N) ((adjA.homEquiv M (G.obj N)).symm b)
      simp only [Equiv.apply_symm_apply] at h
      exact (((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ a).homEquiv
        M.obj (G.obj N).obj).symm_apply_eq.mpr h).symm
    have ha' : (adjA.homEquiv M (G.obj N)).symm b =
        ⟨((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ a).homEquiv
          M.obj (G.obj N).obj).symm b.hom⟩ := by
      ext
      exact ha
    rw [ha'] at hh
    exact congrArg (fun z ↦ z.hom) hh
  refine ⟨e, heq, ?_⟩
  intro e' heq'
  apply Iso.ext
  apply NatTrans.ext
  funext N
  have hT (M : (localizingClosureProEtale Λ U).FullSubcategory) :
      IsIso (mateOpenTargetLowerShriek Λ sq c M.obj) := by
    have : IsIso (mateOpenTargetLowerShriek Λ sq c M.obj ≫
        (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ v).unit.app
          ((rightDerivedLowerShriekOfCompactification Λ d).obj M.obj) ≫
        (upperStar Λ v).mapDerivedCategory.map (β.hom.app M)) := by
      rw [hβ M]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ v).unit.app
          ((rightDerivedLowerShriekOfCompactification Λ d).obj M.obj) ≫
        (upperStar Λ v).mapDerivedCategory.map (β.hom.app M))
  have H := heq' ((G ⋙ mateOpenPullback Λ a hs).obj N) N (𝟙 _)
  have H' := heq ((G ⋙ mateOpenPullback Λ a hs).obj N) N (𝟙 _)
  have := hT ((G ⋙ mateOpenPullback Λ a hs).obj N)
  apply (adjJ.homEquiv _ _).symm.injective
  apply ObjectProperty.hom_ext
  apply (cancel_epi (mateOpenTargetLowerShriek Λ sq c
    ((G ⋙ mateOpenPullback Λ a hs).obj N).obj)).mp
  simpa only [Category.id_comp] using H.trans H'.symm

/-- Open restrictions jointly detect isomorphisms on the whole localizing closure, for
arbitrary open covers and arbitrary (unbounded) objects. Applying the preceding two
comparisons to every member gives exactly the two locality assertions for f! in clause (3).
Source: blueprint det-sf-mate-open-restriction (3)
(blueprint: det-sf-mate-open-restriction).

Proof: The supplied iSup equality says that the given opens cover X. Their inclusions
form the actual pro-etale cover ofArrows_opens_ι_mem_proetalePrecoverage. Apply
condensed_cover_restriction_conservative to the condensed ring Mon.mk Λ, this cover,
and b.hom in the ambient unbounded derived category. Its hypotheses are exactly the
restrictions in the statement. ObjectProperty.isIso_hom_iff gives the isomorphism in
the full localizing subcategory. The argument includes the empty scheme and arbitrary
index universes; no cohomological bound is introduced. -/
theorem mateOpenCover_isIso
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpℓ : p ≠ ℓ)
    (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    {I : Type w} (U : I → X.Opens) (_hcover : iSup U = ⊤)
    {K L : (localizingClosureProEtale Λ X).FullSubcategory} (b : K ⟶ L)
    (_hb : ∀ i : I, IsIso ((upperStar Λ (U i).ι).mapDerivedCategory.map b.hom)) :
    IsIso b := by
  let C : Scheme.Cover.{w} Scheme.proetalePrecoverage X :=
    { I₀ := I
      X i := (U i).toScheme
      f i := (U i).ι
      mem₀ := ofArrows_opens_ι_mem_proetalePrecoverage U (by
        intro x
        have hx : x ∈ iSup U := by rw [_hcover]; trivial
        exact TopologicalSpace.Opens.mem_iSup.mp hx) }
  have hb : IsIso b.hom :=
    ((condensed_cover_restriction_conservative (Mon.mk Λ) X C).1 K.obj L.obj b.hom).2 _hb
  exact (ObjectProperty.isIso_hom_iff b).1 hb

end AlgebraicGeometry.ProEtale.CondensedRing
