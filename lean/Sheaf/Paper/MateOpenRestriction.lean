/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.BrownExceptionalAdjoint
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.Compactification.BaseChange
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover
import Sheaf.Paper.OpenPullbackGenerators
import Sheaf.Paper.OpenImmersionLocalizing
import Sheaf.Compactification.BoundaryRefinement
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.Paper.CondensedModuleDerivedPushpull
import Sheaf.Paper.LocalizingLowerShriekComposition
import Sheaf.Paper.NonrationalLocalizingLowerShriekComposition
import Sheaf.SixFunctorsBasics.BrownHypotheses

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

/-- Restriction of the existing exact termwise inverse image to the recorded localizing
closures. The witness certifies membership only; no functor is chosen.
Source: blueprint det-sf-mate-open-restriction (1)
(blueprint: det-sf-mate-open-restriction). -/
def mateOpenPullback {U X : Scheme.{u}} (j : U ⟶ X)
    (h : ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
      localizingClosureProEtale Λ U ((upperStar Λ j).mapDerivedCategory.obj K.obj)) :
    (localizingClosureProEtale Λ X).FullSubcategory ⥤
      (localizingClosureProEtale Λ U).FullSubcategory :=
  (localizingClosureProEtale Λ U).lift
    ((localizingClosureProEtale Λ X).ι ⋙ (upperStar Λ j).mapDerivedCategory) h

/-- Restriction of actual levelwise extension by zero to the localizing closures.
Source: blueprint det-sf-mate-open-restriction (1)
(blueprint: det-sf-mate-open-restriction). -/
def mateOpenExtension {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (h : ∀ K : (localizingClosureProEtale Λ U).FullSubcategory,
      localizingClosureProEtale Λ X
        ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj K.obj)) :
    (localizingClosureProEtale Λ U).FullSubcategory ⥤
      (localizingClosureProEtale Λ X).FullSubcategory :=
  (localizingClosureProEtale Λ X).lift
    ((localizingClosureProEtale Λ U).ι ⋙
      (openImmersionLowerShriek Λ j).mapDerivedCategory) h

/-- Canonical composition of open extensions: the left-adjoint comparison of the exact
open adjunctions and the coefficient-compatible inverse-image compositor.
Source: blueprint det-sf-mate-open-restriction (2), composite adjunction calculation
(blueprint: det-sf-mate-open-restriction). -/
def mateOpenExtensionComp {U X Z : Scheme.{u}} (j : U ⟶ X) (i : X ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion i] :
    (openImmersionLowerShriek Λ j).mapDerivedCategory ⋙
        (openImmersionLowerShriek Λ i).mapDerivedCategory ≅
      (openImmersionLowerShriek Λ (j ≫ i)).mapDerivedCategory :=
  Adjunction.leftAdjointUniq
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).comp
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i))
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (j ≫ i)).ofNatIsoRight
      (Functor.mapDerivedCategoryNatIso (upperStarComp Λ j i) ≪≫
        Functor.mapDerivedCategoryCompIso (upperStar Λ i) (upperStar Λ j)))

/-- The lower-shriek compositor when the first morphism is open, computed in the
compactification with the same proper map. This fixes the source comparison's normalization.
Source: blueprint det-sf-mate-open-restriction (2)
(blueprint: det-sf-mate-open-restriction). -/
def mateOpenSourceLowerShriek {U X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (j : U ⟶ X) [IsOpenImmersion j] :
    (openImmersionLowerShriek Λ j).mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification Λ c ≅
      rightDerivedLowerShriekOfCompactification Λ (c.precomp j) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (mateOpenExtensionComp Λ j c.i)
      (lowerStar Λ c.g).rightDerivedFunctor

/-- The ordinary restriction mate for a commutative proper/open square. It is defined
using only the coefficient-compatible pullback compositor and the direct-image counit.
Source: blueprint det-sf-mate-open-restriction (2), canonical comparison in the open square
(blueprint: det-sf-mate-open-restriction). -/
def mateOpenProperRestriction {Z Z' Y V : Scheme.{u}}
    {a : Z' ⟶ Z} {q : Z' ⟶ V} {p : Z ⟶ Y} {v : V ⟶ Y}
    (sq : CommSq a q p v)
    (B : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    (upperStar Λ v).mapDerivedCategory.obj ((lowerStar Λ p).rightDerivedFunctor.obj B) ⟶
      (lowerStar Λ q).rightDerivedFunctor.obj ((upperStar Λ a).mapDerivedCategory.obj B) :=
  ((derivedUpperStarLowerStarAdjunction Λ q).ofNatIsoLeft
    (leftDerivedUpperStarIsoMapDerivedCategory Λ q)).homEquiv _ _
      (((Functor.mapDerivedCategoryCompIso (upperStar Λ v) (upperStar Λ q)).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          ((upperStarComp Λ q v).symm ≪≫
            eqToIso (congrArg (upperStar Λ) sq.w.symm) ≪≫ upperStarComp Λ a p) ≪≫
        Functor.mapDerivedCategoryCompIso (upperStar Λ p) (upperStar Λ a)).hom.app
          ((lowerStar Λ p).rightDerivedFunctor.obj B) ≫
        (upperStar Λ a).mapDerivedCategory.map
          (((derivedUpperStarLowerStarAdjunction Λ p).ofNatIsoLeft
            (leftDerivedUpperStarIsoMapDerivedCategory Λ p)).counit.app B))

/-- The open square identifies the two composites of extensions by zero. Its components
are fixed by the units of the open adjunctions, including the coefficient actions.
Source: blueprint det-sf-mate-open-restriction (2)
(blueprint: det-sf-mate-open-restriction). -/
def mateOpenSquareExtension {U X V Y : Scheme.{u}}
    {a : U ⟶ X} {q : U ⟶ V} {f : X ⟶ Y} {v : V ⟶ Y}
    [IsOpenImmersion a] [IsOpenImmersion v]
    (sq : IsPullback a q f v) (c : Compactification f) :
    (openImmersionLowerShriek Λ a).mapDerivedCategory ⋙
        (openImmersionLowerShriek Λ c.i).mapDerivedCategory ≅
      (openImmersionLowerShriek Λ (c.ofIsPullback sq).i).mapDerivedCategory ⋙
        (openImmersionLowerShriek Λ (pullback.fst c.g v)).mapDerivedCategory :=
  mateOpenExtensionComp Λ a c.i ≪≫
    Functor.mapDerivedCategoryNatIso
      (eqToIso (by
        congr 1
        exact (c.ofIsPullback_i_fst sq).symm)) ≪≫
    (mateOpenExtensionComp Λ (c.ofIsPullback sq).i (pullback.fst c.g v)).symm

/-- The specified component `v* Rf! u! M → Rf_V! M`: first identify the composite open
extensions, then apply the proper/open restriction mate, and undo the open unit on the
base-changed compactification. Thus this is a real map before invertibility is asserted.
Source: blueprint det-sf-mate-open-restriction (2), Cartesian open square
(blueprint: det-sf-mate-open-restriction). -/
def mateOpenTargetLowerShriek {U X V Y : Scheme.{u}}
    {a : U ⟶ X} {q : U ⟶ V} {f : X ⟶ Y} {v : V ⟶ Y}
    [IsOpenImmersion a] [IsOpenImmersion v]
    (sq : IsPullback a q f v) (c : Compactification f)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))) :
    (upperStar Λ v).mapDerivedCategory.obj
        ((rightDerivedLowerShriekOfCompactification Λ c).obj
          ((openImmersionLowerShriek Λ a).mapDerivedCategory.obj M)) ⟶
      (rightDerivedLowerShriekOfCompactification Λ (c.ofIsPullback sq)).obj M :=
  (upperStar Λ v).mapDerivedCategory.map
      ((lowerStar Λ c.g).rightDerivedFunctor.map
        ((mateOpenSquareExtension Λ sq c).hom.app M)) ≫
    mateOpenProperRestriction Λ (IsPullback.of_hasPullback c.g v).toCommSq
      ((openImmersionLowerShriek Λ (pullback.fst c.g v)).mapDerivedCategory.obj
        ((openImmersionLowerShriek Λ (c.ofIsPullback sq).i).mapDerivedCategory.obj M)) ≫
    (lowerStar Λ (pullback.snd c.g v)).rightDerivedFunctor.map
      (inv ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ
        (pullback.fst c.g v)).unit.app
          ((openImmersionLowerShriek Λ (c.ofIsPullback sq).i).mapDerivedCategory.obj M)))

/-- The canonical identification of compact-support image for the trivial open
compactification (j,id) with levelwise extension by zero. The identity direct-image
identification is the derived one normalized on ordinary module sheaves.
Source: blueprint det-sf-mate-open-restriction (1), trivial compactification
(blueprint: det-sf-mate-open-restriction). -/
def mateOpenTrivialLowerShriek {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    rightDerivedLowerShriekOfCompactification Λ (Compactification.ofIsOpenImmersion j) ≅
      (openImmersionLowerShriek Λ j).mapDerivedCategory :=
  Functor.isoWhiskerLeft (openImmersionLowerShriek Λ j).mapDerivedCategory
      (refinementDerivedLowerStarId Λ X) ≪≫
    Functor.rightUnitor _

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

/-- Target-open restriction u* f! = f_V! v*, with its precise mate normalization.
The inverse-image scheme U is expressed by an arbitrary Cartesian open square, including
its identity and empty cases. The base-changed compactification is the recorded upstream
construction c.ofIsPullback. The equation is in the ambient derived module category and
thus, by fullness, also in its localizing subcategory. It fixes e uniquely.
Source: blueprint det-sf-mate-open-restriction (2), target-open comparison
(blueprint: det-sf-mate-open-restriction).

Proof (DAG steps 4--7): openImmersionLowerShriek_localizing and
unboundedLocalizingPullback give he, hs and hv. Separated finite type is stable under
base change, so all four schemes and maps remain in the standing setting. Brown hypotheses
and det-sf-existence-brown applied to the base-changed compactification give hq and a right
adjoint. The open comparisons of clause (1) and the composition of exceptional inverse
images give u* f! = u! f! = (fu)! = (vf_V)! = f_V! v! = f_V! v*.
Composition comes from lem-sfb-localizing-lower-shriek-composition for rational coefficients
and lem-sfb-nonrational-localizing-lower-shriek-composition for the other cases. Their Hom
bijections are the composite adjunction; Yoneda supplies naturality. On the common
base-changed compactification, transpose these same bijections. The open compositors give
mateOpenSquareExtension, the direct-image counit gives mateOpenProperRestriction, and the
inverse open unit gives mateOpenTargetLowerShriek. Thus the transposed comparison satisfies
the displayed equation. Open restriction of proper direct image identifies that map with
the ordinary open restriction, so it is invertible (termwise on K-injectives, which remain
K-injective because open extension is exact). Its Hom bijections give uniqueness of e.
Brown's adjunction-compatible compactification comparisons identify this with the same
comparison for any chosen compactifications. -/
theorem mateOpenTargetRestriction
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
  sorry

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
