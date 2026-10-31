/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.AlgebraicGeometry.ClosedTestDerivedExchangeModel.ClosedTestDerivedExchangeModel
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedExchangeOpenRestriction
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoverRestrictionConservative

/-! # Affine descent for degree-zero condensed closed exchange

Source: Stacks 0D6F and 07A7, and the affine-local final step of
lem-sfb-proper-constructible-closed-exchange-heart.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w₁ w₂

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

-- Choose the published structures so derived-functor arguments share the same data.
attribute [local instance 4000]
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  CategoryTheory.Mod.instAbelian
attribute [local instance 5000] AlgebraicGeometry.ProEtale.sheafMonoidalCategory

attribute [local irreducible] upperStar lowerStar upperStarFromPoint
  condensedAmbientExchange moduleObjectDerivedPushforward moduleObjectDerivedPullback
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Functor.mapDerivedCategorySingleFunctor
  ClosedTestDerivedExchangeModel.pull ClosedTestDerivedExchangeModel.sectionsOver
  ClosedTestDerivedExchangeModel.exchange

/-- Normalize the packaged coefficient parameter before applying cover conservativity
at a concrete exchange map. Keeping its morphism abstract prevents kernel reduction
of the concrete tensor pullback constructions while comparing the coefficient records. -/
private theorem isIso_iff_on_condensed_cover
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u})
    {ι : Type*} (U : ι → Scheme.{u}) (b : ∀ i, U i ⟶ T)
    (hcov : Presieve.ofArrows U b ∈ Scheme.proetalePrecoverage T)
    (P Q : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)))
    (φ : P ⟶ Q) :
    IsIso φ ↔ ∀ i, IsIso ((upperStar Λ (b i)).mapDerivedCategory.map φ) := by
  exact (condensed_cover_restriction_conservative (Mon.mk Λ) T
    { I₀ := ι, X := U, f := b, mem₀ := hcov }).1 P Q φ

/-- The usual single-functor comparison, with its endpoints normalized before
specializing an exact functor. -/
private noncomputable def exactSingleIso
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (M : A) :
    (Functor.mapDerivedCategory.{w₁, w₂} F).obj
        ((DerivedCategory.singleFunctor.{w₁} A 0).obj M) ≅
      (DerivedCategory.singleFunctor.{w₂} B 0).obj (F.obj M) :=
  (Functor.mapDerivedCategorySingleFunctor.{w₁, w₂} F 0).app M

attribute [local irreducible] exactSingleIso

/-- Transport the component of an arbitrary natural transformation across the exact
pullback single-functor isomorphism, with the module categories fixed. -/
private theorem isIso_at_pullback_single_iff
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X V : Scheme.{u}} (a : V ⟶ X)
    {D : Type*} [Category D]
    {G H : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V)) ⥤ D}
    (α : G ⟶ H)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsIso (α.app ((upperStar Λ a).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor _ 0).obj M))) ↔
      IsIso (α.app ((DerivedCategory.singleFunctor _ 0).obj ((upperStar Λ a).obj M))) := by
  exact NatTrans.isIso_app_iff_of_iso α (exactSingleIso (upperStar Λ a) M)

/-- Apply the single-open comparison after transporting the degree-zero input. -/
private theorem isIso_restricted_exchange_of_single
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y U XU YU' XU' : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    (v : U ⟶ Y) [IsOpenImmersion v]
    (a : XU ⟶ X) (fU : XU ⟶ U)
    (b : YU' ⟶ Y') (gU : YU' ⟶ U)
    (hU : XU' ⟶ XU) (fU' : XU' ⟶ YU')
    (wf : IsPullback a fU f v) (wg : IsPullback b gU g v)
    (w : IsPullback hU fU' fU gU)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hi : IsIso ((ClosedTestDerivedExchangeModel.exchange Λ w.toCommSq).app
      ((DerivedCategory.singleFunctor _ 0).obj ((upperStar Λ a).obj M)))) :
    IsIso ((upperStar Λ b).mapDerivedCategory.map
      ((condensedAmbientExchange Λ sq).app ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  have hi' := (isIso_at_pullback_single_iff Λ a
    (ClosedTestDerivedExchangeModel.exchange Λ w.toCommSq) M).mpr hi
  exact (condensed_exchange_one_open_restriction Λ sq v a fU b gU hU fU' wf wg w
    ((DerivedCategory.singleFunctor _ 0).obj M)).mpr hi'

/-- Affine quotient charts detect the actual closed exchange on a module in degree zero.
There is no properness, coefficient admissibility or constructibility assumption.

Source: Stacks 0D6F and 07A7; blueprint latest, compactification coherence refinement,
paragraph (2), affine localization and open descent
(blueprint: lem-sfb-condensed-closed-exchange-affine-descent).

Proof: Cover Y by affine opens U=Spec A. The pullback of c is a closed immersion
into U, hence is canonically isomorphic over U to Spec(A/I), for its defining ideal I.
These quotient charts also cover C after inverse image. Form the three pullback
squares displayed in the hypothesis. Ringed slice localization identifies restriction
of the derived direct images with the direct images of the restricted sheaves.
The exact-pullback single-functor comparison identifies restriction of M[0] with
(a^*M)[0]. Localization preserves the adjunction units and counits and pullback
composition; consequently the restriction of the actual mate is the localized mate,
conjugated by these canonical isomorphisms. The exact-versus-left-derived pullback
comparison identifies the local exact-pullback mate with the actual ambient mate,
preserving its adjunction units, counits and square comparison. The internal/section-module
equivalence
preserves those adjunctions, so ringed open descent applies to the actual condensed
mate. The hypothesis makes every such local mate invertible. Conservativity on the
inverse-image open cover of C proves the conclusion. The empty cover handles empty Y.
-/
theorem condensed_closed_exchange_affine_descent
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y C : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (c : C ⟶ Y) [IsClosedImmersion c]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hloc : ∀ (A : Type u) [CommRing A] (I : Ideal A)
      (XU XZ : Scheme.{u}) (v : Spec (.of A) ⟶ Y) [IsOpenImmersion v]
      (a : XU ⟶ X) (fU : XU ⟶ Spec (.of A))
      (b : Spec (.of (A ⧸ I)) ⟶ C)
      (h : XZ ⟶ XU) (fZ : XZ ⟶ Spec (.of (A ⧸ I)))
      (_wf : IsPullback a fU f v)
      (_wc : IsPullback b (ClosedTestDerivedExchangeModel.closedMap A I) c v)
      (w : IsPullback h fZ fU (ClosedTestDerivedExchangeModel.closedMap A I)),
      IsIso ((ClosedTestDerivedExchangeModel.exchange Λ w.toCommSq).app
          ((DerivedCategory.singleFunctor _ 0).obj ((upperStar Λ a).obj M)))) :
    IsIso ((condensedAmbientExchange Λ
      (g' := pullback.fst f c) (f' := pullback.snd f c) (f := f) (g := c)
      { w := pullback.condition
        isoPullback := Iso.refl _
        hom_fst := Category.id_comp _
        hom_snd := Category.id_comp _ }).app ((DerivedCategory.singleFunctor _ 0).obj M)) := by
  classical
  obtain ⟨𝒱⟩ : Nonempty Y.AffineOpenCover := ⟨Y.affineOpenCover⟩
  let A (i : 𝒱.I₀) := 𝒱.X i
  let v (i : 𝒱.I₀) : Spec (A i) ⟶ Y := 𝒱.f i
  have closed (i : 𝒱.I₀) : IsClosedImmersion (pullback.snd c (v i)) := inferInstance
  obtain ⟨I, e, he⟩ : ∃ (I : ∀ i : 𝒱.I₀, Ideal (A i))
      (e : ∀ i : 𝒱.I₀, pullback c (v i) ≅ Spec (.of (A i ⧸ I i))),
      ∀ i, pullback.snd c (v i) = (e i).hom ≫
        ClosedTestDerivedExchangeModel.closedMap (A i) (I i) := by
    choose I e he using fun i ↦ (IsClosedImmersion.Spec_iff).mp (closed i)
    exact ⟨I, e, he⟩
  let b (i : 𝒱.I₀) : Spec (.of (A i ⧸ I i)) ⟶ C :=
    (e i).inv ≫ pullback.fst c (v i)
  have wc (i : 𝒱.I₀) : IsPullback (b i)
      (ClosedTestDerivedExchangeModel.closedMap (A i) (I i)) c (v i) := by
    apply (IsPullback.of_hasPullback c (v i)).of_iso
      (e i) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simp [b]
    · simpa only [Iso.refl_hom, Category.comp_id] using he i
    · simp
    · simp
  let 𝒲 := 𝒱.openCover.pullback₁ c
  let 𝒰 : C.OpenCover := Scheme.Cover.copy 𝒲 𝒱.I₀
    (fun i ↦ Spec (.of (A i ⧸ I i))) b (Equiv.refl _) (fun i ↦ (e i).symm)
    (fun _ ↦ rfl)
  let 𝒰p : Scheme.Cover Scheme.proetalePrecoverage C :=
    (𝒰.changeProp (Q := @Etale) (fun _ ↦ inferInstance)).weaken
      Scheme.etalePrecoverage_le_proetalePrecoverage
  -- Keep the canonical exchange expression identical in the local and global checks.
  have localIso (i : 𝒱.I₀) :
      IsIso ((upperStar Λ (b i)).mapDerivedCategory.map
        ((condensedAmbientExchange Λ
          (g' := pullback.fst f c) (f' := pullback.snd f c) (f := f) (g := c)
          { w := pullback.condition
            isoPullback := Iso.refl _
            hom_fst := Category.id_comp _
            hom_snd := Category.id_comp _ }).app
          ((DerivedCategory.singleFunctor _ 0).obj M))) := by
    let vi : Spec (.of (A i)) ⟶ Y := v i
    have : IsOpenImmersion vi := by dsimp [vi]; infer_instance
    let fU : pullback f vi ⟶ Spec (.of (A i)) := pullback.snd f vi
    let a : pullback f vi ⟶ X := pullback.fst f vi
    let s := ClosedTestDerivedExchangeModel.closedMap (A i) (I i)
    let h : pullback fU s ⟶ pullback f vi := pullback.fst fU s
    let fZ : pullback fU s ⟶ Spec (.of (A i ⧸ I i)) := pullback.snd fU s
    have wci : IsPullback (b i)
        (ClosedTestDerivedExchangeModel.closedMap (A i) (I i)) c vi := wc i
    have w : IsPullback h fZ fU
        (ClosedTestDerivedExchangeModel.closedMap (A i) (I i)) :=
      .of_hasPullback fU s
    have hi := hloc (A i) (I i) (pullback f vi) (pullback fU s) vi
      a fU (b i) h fZ (.of_hasPullback f vi) wci w
    exact isIso_restricted_exchange_of_single Λ
      (X' := pullback f c) (X := X) (Y' := C) (Y := Y)
      (U := Spec (.of (A i))) (XU := pullback f vi)
      (YU' := Spec (.of (A i ⧸ I i))) (XU' := pullback fU s)
      (g' := pullback.fst f c) (f' := pullback.snd f c) (f := f) (g := c)
      { w := pullback.condition
        isoPullback := Iso.refl _
        hom_fst := Category.id_comp _
        hom_snd := Category.id_comp _ }
      vi a fU (b i) (ClosedTestDerivedExchangeModel.closedMap (A i) (I i))
      h fZ (.of_hasPullback f vi) wci w M hi
  exact (isIso_iff_on_condensed_cover Λ C
    (fun i ↦ Spec (.of (A i ⧸ I i))) b 𝒰p.mem₀ _ _
    ((condensedAmbientExchange Λ
      (g' := pullback.fst f c) (f' := pullback.snd f c) (f := f) (g := c)
      { w := pullback.condition
        isoPullback := Iso.refl _
        hom_fst := Category.id_comp _
        hom_snd := Category.id_comp _ }).app
          ((DerivedCategory.singleFunctor _ 0).obj M))).mpr localIso

end AlgebraicGeometry.ProEtale.CondensedRing
