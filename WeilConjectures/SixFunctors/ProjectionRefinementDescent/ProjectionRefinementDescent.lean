/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProjectionRefinementDescent.ProjectionRefinementData
import WeilConjectures.SixFunctors.ProjectionRefinementDescent.ProjectionRefinementInputs
import WeilConjectures.SixFunctors.ProjectionRefinementDescent.ProjectionRefinementSquare
import WeilConjectures.SixFunctors.ProjectionRefinementDescent.ProjectionRefinementComparisons
import WeilConjectures.Compactification.CategoryBaseChange

/-! # Projection descent from witnessed refinement squares

Source: current blueprint, fix-prop-projection-formula.proof.md, refinement sentence;
Stacks 0F7B, 0F7G, 0B56 and 0DV0.
(blueprint: lem-sf-projection-refinement-descent).
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace WeilConjectures.ProjectionRefinementDescent

attribute [local irreducible] Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  HasDerivedCategory.ofHasKInjectiveResolutions DerivedCategory
  projectionMapOfCompactification
  AlgebraicGeometry.ProEtale.derivedTensor theta

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ)

attribute [local implicit_reducible] tensorInput derivedTensorRightDerivedLowerShriek
  rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar

private theorem restriction_component
    {B C D : Type*} [Category B] [Category C] [Category D]
    (P : ObjectProperty B) (Q : ObjectProperty C)
    {F G : B ⥤ C ⥤ D} (a : F ⟶ G)
    (K : P.FullSubcategory) (L : Q.FullSubcategory) :
    (Functor.whiskerLeft (P.ι.prod Q.ι) (Functor.uncurry.map a)).app (K, L) =
      (a.app K.obj).app L.obj := by
  rfl

private theorem native_component_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : ProperOpenDerived A X) (L : ProperOpenDerived A Y) :
    ((AmbientProperOpen.RefinementProjection.finiteProjection A c).app K).app L =
      coefficientProjectionComponent A c K L := by
  rfl

private def restricted_projection
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    (P : ObjectProperty (ProperOpenDerived A X))
    (Q : ObjectProperty (ProperOpenDerived A Y)) (c : Compactification f) :
    P.ι.prod Q.ι ⋙ Functor.uncurry.obj (coefficientProjectionSource A c) ⟶
      P.ι.prod Q.ι ⋙ Functor.uncurry.obj (coefficientProjectionTarget A c) :=
  Functor.whiskerLeft (P.ι.prod Q.ι)
    (Functor.uncurry.map (AmbientProperOpen.RefinementProjection.finiteProjection A c))

private theorem restricted_projection_app
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    (P : ObjectProperty (ProperOpenDerived A X))
    (Q : ObjectProperty (ProperOpenDerived A Y)) (c : Compactification f)
    (K : P.FullSubcategory) (L : Q.FullSubcategory) :
    (restricted_projection A P Q c).app (K, L) =
      coefficientProjectionComponent A c K.obj L.obj := by
  calc
    (restricted_projection A P Q c).app (K, L) =
        ((AmbientProperOpen.RefinementProjection.finiteProjection A c).app K.obj).app
          L.obj := by
      exact restriction_component P Q
        (AmbientProperOpen.RefinementProjection.finiteProjection A c) K L
    _ = coefficientProjectionComponent A c K.obj L.obj :=
      native_component_eq A c K.obj L.obj

private theorem descend_square
    {A : Type*} [Category A] {B : Type*} [Category B]
    (F : A ⥤ B) {a b c : A} {x y z : B}
    (s : a ≅ b) (t : a ≅ c) (v : x ≅ y) (w : x ≅ z)
    (p : F.obj a ⟶ x) (q : F.obj b ⟶ y) (r : F.obj c ⟶ z)
    (hq : p ≫ v.hom = F.map s.hom ≫ q)
    (hr : p ≫ w.hom = F.map t.hom ≫ r) :
    q ≫ (v.symm ≪≫ w).hom = F.map (s.symm ≪≫ t).hom ≫ r := by
  apply (cancel_epi (F.map s.hom)).mp
  calc
    F.map s.hom ≫ (q ≫ (v.symm ≪≫ w).hom) = p ≫ w.hom := by
      rw [← Category.assoc, ← hq]
      simp
    _ = F.map t.hom ≫ r := hr
    _ = F.map s.hom ≫ (F.map (s.symm ≪≫ t).hom ≫ r) := by
      simp [← CategoryTheory.Functor.map_comp, ← Category.assoc]

private theorem descend_coefficient_square
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (b c d : Compactification f)
    (K : ProperOpenDerived A X) (L : ProperOpenDerived A Y)
    (s : (coefficientImage A b).obj K ≅ (coefficientImage A c).obj K)
    (t : (coefficientImage A b).obj K ≅ (coefficientImage A d).obj K)
    (v : (coefficientImage A b).obj
        (((ProperOpenTensor A X).obj K).obj ((ProperOpenPull A f).obj L)) ≅
      (coefficientImage A c).obj
        (((ProperOpenTensor A X).obj K).obj ((ProperOpenPull A f).obj L)))
    (w : (coefficientImage A b).obj
        (((ProperOpenTensor A X).obj K).obj ((ProperOpenPull A f).obj L)) ≅
      (coefficientImage A d).obj
        (((ProperOpenTensor A X).obj K).obj ((ProperOpenPull A f).obj L)))
    (hq : coefficientProjectionComponent A b K L ≫ v.hom =
      ((ProperOpenTensor A Y).map s.hom).app L ≫ coefficientProjectionComponent A c K L)
    (hr : coefficientProjectionComponent A b K L ≫ w.hom =
      ((ProperOpenTensor A Y).map t.hom).app L ≫ coefficientProjectionComponent A d K L) :
    coefficientProjectionComponent A c K L ≫ (v.symm ≪≫ w).hom =
      ((ProperOpenTensor A Y).map (s.symm ≪≫ t).hom).app L ≫
        coefficientProjectionComponent A d K L := by
  exact descend_square ((ProperOpenTensor A Y).flip.obj L) s t v w
    (coefficientProjectionComponent A b K L)
    (coefficientProjectionComponent A c K L)
    (coefficientProjectionComponent A d K L) hq hr

private theorem descend_restricted_square
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    (P : ObjectProperty (ProperOpenDerived A X))
    (Q : ObjectProperty (ProperOpenDerived A Y)) (b c d : Compactification f)
    (K : P.FullSubcategory) (L : Q.FullSubcategory)
    (s : (coefficientImage A b).obj K.obj ≅ (coefficientImage A c).obj K.obj)
    (t : (coefficientImage A b).obj K.obj ≅ (coefficientImage A d).obj K.obj)
    (v : (coefficientImage A b).obj
        (((ProperOpenTensor A X).obj K.obj).obj ((ProperOpenPull A f).obj L.obj)) ≅
      (coefficientImage A c).obj
        (((ProperOpenTensor A X).obj K.obj).obj ((ProperOpenPull A f).obj L.obj)))
    (w : (coefficientImage A b).obj
        (((ProperOpenTensor A X).obj K.obj).obj ((ProperOpenPull A f).obj L.obj)) ≅
      (coefficientImage A d).obj
        (((ProperOpenTensor A X).obj K.obj).obj ((ProperOpenPull A f).obj L.obj)))
    (rhoK : (coefficientImage A c).obj K.obj ⟶ (coefficientImage A d).obj K.obj)
    (rhoT : (coefficientImage A c).obj
        (((ProperOpenTensor A X).obj K.obj).obj ((ProperOpenPull A f).obj L.obj)) ⟶
      (coefficientImage A d).obj
        (((ProperOpenTensor A X).obj K.obj).obj ((ProperOpenPull A f).obj L.obj)))
    (hK : rhoK = (s.symm ≪≫ t).hom) (hT : rhoT = (v.symm ≪≫ w).hom)
    (hq : coefficientProjectionComponent A b K.obj L.obj ≫ v.hom =
      ((ProperOpenTensor A Y).map s.hom).app L.obj ≫
        coefficientProjectionComponent A c K.obj L.obj)
    (hr : coefficientProjectionComponent A b K.obj L.obj ≫ w.hom =
      ((ProperOpenTensor A Y).map t.hom).app L.obj ≫
        coefficientProjectionComponent A d K.obj L.obj) :
    coefficientProjectionComponent A c K.obj L.obj ≫ rhoT =
      ((ProperOpenTensor A Y).map rhoK).app L.obj ≫
        (restricted_projection A P Q d).app (K, L) := by
  have h : coefficientProjectionComponent A c K.obj L.obj ≫ rhoT =
      ((ProperOpenTensor A Y).map rhoK).app L.obj ≫
        coefficientProjectionComponent A d K.obj L.obj := by
    rw [hK, hT]
    exact descend_coefficient_square A b c d K.obj L.obj s t v w hq hr
  exact h.trans (congrArg (fun a ↦ ((ProperOpenTensor A Y).map rhoK).app L.obj ≫ a)
    (restricted_projection_app A P Q d K L).symm)

/-- Projection mates descend to one natural transformation independent of compactification.
The comparison family below is normalized on every common refinement by the recorded
witnessed theta and satisfies the cocycle. The last equation identifies the descended
natural transformation with each actual compactification projection, on all input pairs.
There is no assumption that any projection map is invertible.

Source: current blueprint, fix-prop-projection-formula.proof.md, refinement sentence;
Stacks Tags 0F7B, 0F7G, 0B56, 0DV0
(blueprint: lem-sf-projection-refinement-descent).

Proof:
1. Apply tensor_and_origins: the existing finite-ring origin theorem supplies a
   retained origin for any bounded constructible object, and the proved intrinsic
   projection-domain theorem supplies tensor closure. Apply origin existence to
   both K and its tensor, with no finite-Tor assumption on K.
2. Apply refinement_square. It combines the directed proper/open projection square
   with normalized_refinement_inverse and cancels the two comparison inverse pairs.
3. Apply comparison_cocycle: extend the existing compactification comparisons from
   the fully faithful origin category along Mathlib's essential-image lift. Its
   naturality gives normalization for every retained witness and the cocycle.
4. Restrict the actual projection natural transformation at a chosen c0 to the
   input full subcategories, giving tau. Choose a common refinement of c and c0.
   Apply the refinement square to both legs. Cancel only comparison isomorphisms;
   normalization of rho identifies the two composites with rho(c,c0) at K and T.
5. The system clause below is the existing intrinsic proper/open mate identity,
   specialized at the identity left proper map, without detection by evaluation.
-/
theorem finite_descent (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra ℚ_[C.l] E] [FiniteDimensional ℚ_[C.l] E]
    (n : ℕ) (_S : SixFunctorOperationDatum D C E (n + 1) (Nat.succ_pos n))
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    (∀ (K : (boundedConstructible C.l E n X).FullSubcategory)
      (L : (finiteTor C.l E n Y).FullSubcategory),
      boundedConstructible C.l E n X (tensorInput C.l E n f K.obj L.obj) ∧
      (∃ O : RefinementFiniteLevelOrigin C.l E (n + 1) (Nat.succ_pos n) X,
        Nonempty (refinementFiniteLevelFixedObject C.l E (n + 1) (Nat.succ_pos n) X O ≅
          K.obj)) ∧
      (∃ OT : RefinementFiniteLevelOrigin C.l E (n + 1) (Nat.succ_pos n) X,
        Nonempty (refinementFiniteLevelFixedObject C.l E (n + 1) (Nat.succ_pos n) X OT ≅
          tensorInput C.l E n f K.obj L.obj))) ∧
    (∀ (c d : Compactification f) (r : c.Refinement d)
      (K : (boundedConstructible C.l E n X).FullSubcategory)
      (L : (finiteTor C.l E n Y).FullSubcategory),
      refinementLaw C.l E n c d r K L) ∧
    ∃ rho : ∀ c d : Compactification f,
        (boundedConstructible C.l E n X).ι ⋙ image C.l E n c ≅
          (boundedConstructible C.l E n X).ι ⋙ image C.l E n d,
      (∀ (c d b : Compactification f) (r : b.Refinement c) (s : b.Refinement d)
        (K : (boundedConstructible C.l E n X).FullSubcategory)
        (O : RefinementFiniteLevelOrigin C.l E (n + 1) (Nat.succ_pos n) X)
        (e : refinementFiniteLevelFixedObject C.l E (n + 1) (Nat.succ_pos n) X O ≅ K.obj),
        (rho c d).app K = (theta C.l E n r K.obj O e).symm ≪≫
          theta C.l E n s K.obj O e) ∧
      (∀ c d b : Compactification f, rho c d ≪≫ rho d b = rho c b) ∧
      ∀ c₀ : Compactification f,
        ∃ tau : source C.l E n c₀ ⟶ target C.l E n c₀,
          ∀ (c : Compactification f)
            (K : (boundedConstructible C.l E n X).FullSubcategory)
            (L : (finiteTor C.l E n Y).FullSubcategory)
            (hT : boundedConstructible C.l E n X (tensorInput C.l E n f K.obj L.obj)),
          coefficientProjectionComponent (Coefficient C.l E n) c K.obj L.obj ≫
            (rho c c₀).hom.app ⟨tensorInput C.l E n f K.obj L.obj, hT⟩ =
          ((ProperOpenTensor (Coefficient C.l E n) Y).map ((rho c c₀).hom.app K)).app
              L.obj ≫ tau.app (K, L) := by
  classical
  obtain ⟨origins, tensors⟩ := tensor_and_origins D C E n _S f
  have squares := refinement_square D C E n f
  obtain ⟨rho, normalization, cocycle⟩ := comparison_cocycle D C E n f origins
  refine ⟨?_, squares, rho, normalization, cocycle, ?_⟩
  · intro K L
    have hT := tensors K L
    exact ⟨hT, origins K, origins ⟨tensorInput C.l E n f K.obj L.obj, hT⟩⟩
  · intro c₀
    let tau : source C.l E n c₀ ⟶ target C.l E n c₀ :=
      restricted_projection (Coefficient C.l E n)
        (boundedConstructible C.l E n X) (finiteTor C.l E n Y) c₀
    refine ⟨tau, ?_⟩
    intro c K L hT
    have : IsCofiltered (Compactification f) :=
      Compactification.isCofiltered_of_field (X ↘ Spec (.of D.k))
        (Y ↘ Spec (.of D.k)) f (comp_over f _)
    let b := IsCofiltered.min c c₀
    let r : b.Refinement c := IsCofiltered.minToLeft c c₀
    let s : b.Refinement c₀ := IsCofiltered.minToRight c c₀
    obtain ⟨O, ⟨e⟩⟩ := origins K
    obtain ⟨OT, ⟨eT⟩⟩ := origins ⟨tensorInput C.l E n f K.obj L.obj, hT⟩
    have hK := congrArg Iso.hom (normalization c c₀ b r s K O e)
    have hTensor := congrArg Iso.hom
      (normalization c c₀ b r s ⟨tensorInput C.l E n f K.obj L.obj, hT⟩ OT eT)
    change (rho c c₀).hom.app K = _ at hK
    change (rho c c₀).hom.app ⟨tensorInput C.l E n f K.obj L.obj, hT⟩ = _ at hTensor
    have hr := squares b c r K L O e OT eT
    have hs := squares b c₀ s K L O e OT eT
    exact descend_restricted_square (Coefficient C.l E n)
      (boundedConstructible C.l E n X) (finiteTor C.l E n Y) b c c₀ K L
      (theta C.l E n r K.obj O e) (theta C.l E n s K.obj O e)
      (theta C.l E n r (tensorInput C.l E n f K.obj L.obj) OT eT)
      (theta C.l E n s (tensorInput C.l E n f K.obj L.obj) OT eT)
      ((rho c c₀).hom.app K)
      ((rho c c₀).hom.app ⟨tensorInput C.l E n f K.obj L.obj, hT⟩)
      hK hTensor hr hs

end WeilConjectures.ProjectionRefinementDescent

namespace WeilConjectures.IntegralSystemRealization

end WeilConjectures.IntegralSystemRealization
