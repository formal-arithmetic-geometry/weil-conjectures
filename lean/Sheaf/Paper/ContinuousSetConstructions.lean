/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.ProfinitePointPullback
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant

import Mathlib.AlgebraicGeometry.Limits

/-! # Continuous-set coefficient constructions

Shared definitions for the normalized realization and its proof dependencies.
Source: Hemo--Richarz--Scholbach, Example 3.1; Bhatt--Scholze, Lemma 4.2.12.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Restriction of Mathlib's continuous-map presheaf to the small pro-etale site.
Source: Bhatt--Scholze, Lemma 4.2.12
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
abbrev continuousSetPresheaf (X : Scheme.{u}) (D : Type (u + 1)) [TopologicalSpace D] :=
  (Scheme.ProEt.forget X ⋙ Over.forget X).op ⋙ continuousMapPresheaf D

/-- Continuous functions satisfy descent on the small pro-etale site.
Source: Bhatt--Scholze, Lemma 4.2.12
(blueprint: lem-sfb-continuous-set-proetale-descent).
Proof: continuous functions form an fpqc sheaf by quotient-map descent. Restrict this
sheaf along the forgetful functor from the small pro-etale site, whose covering families
are fpqc covering families. This proves the first assertion of Bhatt--Scholze Lemma 4.2.12. -/
theorem continuousSetPresheaf_isSheaf (X : Scheme.{u}) (D : Type (u + 1))
    [TopologicalSpace D] :
    Presheaf.IsSheaf (Scheme.ProEt.topology X) (continuousSetPresheaf X D) := by
  exact (Scheme.ProEt.forget X ⋙ Over.forget X).op_comp_isSheaf_of_isSheaf _
    Scheme.proetaleTopology (continuousMapPresheaf D)
    (.of_le Scheme.proetaleTopology_le_fpqcTopology
      (isSheaf_fpqcTopology_continuousMapPresheaf D))

/-- The actual sheaf of continuous functions, with no sheafification of its sections.
Source: Bhatt--Scholze, Lemma 4.2.12
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
noncomputable def continuousSetSheaf (X : Scheme.{u}) (D : Type (u + 1))
    [TopologicalSpace D] : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)) :=
  ⟨continuousSetPresheaf X D, continuousSetPresheaf_isSheaf X D⟩

/-- Postcomposition of continuous sections with a continuous coefficient map.
Source: Hemo--Richarz--Scholbach, Example 3.1
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
def continuousSetSheafMap (X : Scheme.{u}) {D E : Type (u + 1)}
    [TopologicalSpace D] [TopologicalSpace E] (h : C(D, E)) :
    continuousSetSheaf X D ⟶ continuousSetSheaf X E :=
  ⟨{ app := fun _ ↦ ↾fun s ↦ h.comp s, naturality := fun _ _ _ ↦ rfl }⟩

/-- The existing Mathlib continuous-function sheaf functor on profinite sets.
Source: Hemo--Richarz--Scholbach, Example 3.1; Mathlib `topCatToSheafCompHausLike`
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
noncomputable abbrev continuousSetProfiniteFunctor :
    TopCat.{u + 1} ⥤ Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)) :=
  topCatToSheafCompHausLike.{u + 1, u} (fun T ↦ TotallyDisconnectedSpace T)
    (fun _ _ f hf ↦ ((Profinite.effectiveEpi_tfae f).out 0 2).mp hf)

/-- The profinite coefficient sheaf `S ↦ C(S,D)`, using Mathlib's construction.
Source: Hemo--Richarz--Scholbach, Example 3.1
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
noncomputable abbrev continuousSetProfiniteSheaf (D : Type (u + 1)) [TopologicalSpace D] :=
  continuousSetProfiniteFunctor.obj (TopCat.of D)

/-- The canonical label map from the spectrum of locally constant integer functions to S.
Source: Hemo--Richarz--Scholbach, Example 3.1, test-object construction; the spectrum
homeomorphism in `lem-weil-pbc-locally-constant-prime-spectrum`
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
noncomputable def continuousSetTestProjection (S : Profinite.{u}) :
    C((profiniteToProEt.obj S).left, S) :=
  ContinuousMap.fst.comp
    ⟨(LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm,
      (LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm.continuous⟩

/-- The projection of a relative test object to its profinite label space.
Source: Hemo--Richarz--Scholbach, Example 3.1, relative test objects
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
noncomputable def continuousSetRelativeTestProjection (X : Scheme.{u}) (S : Profinite.{u}) :
    C(((Scheme.proEtaleBaseChange (toSpecZ X)).obj (profiniteToProEt.obj S)).left, S) :=
  (continuousSetTestProjection S).comp
    (pullback.fst (profiniteToProEt.obj S).hom (toSpecZ X)).base.hom

/-- The composite adjunction defining the specified set inverse image from the point.
Source: Hemo--Richarz--Scholbach, Example 3.1; the point-pullback theorem
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
noncomputable abbrev continuousSetPointAdjunction (X : Scheme.{u}) :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous profiniteToProEt
    (Type (u + 1)) (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)).comp
    (Scheme.proEtaleSheafAdjunction (toSpecZ X) (Type (u + 1)))

/-- Test-function normalization of the realization map: the adjoint sends b to b ∘ r.
Source: Hemo--Richarz--Scholbach, Example 3.1, explicit adjunction calculation
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
def IsContinuousSetRealization (X : Scheme.{u}) (D : Type (u + 1)) [TopologicalSpace D]
    (σ : (profinitePointSetSchemeInverseImage X).obj (continuousSetProfiniteSheaf D) ⟶
      continuousSetSheaf X D) : Prop :=
  ∀ (S : Profinite.{u}) (b : C(S, D)),
    (((continuousSetPointAdjunction X).homEquiv _ _ σ).hom.app (op S)) b =
      b.comp (continuousSetRelativeTestProjection X S)

/-- Naturality of the sectionwise direct-image comparison.
Source: Hemo--Richarz--Scholbach, Example 3.1, scheme pullback
(blueprint: lem-sfb-totally-disconnected-coefficient-realization).
Proof: for a morphism of test schemes the two maps to its pullback followed by the
first projection agree by the defining equation of the pullback map. Precomposing a
continuous function with these equal scheme maps gives the claimed equality (step 8). -/
theorem continuousSetDirectImage_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : Type (u + 1)) [TopologicalSpace D] {U V : Y.ProEtᵒᵖ} (g : U ⟶ V) :
    (continuousSetPresheaf Y D).map g ≫
        (↾fun s ↦ s.comp (pullback.fst V.unop.hom f).base.hom) =
      (↾fun s ↦ s.comp (pullback.fst U.unop.hom f).base.hom) ≫
        ((Scheme.proEtaleSheafDirectImage f (Type (u + 1))).obj
          (continuousSetSheaf X D)).obj.map g := by
  ext s x
  change C(U.unop.left, D) at s
  change s (g.unop.left (pullback.fst V.unop.hom f x)) =
    s (pullback.fst U.unop.hom f
      (((Scheme.proEtaleBaseChange f).map g.unop).left x))
  have hmap : ((Scheme.proEtaleBaseChange f).map g.unop).left ≫
      pullback.fst U.unop.hom f = pullback.fst V.unop.hom f ≫ g.unop.left := by
    simp [Scheme.proEtaleBaseChange, MorphismProperty.Over.pullback]
  exact congrArg s (congrArg (fun k : _ ⟶ U.unop.left ↦ k x) hmap.symm)

/-- Precomposition on the base-changed test object, as an actual sheaf morphism.
Source: Hemo--Richarz--Scholbach, Example 3.1, scheme pullback
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
noncomputable def continuousSetDirectImageMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : Type (u + 1)) [TopologicalSpace D] :
    continuousSetSheaf Y D ⟶
      (Scheme.proEtaleSheafDirectImage f (Type (u + 1))).obj (continuousSetSheaf X D) :=
  ⟨{ app := fun V ↦ ↾fun s ↦ s.comp (pullback.fst V.unop.hom f).base.hom
     naturality := fun _ _ g ↦ continuousSetDirectImage_naturality f D g }⟩

/-- The canonical scheme-pullback comparison is the adjunct of precomposition.
Source: Hemo--Richarz--Scholbach, Example 3.1 and the following paragraph
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
noncomputable def continuousSetPullbackMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : Type (u + 1)) [TopologicalSpace D] :
    (Scheme.proEtaleSheafInverseImage f (Type (u + 1))).obj (continuousSetSheaf Y D) ⟶
      continuousSetSheaf X D :=
  ((Scheme.proEtaleSheafAdjunction f (Type (u + 1))).homEquiv _ _).symm
    (continuousSetDirectImageMap f D)

/-- The map from the constant presheaf sends an element to the constant function.
Source: Bhatt--Scholze, Lemma 4.2.12
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
def continuousSetConstantPresheafMap (X : Scheme.{u}) (D : Type (u + 1))
    [TopologicalSpace D] :
    (Functor.const X.ProEtᵒᵖ).obj D ⟶ continuousSetPresheaf X D where
  app U := ↾fun d ↦ ContinuousMap.const U.unop.left d
  naturality _ _ _ := rfl

/-- The canonical constant-sheaf comparison is the sheafification adjunct of constants.
Source: Bhatt--Scholze, Lemma 4.2.12
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
noncomputable def continuousSetConstantMap (X : Scheme.{u}) (D : Type (u + 1))
    [TopologicalSpace D] :
    (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).obj D ⟶
      continuousSetSheaf X D :=
  ((sheafificationAdjunction (Scheme.ProEt.topology X) (Type (u + 1))).homEquiv _ _).symm
    (continuousSetConstantPresheafMap X D)


end AlgebraicGeometry.ProEtale
