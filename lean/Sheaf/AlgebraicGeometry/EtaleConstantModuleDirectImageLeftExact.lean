/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ND
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-!
# Direct image of modules over the constant ring on the small étale site

Source: Stacks Project, sites-modules, Tags 03CV, 03D9--03DC; sites-cohomology,
Section 071J (blueprint: lem-weil-pbc-module-direct-image-left-exact).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option maxHeartbeats 400000 in
-- The universal-property uniqueness check compares the expanded pushforward functors.
/-- The canonical scalar map and the additive left exact module direct image.
Source: Stacks Project, sites-modules, Tags 03CV, 03D9--03DC; sites-cohomology,
Section 071J (blueprint: lem-weil-pbc-module-direct-image-left-exact).

The scalar map is uniquely characterized by its composite with the sheafification
map from the constant presheaf. `SheafOfModules.pushforward ρ` supplies the object
and morphism data: its sections are those over the base-changed object, with
scalars restricted through `ρ`, and its maps are the original component maps.
The final clause expresses preservation of `0 → F₁ → F₂ → F₃`, without requiring
surjectivity at `F₃`.

Proof plan (the node's five steps):
1. Continuity (`lem-weil-pbc-etale-base-change-continuous`) makes the direct image
of the constant ring a sheaf. The constant-presheaf sheafification maps are natural;
`def-weil-pbc-constant-sheaf` and `def-weil-pbc-sheafification` extend them uniquely
from the constant sheaf to define `ρ`.
2. Restriction of scalars through `ρ` gives the module axioms and semilinear
restriction maps; componentwise linear maps give a functor, whose underlying
abelian sheaf is precisely the abelian direct image
(`def-weil-sheaf-of-modules-category`).
3. Addition and zero of morphisms are componentwise, so direct image is additive.
4. By `lem-weil-pbc-module-sheaves-limits-sectionwise`, finite products (including
the empty product) and kernels are computed sectionwise. Direct image leaves the
corresponding tuples and kernel subsets, their restrictions and scalar actions
unchanged. Thus the canonical comparison maps are module isomorphisms.
5. `def-sp-left-exact-additive` identifies this with left exactness. A sequence
`0 → F₁ → F₂ → F₃` identifies its first map with a kernel of the second. Applying
the functor and its kernel comparison preserves this identification, proving
exactness and injectivity of the first image map. -/
theorem existsUnique_constantModuleDirectImage_leftExact
    {U V : Scheme.{max u v}} (u : U ⟶ V) (R : Type v) [CommRing R] :
    ∃! ρ : ((constantSheaf (V.smallGrothendieckTopology @Etale) RingCat.{max u v + 1}).obj
          (RingCat.of (ULift.{max u v + 1} R))) ⟶
        ((MorphismProperty.Over.pullback @Etale ⊤ u).sheafPushforwardContinuous
          RingCat.{max u v + 1}
          (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)).obj
          ((constantSheaf (U.smallGrothendieckTopology @Etale) RingCat.{max u v + 1}).obj
          (RingCat.of (ULift.{max u v + 1} R))),
      (toSheafify (V.smallGrothendieckTopology @Etale)
          ((Functor.const V.Etaleᵒᵖ).obj (RingCat.of (ULift.{max u v + 1} R))) ≫ ρ.hom =
        (MorphismProperty.Over.pullback @Etale ⊤ u).op.whiskerLeft
          (toSheafify (U.smallGrothendieckTopology @Etale)
            ((Functor.const U.Etaleᵒᵖ).obj (RingCat.of (ULift.{max u v + 1} R))))) ∧
      ((SheafOfModules.pushforward.{max u v + 1} ρ) ⋙
        SheafOfModules.toSheaf
          ((constantSheaf (V.smallGrothendieckTopology @Etale) RingCat.{max u v + 1}).obj
          (RingCat.of (ULift.{max u v + 1} R))) =
        SheafOfModules.toSheaf
          ((constantSheaf (U.smallGrothendieckTopology @Etale) RingCat.{max u v + 1}).obj
          (RingCat.of (ULift.{max u v + 1} R))) ⋙
          (MorphismProperty.Over.pullback @Etale ⊤ u).sheafPushforwardContinuous
            AddCommGrpCat.{max u v + 1}
            (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)) ∧
      (SheafOfModules.pushforward.{max u v + 1} ρ).Additive ∧
      PreservesFiniteProducts (SheafOfModules.pushforward.{max u v + 1} ρ) ∧
      (∀ (X Y : SheafOfModules.{max u v + 1}
          ((constantSheaf (U.smallGrothendieckTopology @Etale) RingCat.{max u v + 1}).obj
          (RingCat.of (ULift.{max u v + 1} R)))) (f : X ⟶ Y),
        PreservesLimit (parallelPair f 0) (SheafOfModules.pushforward.{max u v + 1} ρ)) ∧
      (∀ S : ShortComplex (SheafOfModules.{max u v + 1}
          ((constantSheaf (U.smallGrothendieckTopology @Etale) RingCat.{max u v + 1}).obj
          (RingCat.of (ULift.{max u v + 1} R)))),
        S.Exact → Mono S.f →
          ∃ h : (SheafOfModules.pushforward.{max u v + 1} ρ).map S.f ≫
              (SheafOfModules.pushforward.{max u v + 1} ρ).map S.g = 0,
            (ShortComplex.mk ((SheafOfModules.pushforward.{max u v + 1} ρ).map S.f)
              ((SheafOfModules.pushforward.{max u v + 1} ρ).map S.g) h).Exact ∧
              Mono ((SheafOfModules.pushforward.{max u v + 1} ρ).map S.f)) := by
  let B := MorphismProperty.Over.pullback @Etale ⊤ u
  let JV := V.smallGrothendieckTopology (Q := @Etale) @Etale
  let JU := U.smallGrothendieckTopology (Q := @Etale) @Etale
  let A := RingCat.of (ULift.{max u v + 1} R)
  let RU := (constantSheaf JU RingCat.{max u v + 1}).obj A
  let T := (B.sheafPushforwardContinuous RingCat.{max u v + 1} JV JU).obj RU
  let η : (Functor.const V.Etaleᵒᵖ).obj A ⟶ T.obj :=
    B.op.whiskerLeft (toSheafify JU ((Functor.const U.Etaleᵒᵖ).obj A))
  let ρ : (constantSheaf JV RingCat.{max u v + 1}).obj A ⟶ T :=
    ⟨sheafifyLift JV η T.property⟩
  let F := SheafOfModules.pushforward.{max u v + 1} ρ
  let RV := (constantSheaf JV RingCat.{max u v + 1}).obj A
  let G := SheafOfModules.toSheaf.{max u v + 1} RV
  have : PreservesFiniteLimits (F ⋙ G) :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.toSheaf.{max u v + 1} RU ⋙
        B.sheafPushforwardContinuous AddCommGrpCat.{max u v + 1} JV JU))
  have : PreservesFiniteLimits F := preservesFiniteLimits_of_reflects_of_preserves F G
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  refine ⟨ρ, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact toSheafify_sheafifyLift JV η T.property
    · rfl
    · exact inferInstanceAs F.Additive
    · infer_instance
    · intros
      infer_instance
    · intro S hS hmono
      have : Mono S.f := hmono
      refine ⟨(S.map F).zero, ?_, ?_⟩
      · exact hS.map_of_mono_of_preservesKernel F hmono inferInstance
      · infer_instance
  · intro σ hσ
    apply ObjectProperty.hom_ext
    dsimp only [ρ]
    apply sheafifyLift_unique
    exact hσ.1

end AlgebraicGeometry.Etale
