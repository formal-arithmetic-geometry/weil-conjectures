/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.Sites.LocalizedSheavesOverRepresentable
import WeilConjectures.CategoryTheory.Sites.SliceSheafInverseImageEquivalence
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over

/-!
# Localization of a continuous site morphism

Source: literature/stacks-project/sites.tex, Tag 03CF, lemma-localize-morphism
(blueprint: lem-weil-pbc-slice-site-localization).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false

/-- Localization of a continuous morphism of sites induces a morphism on slices.

Source: Stacks Project, `sites.tex`, Tag 03CF, lemma `localize-morphism`.
The precoverage instances are the site axioms of 00VH. `hcover` and `hpullback`
are Stacks continuity (00WV); the `IsContinuous` instance expresses its consequence
for sheaves. `Over.post u` is the existing slice functor. The two first conjuncts
state Stacks continuity on the slices using `Presieve.overEquiv` to read coverings.
The existential witnesses then make the localized sheaf functors typeable.

Proof (the five steps of the node):
1. Coverings and pullbacks over V are the underlying coverings and pullbacks;
   apply hcover and hpullback. The continuous-functor sheaf adjunction supplies
   the slice left adjoint (lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction).
   Precomposition evaluated at T → V is G(u(T)) on both sides of the direct-image
   comparison, including all restriction maps.
2. Sheafification and Yoneda identify maps from L(h_V#) to G with G(u(V)),
   naturally in G. Covariant Yoneda gives c : L(h_V#) ≅ h_U#. The adjoint of c
   sends a representable section a to the sheafified section u(a)
   (def-weil-pbc-sheafification, lem-galois-yoneda-hom-bijection,
   lem-weil-pbc-coyoneda-iso-of-natural-hom-bijection).
3. Under lem-weil-pbc-localized-sheaves-over-representable, send (H,p) to
   (LH,c ∘ Lp). Its right adjoint is (RG ×_{R(h_U#)} h_V# → h_V#).
   The sectionwise fibre formula identifies this right adjoint with slice
   precomposition. Uniqueness of left adjoints identifies the slice inverse
   image with this functor on over categories; limits are sectionwise by
   lem-weil-pbc-site-sheaf-sets-limits-sectionwise.
4. The functor on over categories preserves terminal objects and pullbacks
   because L does. These generate finite limits, including the empty limit.
   Transport across the slice equivalences. The adjunction also implies finite
   colimit preservation, so this is a morphism of sites.
5. Restriction corresponds to (H × h_V# → h_V#). Apply L and its product
   preservation, then c, to obtain (LH × h_U# → h_U#). The fibre formula
   identifies this naturally with restriction of LH, proving the inverse-image
   comparison. Together with step 1 this gives both comparisons
   (def-pur-localized-ringed-site).
(blueprint: lem-weil-pbc-slice-site-localization)
-/
theorem slice_site_localization
    {D : Type u} {C : Type v} [SmallCategory D] [SmallCategory C]
    (K : Precoverage D) (J : Precoverage C)
    [K.HasIsos] [K.IsStableUnderComposition] [K.IsStableUnderBaseChange] [K.HasPullbacks]
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (u : D ⥤ C)
    (hcover : ∀ (X : D) (R : Presieve X), R ∈ K X → R.map u ∈ J (u.obj X))
    (hpullback : ∀ (X Y Z : D) (R : Presieve X), R ∈ K X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) u)
    [u.IsContinuous K.toGrothendieck J.toGrothendieck]
    [(u.sheafPushforwardContinuous (Type (max u v))
      K.toGrothendieck J.toGrothendieck).IsRightAdjoint]
    [PreservesFiniteLimits (u.sheafPullback (Type (max u v)) K.toGrothendieck J.toGrothendieck)]
    (V : D) :
    (∀ (X : Over V) (R : Presieve X), Presieve.overEquiv X R ∈ K X.left →
      Presieve.overEquiv ((Over.post (X := V) u).obj X)
        (R.map (Over.post (X := V) u)) ∈ J (u.obj X.left)) ∧
    (∀ (X Y Z : Over V) (R : Presieve X), Presieve.overEquiv X R ∈ K X.left →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (Over.post (X := V) u)) ∧
    ∃ hcont : (Over.post (X := V) u).IsContinuous
        (K.toGrothendieck.over V) (J.toGrothendieck.over (u.obj V)),
      ∃ hadj : ((Over.post (X := V) u).sheafPushforwardContinuous (Type (max u v))
        (K.toGrothendieck.over V) (J.toGrothendieck.over (u.obj V))).IsRightAdjoint,
      ∃ hlim : PreservesFiniteLimits
        ((Over.post (X := V) u).sheafPullback (Type (max u v))
          (K.toGrothendieck.over V) (J.toGrothendieck.over (u.obj V))),
        Nonempty ((K.toGrothendieck.overPullback (Type (max u v)) V) ⋙
          (Over.post (X := V) u).sheafPullback (Type (max u v)) (K.toGrothendieck.over V)
            (J.toGrothendieck.over (u.obj V)) ≅
          u.sheafPullback (Type (max u v)) K.toGrothendieck J.toGrothendieck ⋙
            J.toGrothendieck.overPullback (Type (max u v)) (u.obj V)) ∧
        Nonempty (u.sheafPushforwardContinuous (Type (max u v)) K.toGrothendieck J.toGrothendieck ⋙
          K.toGrothendieck.overPullback (Type (max u v)) V ≅
          J.toGrothendieck.overPullback (Type (max u v)) (u.obj V) ⋙
            (Over.post (X := V) u).sheafPushforwardContinuous (Type (max u v))
              (K.toGrothendieck.over V) (J.toGrothendieck.over (u.obj V)))  := by
  have hcov : ∀ (X : Over V) (R : Presieve X),
      Presieve.overEquiv X R ∈ K X.left →
      Presieve.overEquiv ((Over.post (X := V) u).obj X)
        (R.map (Over.post (X := V) u)) ∈ J (u.obj X.left) := by
    intro X R hR
    have heq : Presieve.overEquiv ((Over.post (X := V) u).obj X)
        (R.map (Over.post u)) = (Presieve.overEquiv X R).map u := by
      change (R.map (Over.post u)).map (Over.forget _) = _
      obtain ⟨I, A, f, rfl⟩ := R.exists_eq_ofArrows
      simp only [Presieve.overEquiv, RelIso.coe_fn_mk, Equiv.coe_fn_mk,
        Presieve.map_ofArrows]
      rfl
    rw [heq]
    exact hcover X.left _ hR
  have hpb : ∀ (X Y Z : Over V) (R : Presieve X),
      Presieve.overEquiv X R ∈ K X.left →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (Over.post (X := V) u) := by
    intro X Y Z R hR f g hf
    have : PreservesLimit (cospan f.left g.left) u :=
      hpullback X.left Y.left Z.left _ hR f.left g.left
        (Presieve.map.of hf)
    have : PreservesLimit (cospan f g ⋙ Over.forget V) u := by
      have : PreservesLimit (cospan
          ((cospan f g ⋙ Over.forget V).map WalkingCospan.Hom.inl)
          ((cospan f g ⋙ Over.forget V).map WalkingCospan.Hom.inr)) u := by
        simpa only [Functor.comp_map, cospan_map_inl, cospan_map_inr, Over.forget_map] using
          (inferInstance : PreservesLimit (cospan f.left g.left) u)
      exact preservesLimit_of_iso_diagram u (diagramIsoCospan _).symm
    have : PreservesLimit (cospan f g) (Over.post u ⋙ Over.forget (u.obj V)) :=
      inferInstanceAs (PreservesLimit (cospan f g) (Over.forget V ⋙ u))
    exact preservesLimit_of_reflects_of_preserves _ (Over.forget _)
  refine ⟨hcov, hpb, ?_⟩
  have : (K.comap (Over.forget V)).PullbacksPreservedBy (Over.post u) :=
    ⟨fun {X R} hR ↦ ⟨fun {Y Z f g} hf _ ↦ hpb X Y Z R hR f g hf⟩⟩
  have hcont : (Over.post (X := V) u).IsContinuous
      (K.toGrothendieck.over V) (J.toGrothendieck.over (u.obj V)) := by
    rw [over_toGrothendieck_eq_toGrothendieck_comap_forget,
      over_toGrothendieck_eq_toGrothendieck_comap_forget]
    exact (Over.post u).isContinuous_toGrothendieck_of_pullbacksPreservedBy
      (K.comap (Over.forget V)) (J.comap (Over.forget (u.obj V)))
      (fun _ _ hR ↦ hcov _ _ hR)
  have := hcont
  refine ⟨hcont, inferInstance, ?_⟩
  obtain ⟨hlim, e, eR⟩ :=
    sliceSheafInverseImage_remainder K.toGrothendieck J.toGrothendieck u V
  exact ⟨hlim, e, eR⟩

end CategoryTheory
