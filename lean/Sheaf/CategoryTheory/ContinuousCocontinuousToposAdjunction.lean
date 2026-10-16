/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.CategoryTheory.SpecialCocontinuousCoverings
public import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SiteContinuousPushforwardSheaf
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# The topos adjunction of a continuous cocontinuous site functor

Source: Stacks Project, Sites, Section 00XF and Tags 00XH, 00XK, 00XL, 00XO, 00XR
(blueprint: lem-weil-pbc-continuous-cocontinuous-topos-adjunction).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Source: Stacks Project, Sites, Section 00XF and Tags 00XH, 00XK, 00XL, 00XO, 00XR
(blueprint: lem-weil-pbc-continuous-cocontinuous-topos-adjunction).

`L` is identified naturally with precomposition. The existing cocontinuous pushforward
is identified sectionwise with exactly the subtype of compatible families in the node.
The two naturality equations give its restriction maps and its action on sheaf maps.
The last two equations specify the counit and unit under these identifications.
An adjunction with `PreservesFiniteLimits L` is the node's morphism of topoi; no local
fullness, local faithfulness, or cover-density is imposed.

Proof:
1. Continuity makes precomposition a sheaf, by
   lem-weil-pbc-site-continuous-pushforward-sheaf, and hence defines `L` on objects
   and natural transformations.
2. At `V`, form the subset of the product of `F(A)` indexed by `(A, u(A) ⟶ V)`
   satisfying the displayed compatibility. Restriction substitutes `ψ ≫ h` and
   sheaf maps act componentwise. The indexing set may be empty.
3. To prove separatedness, pull a target cover back along each `ψ` and use
   cocontinuity to refine it by images of a source cover. Equality on that cover
   implies equality in `F(A)` by the sheaf condition.
4. For gluing, choose such lifts and glue the corresponding sections of `F`.
   On overlaps their images in the target have equal composite to `V`, hence
   factor through the target overlap. The matching condition gives equality.
5. Two choices of lifts have a common refinement by source fibre products;
   the same overlap argument and separatedness show that the glued section
   is independent of the choice.
6. Pulling these lifted covers back along `B ⟶ A` proves compatibility of the
   glued coordinates. Identity covers show that the resulting family restricts
   to the prescribed matching families. This proves that `R F` is a sheaf.
7. Transpose `α : L G ⟶ F` by sending `t` to the family `α_A(G(ψ)(t))`.
   The inverse evaluates at `(A, id)`. Naturality and compatibility prove that
   these are inverse, bifunctorial hom-set bijections (00XH).
8. Transpose identities to obtain the displayed unit and counit. Evaluating
   at identity arrows proves one triangle; substitution of indices followed
   by evaluation proves the other.
9. Limits of sheaves of sets are sectionwise, by
   lem-weil-pbc-site-sheaf-sets-limits-sectionwise. Precomposition therefore
   preserves finite limits, including the terminal object.
10. These functors give the morphism of topoi associated to cocontinuity (00XO).
    Its usual sheafified inverse image is canonically `L`: the universal
    property in def-weil-pbc-sheafification makes sheafification of an already
    sheaf presheaf canonically the identity, compatibly with unit and counit. -/
theorem continuousCocontinuous_toposAdjunction
    {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
    (J : Precoverage C) (K : Precoverage D)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [K.HasIsos] [K.IsStableUnderComposition] [K.IsStableUnderBaseChange] [K.HasPullbacks]
    (f : C ⥤ D)
    (hcover : ∀ (X : C) (S : Presieve X), S ∈ J X → S.map f ∈ K (f.obj X))
    (hpullback : ∀ (X Y Z : C) (S : Presieve X), S ∈ J X →
      ∀ (a : Y ⟶ X) (b : Z ⟶ X), S a → PreservesLimit (cospan a b) f)
    [f.IsCocontinuous J.toGrothendieck K.toGrothendieck] :
    ∃ (L : Sheaf K.toGrothendieck (Type u) ⥤ Sheaf J.toGrothendieck (Type u))
      (eL : L ⋙ sheafToPresheaf J.toGrothendieck (Type u) ≅
        sheafToPresheaf K.toGrothendieck (Type u) ⋙
          (Functor.whiskeringLeft _ _ (Type u)).obj f.op)
      (adj : L ⊣ f.sheafPushforwardCocontinuous (Type u)
        J.toGrothendieck K.toGrothendieck),
      PreservesFiniteLimits L ∧
      ∃ e : ∀ (F : Sheaf J.toGrothendieck (Type u)) (V : D),
        ((f.sheafPushforwardCocontinuous (Type u)
          J.toGrothendieck K.toGrothendieck).obj F).obj.obj (op V) ≃
          {s : ∀ (A : C), (f.obj A ⟶ V) → F.obj.obj (op A) //
            ∀ (A B : C) (a : B ⟶ A) (ψ : f.obj A ⟶ V),
              F.obj.map a.op (s A ψ) = s B (f.map a ≫ ψ)},
        (∀ (F : Sheaf J.toGrothendieck (Type u)) (V V' : D) (h : V' ⟶ V)
          (s : ((f.sheafPushforwardCocontinuous (Type u)
            J.toGrothendieck K.toGrothendieck).obj F).obj.obj (op V))
          (A : C) (ψ : f.obj A ⟶ V'),
          (e F V' (((f.sheafPushforwardCocontinuous (Type u)
            J.toGrothendieck K.toGrothendieck).obj F).obj.map h.op s)).val A ψ =
              (e F V s).val A (ψ ≫ h)) ∧
        (∀ (F F' : Sheaf J.toGrothendieck (Type u)) (α : F ⟶ F') (V : D)
          (s : ((f.sheafPushforwardCocontinuous (Type u)
            J.toGrothendieck K.toGrothendieck).obj F).obj.obj (op V))
          (A : C) (ψ : f.obj A ⟶ V),
          (e F' V (((f.sheafPushforwardCocontinuous (Type u)
            J.toGrothendieck K.toGrothendieck).map α).hom.app (op V) s)).val A ψ =
              α.hom.app (op A) ((e F V s).val A ψ)) ∧
        (∀ (F : Sheaf J.toGrothendieck (Type u)) (U : C)
          (s : ((f.sheafPushforwardCocontinuous (Type u)
            J.toGrothendieck K.toGrothendieck).obj F).obj.obj (op (f.obj U))),
          (adj.counit.app F).hom.app (op U)
            (((eL.inv.app _).app (op U)) s) = (e F (f.obj U) s).val U (𝟙 _)) ∧
        (∀ (G : Sheaf K.toGrothendieck (Type u)) (V : D) (t : G.obj.obj (op V))
          (A : C) (ψ : f.obj A ⟶ V),
          (eL.hom.app G).app (op A)
            ((e (L.obj G) V ((adj.unit.app G).hom.app (op V) t)).val A ψ) =
              G.obj.map ψ.op t) := by
  sorry

end CategoryTheory
