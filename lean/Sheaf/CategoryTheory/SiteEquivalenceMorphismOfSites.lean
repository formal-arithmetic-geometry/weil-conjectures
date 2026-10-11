import Mathlib.CategoryTheory.Sites.Pullback
import Sheaf.CategoryTheory.SiteContinuousPushforwardSheaf

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-! # Equivalence of sites gives morphisms of sites

Source: Stacks Project, Sites, Definitions 00VH, 00WV, 00X1 and Lemmas 00WW,
00WX (blueprint: lem-weil-pbc-site-equivalence-is-morphism-of-sites).
-/

/-- An equivalence of Stacks sites `p : A ⥤ C` with quasi-inverse `p'` such that a family
is a covering of `A` iff its image is a covering of `C` satisfies: (1) a family is a
covering of `C` iff its image under `p'` is a covering of `A`; (2) `p` and `p'` are
continuous (Sites, Definition 00WV: coverings go to coverings, written by clause (1) and
the hypothesis `hcover`, and the fibre products `T ×_V V_i` along members of coverings are
preserved), so that the pushforwards `p^s`, `p'^s` are defined; (3) `p^s` and `p'^s` are
quasi-inverse on sheaves of sets and on abelian sheaves; (4) `p_s` and `p'_s` on sheaves
of sets are exact, so `p` and `p'` define morphisms of sites (Definition 00X1), and `p_s`
is a quasi-inverse of `p^s`, `p'_s` a quasi-inverse of `p'^s`.

Proof: (1) by the isomorphic-family lemma and naturality of `epsilon`, which makes the
hypotheses symmetric in `(p, p')`; fibre products are preserved since `p` is a right
adjoint of `p'` (`Equivalence.mk` and `toAdjunction`) and right adjoints preserve limits;
continuity follows; `p^s`, `p'^s` are quasi-inverse via Lemma 00WW and `epsilon`, `eta`;
`p_s` is isomorphic to `p'^s` by uniqueness of left adjoints, hence a quasi-inverse of
`p^s`; exactness: `p_s` is a left adjoint, so preserves colimits, and is isomorphic to the
right adjoint `p'^s`, so preserves limits; `p'` by symmetry.

Source: Stacks Project, Sites, Definitions 00VH, 00WV, 00X1 and Lemmas 00WW,
00WX; Categories, Definitions 001J and 0034.
(blueprint: lem-weil-pbc-site-equivalence-is-morphism-of-sites)
-/
theorem site_equivalence_is_morphism_of_sites
    {A C : Type u} [SmallCategory A] [SmallCategory C]
    (JA : Precoverage A) (JC : Precoverage C)
    [JA.HasIsos] [JA.IsStableUnderComposition] [JA.IsStableUnderBaseChange]
    [JA.HasPullbacks]
    [JC.HasIsos] [JC.IsStableUnderComposition] [JC.IsStableUnderBaseChange]
    [JC.HasPullbacks]
    (p : A ⥤ C) [p.IsEquivalence]
    (p' : C ⥤ A)
    (eta : 𝟭 A ≅ p ⋙ p') (epsilon : p' ⋙ p ≅ 𝟭 C)
    (hcover : ∀ (X : A) (R : Presieve X), R ∈ JA X ↔
      R.map p ∈ JC (p.obj X)) :
    (∀ (Y : C) (R : Presieve Y), R ∈ JC Y ↔
      R.map p' ∈ JA (p'.obj Y)) ∧
    (∀ (X Y Z : A) (R : Presieve X), R ∈ JA X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) p) ∧
    (∀ (X Y Z : C) (R : Presieve X), R ∈ JC X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) p') ∧
    ∃ (hp : p.IsContinuous JA.toGrothendieck JC.toGrothendieck),
      ∃ (hp' : p'.IsContinuous JC.toGrothendieck JA.toGrothendieck),
      Nonempty (p.sheafPushforwardContinuous (Type u)
        JA.toGrothendieck JC.toGrothendieck ⋙
        p'.sheafPushforwardContinuous (Type u)
          JC.toGrothendieck JA.toGrothendieck ≅ 𝟭
            (Sheaf JC.toGrothendieck (Type u))) ∧
      Nonempty (p'.sheafPushforwardContinuous (Type u)
        JC.toGrothendieck JA.toGrothendieck ⋙
        p.sheafPushforwardContinuous (Type u)
          JA.toGrothendieck JC.toGrothendieck ≅ 𝟭
            (Sheaf JA.toGrothendieck (Type u))) ∧
      Nonempty (p.sheafPushforwardContinuous (AddCommGrpCat.{u})
        JA.toGrothendieck JC.toGrothendieck ⋙
        p'.sheafPushforwardContinuous (AddCommGrpCat.{u})
          JC.toGrothendieck JA.toGrothendieck ≅ 𝟭
            (Sheaf JC.toGrothendieck (AddCommGrpCat.{u}))) ∧
      Nonempty (p'.sheafPushforwardContinuous (AddCommGrpCat.{u})
        JC.toGrothendieck JA.toGrothendieck ⋙
        p.sheafPushforwardContinuous (AddCommGrpCat.{u})
          JA.toGrothendieck JC.toGrothendieck ≅ 𝟭
            (Sheaf JA.toGrothendieck (AddCommGrpCat.{u}))) ∧
      PreservesFiniteLimits (Functor.sheafPullback p (Type u)
        JA.toGrothendieck JC.toGrothendieck) ∧
      PreservesFiniteColimits (Functor.sheafPullback p (Type u)
        JA.toGrothendieck JC.toGrothendieck) ∧
      PreservesFiniteLimits (Functor.sheafPullback p' (Type u)
        JC.toGrothendieck JA.toGrothendieck) ∧
      PreservesFiniteColimits (Functor.sheafPullback p' (Type u)
        JC.toGrothendieck JA.toGrothendieck) ∧
      Nonempty (Functor.sheafPullback p (Type u)
        JA.toGrothendieck JC.toGrothendieck ⋙
        p.sheafPushforwardContinuous (Type u)
          JA.toGrothendieck JC.toGrothendieck ≅ 𝟭
            (Sheaf JA.toGrothendieck (Type u))) ∧
      Nonempty (p.sheafPushforwardContinuous (Type u)
        JA.toGrothendieck JC.toGrothendieck ⋙
        Functor.sheafPullback p (Type u)
          JA.toGrothendieck JC.toGrothendieck ≅ 𝟭
            (Sheaf JC.toGrothendieck (Type u))) ∧
      Nonempty (Functor.sheafPullback p' (Type u)
        JC.toGrothendieck JA.toGrothendieck ⋙
        p'.sheafPushforwardContinuous (Type u)
          JC.toGrothendieck JA.toGrothendieck ≅ 𝟭
            (Sheaf JC.toGrothendieck (Type u))) ∧
      Nonempty (p'.sheafPushforwardContinuous (Type u)
        JC.toGrothendieck JA.toGrothendieck ⋙
        Functor.sheafPullback p' (Type u)
          JC.toGrothendieck JA.toGrothendieck ≅ 𝟭
            (Sheaf JA.toGrothendieck (Type u))) := by
  sorry

end CategoryTheory
