import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Exact equivalences on bounded-below derived categories

Source: Stacks Project, Tag 015F, `lemma-right-derived-exact-functor`, applied to
quasi-inverse exact functors (blueprint: lem-kun-exact-equivalence-derived-plus).
-/

namespace CategoryTheory

open CategoryTheory Limits

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

universe u v u' v'

/-- An exact additive equivalence of abelian categories restricts to the bounded-below
-derived categories.  The displayed unit and counit are the termwise induced ones, and
both restricted functors preserve and reflect isomorphisms.

Source: Stacks Project, Tag 015F, `lemma-right-derived-exact-functor`, applied to quasi-inverse
exact functors; the bounded-below restriction and the explicit unit/counit formulas are the
formal consequence recorded in the blueprint (blueprint: lem-kun-exact-equivalence-derived-plus).

Proof (the node's steps):
1. By `lem-sp-exact-functor-preserves-homology` the additive exact functors `F`, `G` satisfy the
   hypotheses of `lem-weil-pbc-exact-functor-derived-factorization`: `C(F)`, `C(G)` preserve
   quasi-isomorphisms and descend to `F_D`, `G_D` on `D(A)`, `D(B)`, with natural isomorphisms
   `φ^F : F_D ∘ Q_A ≅ Q_B ∘ C(F)` and `φ^G : G_D ∘ Q_B ≅ Q_A ∘ C(G)`; no resolutions are used.
2. By `lem-weil-pbc-exact-functor-bounded-below` both carry `D^{≥ a}` into `D^{≥ a}` for every
   `a`; by `def-weil-pbc-bounded-derived-subcategories` each bounded below object lies in one
   such subcategory, so `F_D`, `G_D` restrict to `F⁺`, `G⁺` on the full subcategories `D⁺`.
3. Degreewise, `(η^C_K)^r = η_{K^r}` and `(ε^C_L)^r = ε_{L^r}` are morphisms of complexes by
   naturality at the differentials (`def-weil-abstract-derived-category`), and are natural
   isomorphisms `id ≅ C(G) C(F)` and `C(F) C(G) ≅ id`.
4. With `a_K = φ^G_{C(F)K} ∘ G_D(φ^F_K)` and `b_L = φ^F_{C(G)L} ∘ F_D(φ^G_L)`, clause (2) of
   `lem-weil-pbc-localization-universal-property` descends `a⁻¹ ∘ Q_A(η^C)` and
   `Q_B(ε^C) ∘ b` to natural isomorphisms `η_D : id ≅ G_D F_D`, `ε_D : F_D G_D ≅ id`, with
   `η_{D, Q_A K} = a_K⁻¹ Q_A(η^C_K)` and `ε_{D, Q_B L} = Q_B(ε^C_L) b_L`; these are the
   termwise induced unit and counit (`mapDerivedCategoryPlusNatIso` with the identity and
   composition isomorphisms in the Lean).
5. Since `D⁺` is full (`def-weil-pbc-bounded-derived-subcategories`), `η_D`, `ε_D` restrict to
   `η⁺ : id ≅ G⁺ F⁺` and `ε⁺ : F⁺ G⁺ ≅ id`, so `F⁺`, `G⁺` are quasi-inverse equivalences; if
   `η`, `ε` satisfy the triangle identities, these descend by clause (3) of
   `lem-weil-pbc-localization-universal-property`.
6. Every functor preserves isomorphisms. If `F⁺(u)` has inverse `t`, then
   `(η⁺_X)⁻¹ ∘ G⁺(t) ∘ η⁺_Y` is inverse to `u` by naturality of `η⁺`; symmetrically
   `ε⁺_X ∘ F⁺(t) ∘ (ε⁺_Y)⁻¹` inverts `u` when `G⁺(u)` has inverse `t`.
-/
theorem exactEquivalenceDerivedPlus
    {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (η : 𝟭 A ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 B) :
    let Fplus := F.mapDerivedCategoryPlus
    let Gplus := G.mapDerivedCategoryPlus
    let ηplus :=
      (Functor.mapDerivedCategoryPlusIdIso A).symm ≪≫
        Functor.mapDerivedCategoryPlusNatIso η ≪≫
          Functor.mapDerivedCategoryPlusCompIso F G
    let εplus :=
      (Functor.mapDerivedCategoryPlusCompIso G F).symm ≪≫
        Functor.mapDerivedCategoryPlusNatIso ε ≪≫
          Functor.mapDerivedCategoryPlusIdIso B
    ∃ e : DerivedCategory.Plus A ≌ DerivedCategory.Plus B,
      e = Equivalence.mk Fplus Gplus ηplus εplus ∧
        (∀ {X Y : DerivedCategory.Plus A} (f : X ⟶ Y),
          IsIso (Fplus.map f) ↔ IsIso f) ∧
        (∀ {X Y : DerivedCategory.Plus B} (f : X ⟶ Y),
          IsIso (Gplus.map f) ↔ IsIso f) := by
  sorry

end CategoryTheory
