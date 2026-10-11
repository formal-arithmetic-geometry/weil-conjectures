import Sheaf.AlgebraicGeometry.DerivedTensorStructure
import Sheaf.AlgebraicGeometry.DerivedInternalHomAdjunction

/-! # Closed symmetric monoidal dualizability criterion

Source: Stacks Project, Cohomology, Tag 0FPC
(blueprint: lem-pc-dualizable-evaluation-criterion).
-/

universe u w

open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- The evaluation isomorphism criterion for a dualizable object in `D(O_X)`.
The bijection `adj` is a tensor--internal-Hom bijection of
`lem-sc-derived-internal-hom-adjunction`, with the naturality equation of
`scheme_derivedInternalHom_adjunction` as hypothesis `hadj`.
Source: Stacks Project, Cohomology, Tag 0FPC
(blueprint: lem-pc-dualizable-evaluation-criterion).

Proof:
1. Naturality of the adjunction in its first variable: for `f : A → B` and
   `g : B ⊗ K → M` with adjunct `g♭ : B → RHom(K,M)`, the adjunct of `(f ⊗ 1_K) ≫ g`
   is `f ≫ g♭`. Take `A = O_X`, `B = K ⊗ D`, `f = η`, `g = 1_K ⊗ e`, whose adjunct is
   `φ_K`. The adjunct of `(η ⊗ 1_K) ≫ (1_K ⊗ e)` is `η ≫ φ_K`, the adjunct of `id_K` by
   the definition of `η`; bijectivity gives the first triangle identity.
2. Put `g := (1_D ⊗ η) ≫ (e ⊗ 1_D) : D → D`. The map `φ_{O_X} : D = O_X ⊗ D → RHom(K,O_X)`
   is the adjunct of `e` and an isomorphism. By naturality, `g ≫ φ_{O_X}` is the adjunct of
   `(g ⊗ 1_K) ≫ e`. Bifunctoriality (`e ⊗ e` computed two ways) and Step 1 give
   `(g ⊗ 1_K) ≫ e = e`, so `g ≫ φ_{O_X} = φ_{O_X}` and `g = id_D` since `φ_{O_X}` is an
   isomorphism. Associators and unitors are inserted throughout. -/
theorem dualizable_evaluation_criterion (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (K D : schemeDerivedCategory X)
    (adj : ∀ A B C : schemeDerivedCategory X,
      (A ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op B, C)) ≃ (A ⊗ B ⟶ C))
    (hadj : ∀ (A A' B B' C C' : schemeDerivedCategory X)
      (a : A' ⟶ A) (b : B' ⟶ B) (c : C ⟶ C')
      (f : A ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op B, C)),
      adj A' B' C' (a ≫ f ≫
        (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).map (b.op, c)) =
        (a ⊗ₘ b) ≫ adj A B C f ≫ c)
    (e : D ⊗ K ⟶ 𝟙_ (schemeDerivedCategory X))
    (φ : ∀ M : schemeDerivedCategory X,
      M ⊗ D ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op K, M))
    (hφ : ∀ M : schemeDerivedCategory X, IsIso (φ M))
    (hφ_def : ∀ M : schemeDerivedCategory X,
      φ M = (adj (M ⊗ D) K M).symm
        ((α_ M D K).hom ≫ (𝟙 M ⊗ₘ e) ≫ (ρ_ M).hom))
    (η : 𝟙_ (schemeDerivedCategory X) ⟶ K ⊗ D)
    (hη : η ≫ φ K =
      (adj (𝟙_ (schemeDerivedCategory X)) K K).symm ((λ_ K).hom)) :
    𝟙 K = (λ_ K).inv ≫ (η ⊗ₘ 𝟙 K) ≫ (α_ K D K).hom ≫
        (𝟙 K ⊗ₘ e) ≫ (ρ_ K).hom ∧
      𝟙 D = (ρ_ D).inv ≫ (𝟙 D ⊗ₘ η) ≫ (α_ D K D).inv ≫
        (e ⊗ₘ 𝟙 D) ≫ (λ_ D).hom := by
  sorry

end AlgebraicGeometry
