import Sheaf.AlgebraicGeometry.AssociatedModule

/-!
# Morphisms out of the sheaf associated to a module

Source: Stacks Project, Modules, Lemma 01BH assertion (4)
(blueprint: lem-weil-pbc-associated-module-hom).
-/

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped ChangeOfRings

namespace AlgebraicGeometry

variable (X : SheafedSpace CommRingCat.{u})

/--
For a ringed space `X` with `R = Γ(X, O_X)`, an `R`-module `M` and a sheaf of
`O_X`-modules `G`, the map `Hom_{O_X}(F_M, G) → Hom_R(M, Γ(X, G))`,
`φ ↦ φ_X ∘ c_M`, is bijective (Stacks, Modules, Lemma 01BH, assertion (4), with
α = id) (blueprint: lem-weil-pbc-associated-module-hom).

Proof: by the universal property of sheafification, `φ ↦ φ ∘ σ_M` identifies
`O_X`-linear maps `F_M → G` with presheaf-module maps `ψ : P_M → G`. Such a `ψ`
is determined by `E(ψ)(m) = ψ_X(1 ⊗ m)`, since `ψ_U(a ⊗ m) = a · E(ψ)(m)|_U`;
conversely an `R`-linear `v : M → Γ(X, G)` gives the `R`-balanced maps
`(a, m) ↦ a · v(m)|_U`, hence `O_X(U)`-linear `ψ^v_U` compatible with
restrictions (semilinearity of the restrictions of `G`), with `E(ψ^v) = v`. The
composite `E(φ ∘ σ_M) = φ_X ∘ c_M` is the stated map, since
`c_M(m) = σ_{M,X}(1 ⊗ m)`.
-/
theorem associatedModuleHom_bijective
    (M : ModuleCat (X.presheaf.obj (op (⊤ : Opens (X : Type u)))))
    (G : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology (X : Type u))
        (forget₂ CommRingCat RingCat)).obj X.sheaf)) :
    Function.Bijective
      (fun (φ : associatedModule X M ⟶ G) =>
        associatedModuleCanonicalSection X M ≫
          φ.val.app (op (⊤ : Opens (X : Type u)))) := by
  sorry

/-- Naturality of the associated-module Hom bijection `φ ↦ φ_X ∘ c_M`: it carries
`β ∘ φ` to `β_X ∘ (φ_X ∘ c_M)` for `O_X`-linear `β : G → G'`, and `φ ∘ F_u` to
`(φ_X ∘ c_M) ∘ u` for `R`-linear `u : M' → M` (Stacks, Modules, Lemma 01BH
assertion (4)) (blueprint: lem-weil-pbc-associated-module-hom).

Proof: the components of a composite are the composites of the components, and
`F_{u,X} ∘ c_{M'} = c_M ∘ u` by the definition of `F_u`.
-/
theorem associatedModuleHom_natural
    (M M' : ModuleCat (X.presheaf.obj (op (⊤ : Opens (X : Type u)))))
    (G G' : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology (X : Type u))
        (forget₂ CommRingCat RingCat)).obj X.sheaf))
    (β : G ⟶ G') (u : M' ⟶ M) :
    (∀ (φ : associatedModule X M ⟶ G),
      associatedModuleCanonicalSection X M ≫ φ.val.app (op (⊤ : Opens (X : Type u))) ≫
        β.val.app (op (⊤ : Opens (X : Type u))) =
      associatedModuleCanonicalSection X M ≫ (φ ≫ β).val.app
        (op (⊤ : Opens (X : Type u)))) ∧
    (∀ (φ : associatedModule X M ⟶ G),
      associatedModuleCanonicalSection X M' ≫
        (((associatedModuleFunctor X).map u) ≫ φ).val.app
          (op (⊤ : Opens (X : Type u))) =
      u ≫ associatedModuleCanonicalSection X M ≫
        φ.val.app (op (⊤ : Opens (X : Type u)))) := by
  sorry

end AlgebraicGeometry
