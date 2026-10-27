module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks

/-!
# The semilinear translated modification product

Source: Stacks Project, Tag 01WF (H-projective base change), Tag 01NF (projective space),
and Tag 01JY (base change of open immersions); the explicit finite-translate construction
in the proof of semilinear equivariant Chow modification, steps 2, 4 and 5
(blueprint: lem-sfb-semilinear-translated-modification-product).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The finite product over `X` of all translates of `π` has its permutation action and a
common invariant dense isomorphism open. `c` is the product cone: its point is `P`, its base
is `r`, and its component projections are `ρ_g`. `Nonempty (IsLimit c)` states precisely
its universal property. The open `U` is specified by equality with the intersection of
all translated opens. The map `e.hom` is the base-changed structure map; `e.inv` therefore
specifies the inverse that defines `j`. The action `aU` is the restriction of `a`, as
specified by its compatibility with the open inclusion.

Source: Stacks Project, Tag 01WF, Tag 01NF and Tag 01JY; agent-explicit construction in
semilinear equivariant Chow modification, steps 2, 4 and 5
(blueprint: lem-sfb-semilinear-translated-modification-product).

Proof:
1. Write projective space as the pullback of integral projective space along the unique
   map to the terminal scheme (def-nagata-projective-space-base-change). Acting on its
   base coordinate by `Spec (rho g⁻¹)` and fixing its integral coordinate gives an
   automorphism, with inverse obtained from `g⁻¹`. Composing the given closed immersion
   with this automorphism embeds each translated factor into the same projective space.
2. Each `a g` is an automorphism, so its image of `U₀` is open and dense. Their finite
   intersection is dense, including when `X` is empty. Left multiplication permutes
   these opens, so the intersection is invariant; restrict each automorphism to it.
3. Iterate binary fibre products (def-pc-fibre-product) over the nonempty finite group
   to obtain a limiting wide pullback cone. Its maps into `Y` have common composite
   with the translated structure maps, and these projections determine all maps into it.
4. For `h`, the components `ρ_(h⁻¹*g)` have common base map `r` followed by `a h`.
   The universal property gives the unique `A h` with the specified projections and
   gives equivariance of `r`; composing with `f` gives semilinearity.
5. The projection formulas for `A h` followed by `A l` and for `A (h*l)` agree, as do
   those for `A 1` and the identity. Uniqueness gives the group laws and shows that
   `A (h⁻¹)` is the inverse of `A h`, defining the monoid homomorphism into automorphisms.
6. The inverse to `π` over `U₀`, composed with the restriction of `a (g⁻¹)` from `U`
   to `U₀`, gives sections of every translated factor over `U`. Their common base map
   is the inclusion. The product universal property gives `j` and its lift to `P ×_X U`.
7. On `P ×_X U`, every component factors through `π⁻¹(U₀)`. The inverse identities
   for `π` imply that the lift and the base projection are two-sided inverses. These
   identities are checked on the components and the two pullback projections.
8. The projection `P ×_X U → P` is an open immersion by base change of the inclusion
   (lem-weil-pbc-open-immersion-base-change). Compose it with the inverse above to
   obtain the open immersion `j`. Equivariance follows from uniqueness of this inverse
   and equivariance of `r`. No faithfulness or characteristic hypothesis is used.
-/
theorem exists_semilinear_translated_modification_product
    (k : Type u) [Field k] (X Y : Scheme.{u}) (f : X ⟶ Spec (.of k))
    (H : Type v) [Group H] [Finite H] (rho : H →* (k ≃+* k)) (a : H →* Aut X)
    (ha : ∀ h : H, (a h).hom ≫ f =
      f ≫ Spec.map (CommRingCat.ofHom (rho h⁻¹).toRingHom))
    (π : Y ⟶ X) (U₀ : X.Opens) (hU₀ : Dense (U₀ : Set X))
    (hπ : IsIso (π ∣_ U₀)) (n : ℕ)
    (i : Y ⟶ ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (.of k)))
    [IsClosedImmersion i]
    (hi : i ≫ (ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (.of k)) ↘
      Spec (.of k)) = π ≫ f) :
    (∀ g : H,
      ∃ ig : Y ⟶ ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (.of k)),
        IsClosedImmersion ig ∧
        ig ≫ (ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (.of k)) ↘
          Spec (.of k)) = π ≫ (a g).hom ≫ f) ∧
    ∃ c : WidePullbackCone (fun g : H ↦ π ≫ (a g).hom),
      Nonempty (IsLimit c) ∧
      ∃ U : X.Opens,
        (U : Set X) = ⋂ g : H, (a g).hom '' (U₀ : Set X) ∧
        Dense (U : Set X) ∧
        (∀ h : H, (a h).hom '' (U : Set X) = (U : Set X)) ∧
        ∃ (A : H →* Aut c.pt) (aU : H →* Aut U.toScheme),
          (∀ h : H, (aU h).hom ≫ U.ι = U.ι ≫ (a h).hom) ∧
          (∀ h g : H, (A h).hom ≫ c.π g = c.π (h⁻¹ * g)) ∧
          (∀ (h : H) (t : c.pt ⟶ c.pt),
            (∀ g : H, t ≫ c.π g = c.π (h⁻¹ * g)) → t = (A h).hom) ∧
          (∀ h : H, (A h).hom ≫ c.base = c.base ≫ (a h).hom) ∧
          (∀ h : H, (A h).hom ≫ c.base ≫ f =
            (c.base ≫ f) ≫ Spec.map (CommRingCat.ofHom (rho h⁻¹).toRingHom)) ∧
          ∃ (e : pullback c.base U.ι ≅ U.toScheme) (j : U.toScheme ⟶ c.pt),
            e.hom = pullback.snd c.base U.ι ∧
            e.inv ≫ pullback.fst c.base U.ι = j ∧
            IsOpenImmersion j ∧ j ≫ c.base = U.ι ∧
            ∀ h : H, j ≫ (A h).hom = (aU h).hom ≫ j := by
  sorry

end AlgebraicGeometry
