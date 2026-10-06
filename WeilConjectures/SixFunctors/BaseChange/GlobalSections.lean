/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections

/-!
# Functoriality of the pullback of global sections

For a morphism of schemes `h : V ⟶ Y` and an étale sheaf `G` on `Y`, the pullback of global
sections `h^♯ : Γ(Y, G) ⟶ Γ(V, h^* G)` is `AlgebraicGeometry.Etale.globalSectionsUpperStarMap`,
given by the unit of `h^* ⊣ h_*`. It is functorial:

* along the identity it is the identity isomorphism `(𝟙 Y)^* G ≅ G`;
* along a composite `v ≫ u` it is the composite of the pullbacks, modulo
  `(v ≫ u)^* ≅ v^* u^*`;
* for a commutative square `a ≫ u = b ≫ i` the two composite pullbacks agree modulo the
  square isomorphism `b^* i^* ≅ a^* u^*`. Applied to the base change of a closed immersion
  `i : Z ⟶ T` along a finite `u : T' ⟶ T`, this says that pulling back a section to `T'` and
  restricting to the closed fibre `Z' = Z ×_T T'` is the same as restricting it to `Z` and
  pulling back to `Z'`.

These are the finite-pullback identities used in the degree-zero comparison over a
henselian pair; there the morphisms are finite, but finiteness plays no role here.

## Main statements

- `AlgebraicGeometry.Etale.globalSectionsUpperStarMap_id`
- `AlgebraicGeometry.Etale.globalSectionsUpperStarMap_comp`
- `AlgebraicGeometry.Etale.globalSectionsUpperStarMap_comp_squareUpperStarIso`
- `AlgebraicGeometry.Etale.globalSectionsUpperStarMap_descent`
- `AlgebraicGeometry.Etale.globalSectionsUpperStarMap_identities`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

/-- **Finite pullback along the identity**: pulling back a section along `𝟙 Y` gives back the
section, under the identity isomorphism `(𝟙 Y)^* G ≅ G`.
(blueprint: `lemma-weil-pbc-finite-pullback-identity`) -/
@[reassoc]
lemma globalSectionsUpperStarMap_id {Y : Scheme.{u}} (G : Sheaf Y.smallEtaleTopology A) :
    globalSectionsUpperStarMap A (𝟙 Y) G ≫
      (Sheaf.Γ _ A).map ((upperStarId A Y).hom.app G) = 𝟙 _ :=
  sorry

/-- **Finite pullback along a composite**: for `v : T'' ⟶ T'` and `u : T' ⟶ T`, pulling a
section back along `v ≫ u` is pulling it back along `u` and then along `v`, under the
composition isomorphism `(v ≫ u)^* G ≅ v^* u^* G`.
(blueprint: `lemma-weil-pbc-finite-pullback-composition`) -/
@[reassoc]
lemma globalSectionsUpperStarMap_comp {T'' T' T : Scheme.{u}} (v : T'' ⟶ T') (u : T' ⟶ T)
    (G : Sheaf T.smallEtaleTopology A) :
    globalSectionsUpperStarMap A (v ≫ u) G ≫
        (Sheaf.Γ _ A).map ((upperStarComp A v u).hom.app G) =
      globalSectionsUpperStarMap A u G ≫ globalSectionsUpperStarMap A v ((u)^*[A].obj G) :=
  sorry

/-- **Finite pullback and restriction to the closed fibre**: for a commutative square
```
Z' --a--> T'
|         |
b         u
v         v
Z  --i--> T
```
pulling a section back along `u` and then along `a` agrees with restricting it along `i` and
then pulling back along `b`, under the square isomorphism `b^* i^* G ≅ a^* u^* G`. It follows
from `AlgebraicGeometry.Etale.globalSectionsUpperStarMap_comp` applied to the two equal
composites `a ≫ u = b ≫ i`.
(blueprint: `lemma-weil-pbc-finite-pullback-closed-fibre`) -/
@[reassoc]
lemma globalSectionsUpperStarMap_comp_squareUpperStarIso {Z' T' Z T : Scheme.{u}}
    {a : Z' ⟶ T'} {b : Z' ⟶ Z} {u : T' ⟶ T} {i : Z ⟶ T} (sq : CommSq a b u i)
    (G : Sheaf T.smallEtaleTopology A) :
    globalSectionsUpperStarMap A i G ≫ globalSectionsUpperStarMap A b ((i)^*[A].obj G) ≫
        (Sheaf.Γ _ A).map ((squareUpperStarIso A sq).hom.app G) =
      globalSectionsUpperStarMap A u G ≫ globalSectionsUpperStarMap A a ((u)^*[A].obj G) := by
  rw [← globalSectionsUpperStarMap_comp, ← globalSectionsUpperStarMap_comp_assoc,
    ← Functor.map_comp]
  have h₁ := globalSectionsUpperStarMap_comp A a u G
  sorry

/-- **Finite descent compatibility**: let `u : T' ⟶ T`, and let `x'` be a section of `u^* G`
over `T'` descended from a section `x` of `G` over `T`, that is `u^♯ x = x'`. Then the same
equality holds after restriction to a closed fibre: for a commutative square `a ≫ u = b ≫ i`,
the pullback `a^♯ x'` is the pullback along `b` of the restriction `i^♯ x`, under the square
isomorphism. Sections are taken with values in an arbitrary object `M`.
(blueprint: `lemma-weil-pbc-finite-pullback-descent`) -/
lemma globalSectionsUpperStarMap_descent {Z' T' Z T : Scheme.{u}}
    {a : Z' ⟶ T'} {b : Z' ⟶ Z} {u : T' ⟶ T} {i : Z ⟶ T} (sq : CommSq a b u i)
    (G : Sheaf T.smallEtaleTopology A) {M : A} (x : M ⟶ (Sheaf.Γ _ A).obj G)
    (x' : M ⟶ (Sheaf.Γ _ A).obj ((u)^*[A].obj G)) (hx : x ≫ globalSectionsUpperStarMap A u G = x') :
    x' ≫ globalSectionsUpperStarMap A a ((u)^*[A].obj G) =
      x ≫ globalSectionsUpperStarMap A i G ≫ globalSectionsUpperStarMap A b ((i)^*[A].obj G) ≫
        (Sheaf.Γ _ A).map ((squareUpperStarIso A sq).hom.app G) := by
  rw [globalSectionsUpperStarMap_comp_squareUpperStarIso, ← hx, Category.assoc]

/-- **The finite-pullback identities**: the pullback of sections is the identity along the
identity, is compatible with composition, is compatible with restriction to closed fibres,
and preserves descended sections.
(blueprint: `lem-weil-pbc-finite-pullback-identities`) -/
theorem globalSectionsUpperStarMap_identities {Z' T' Z T : Scheme.{u}}
    {a : Z' ⟶ T'} {b : Z' ⟶ Z} {u : T' ⟶ T} {i : Z ⟶ T} (sq : CommSq a b u i)
    (G : Sheaf T.smallEtaleTopology A) :
    globalSectionsUpperStarMap A (𝟙 T) G ≫ (Sheaf.Γ _ A).map ((upperStarId A T).hom.app G) =
        𝟙 _ ∧
      globalSectionsUpperStarMap A (a ≫ u) G ≫
          (Sheaf.Γ _ A).map ((upperStarComp A a u).hom.app G) =
        globalSectionsUpperStarMap A u G ≫ globalSectionsUpperStarMap A a ((u)^*[A].obj G) ∧
      globalSectionsUpperStarMap A i G ≫ globalSectionsUpperStarMap A b ((i)^*[A].obj G) ≫
          (Sheaf.Γ _ A).map ((squareUpperStarIso A sq).hom.app G) =
        globalSectionsUpperStarMap A u G ≫ globalSectionsUpperStarMap A a ((u)^*[A].obj G) ∧
      ∀ {M : A} (x : M ⟶ (Sheaf.Γ _ A).obj G) (x' : M ⟶ (Sheaf.Γ _ A).obj ((u)^*[A].obj G)),
        x ≫ globalSectionsUpperStarMap A u G = x' →
          x' ≫ globalSectionsUpperStarMap A a ((u)^*[A].obj G) =
            x ≫ globalSectionsUpperStarMap A i G ≫
              globalSectionsUpperStarMap A b ((i)^*[A].obj G) ≫
                (Sheaf.Γ _ A).map ((squareUpperStarIso A sq).hom.app G) :=
  ⟨globalSectionsUpperStarMap_id A G, globalSectionsUpperStarMap_comp A a u G,
    globalSectionsUpperStarMap_comp_squareUpperStarIso A sq G,
    fun x x' hx ↦ globalSectionsUpperStarMap_descent A sq G x x' hx⟩

end AlgebraicGeometry.Etale
