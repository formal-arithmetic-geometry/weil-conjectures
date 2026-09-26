/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# The base change map `g^* f_* ⟶ f'_* g'^*`

For a commutative square of schemes

```
  X' --g'--> X
  |          |
  f'         f
  ↓          ↓
  Y' --g---> Y
```

(`sq : CommSq g' f' f g`, so `sq.w : g' ≫ f = f' ≫ g`) the two composites of pullbacks
`f'^* ∘ g^*` and `g'^* ∘ f^*` are both identified with `(g' ≫ f)^* = (f' ≫ g)^*` by the
composition isomorphisms `AlgebraicGeometry.Etale.upperStarComp`, giving the *square
isomorphism* `AlgebraicGeometry.Etale.squareUpperStarIso sq : g^* ⋙ f'^* ≅ f^* ⋙ g'^*`
(functor composition is diagrammatic: `g^* ⋙ f'^*` is "`f'^* ∘ g^*`").

The **base change map** `AlgebraicGeometry.Etale.baseChangeMap sq : f_* ⋙ g^* ⟶ g'^* ⋙ f'_*`,
that is `g^* f_* ⟶ f'_* g'^*`, is the mate (`CategoryTheory.mateEquiv`) of the
square isomorphism with respect to the adjunctions `f^* ⊣ f_*` and `f'^* ⊣ f'_*`: its
adjoint `f'^* g^* f_* F ⟶ g'^* F` is the square isomorphism followed by `g'^*` of the counit
of `f^* ⊣ f_*` (`AlgebraicGeometry.Etale.upperStar_map_baseChangeMap_app_counit`), and
its composite with the unit of `f'^* ⊣ f'_*` is `g^*` of the unit of `f^* ⊣ f_*` followed by
`f'_*` of the square isomorphism (`AlgebraicGeometry.Etale.map_unit_baseChangeMap_app`).

The map is natural in the sheaf by construction
(`AlgebraicGeometry.Etale.baseChangeMap_naturality`). Taking the mate once more, along the
adjunctions `g'^* ⊣ g'_*` and `g^* ⊣ g_*`, recovers the square isomorphism
`AlgebraicGeometry.Etale.squareLowerStarIso sq : g'_* ⋙ f_* ≅ f'_* ⋙ g_*` of the pushforwards
(`AlgebraicGeometry.Etale.mateEquiv_baseChangeSquare`), so the base change map is
equivalently the mate of the square isomorphism of the pushforwards along the horizontal
adjunctions (`AlgebraicGeometry.Etale.baseChangeSquare_eq_mateEquiv_symm`). In this form
it is visibly an isomorphism when `g` and `g'` are universal homeomorphisms, in particular
for the identity square
(`AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isUniversalHomeomorphism`).

The pasting laws for the base change maps of horizontally or vertically composed squares
follow from `CategoryTheory.mateEquiv_vcomp` and `CategoryTheory.mateEquiv_hcomp` together
with the coherence of `AlgebraicGeometry.Etale.upperStarComp`; they are left to a later
file.
(blueprint: `def:weil-pbc-cartesian-square`, `def:weil-pbc-underived-exchange`,
`lemma:weil-pbc-underived-exchange-naturality`)

-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

open Etale

section Square

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The square isomorphism `g^* ⋙ f'^* ≅ f^* ⋙ g'^*` attached to a commutative square
`g' ≫ f = f' ≫ g`: both sides are identified with the pullback along the diagonal
`g' ≫ f = f' ≫ g` by `AlgebraicGeometry.Etale.upperStarComp`. -/
noncomputable def Etale.squareUpperStarIso (sq : CommSq g' f' f g) :
    (g)^*[A] ⋙ (f')^*[A] ≅ (f)^*[A] ⋙ (g')^*[A] :=
  (Etale.upperStarComp A f' g (g' ≫ f) sq.w).symm ≪≫ Etale.upperStarComp A g' f

/-- **The base change map** `g^* f_* ⟶ f'_* g'^*` of a commutative square, as a natural
transformation `f_* ⋙ g^* ⟶ g'^* ⋙ f'_*`: the mate of the square isomorphism
`AlgebraicGeometry.Etale.squareUpperStarIso` with respect to the adjunctions `f^* ⊣ f_*` and
`f'^* ⊣ f'_*`. (blueprint: `def:weil-pbc-underived-exchange`) -/
noncomputable def Etale.baseChangeMap (sq : CommSq g' f' f g) :
    (f)_*[A] ⋙ (g)^*[A] ⟶ (g')^*[A] ⋙ (f')_*[A] :=
  (mateEquiv (Etale.upperStarLowerStarAdjunction A f)
    (Etale.upperStarLowerStarAdjunction A f')
    (TwoSquare.mk _ _ _ _ (Etale.squareUpperStarIso A sq).hom)).natTrans

/-- The base change map as a `TwoSquare`, for the mate calculus. -/
noncomputable abbrev Etale.baseChangeSquare (sq : CommSq g' f' f g) :
    TwoSquare (f)_*[A] (g')^*[A] (g)^*[A] (f')_*[A] :=
  mateEquiv (Etale.upperStarLowerStarAdjunction A f)
    (Etale.upperStarLowerStarAdjunction A f')
    (TwoSquare.mk _ _ _ _ (Etale.squareUpperStarIso A sq).hom)

/-- **The adjoint of the base change map** is the square isomorphism followed by the counit:
for a sheaf `F` on `X`,
`f'^* (baseChangeMap F) ≫ ε_{f'} = squareUpperStarIso (f_* F) ≫ g'^* (ε_f F)`.
(blueprint: `def:weil-pbc-underived-exchange`) -/
lemma Etale.upperStar_map_baseChangeMap_app_counit (sq : CommSq g' f' f g)
    (F : Sheaf X.smallEtaleTopology A) :
    ((f')^*[A]).map ((Etale.baseChangeMap A sq).app F) ≫
        (Etale.upperStarLowerStarAdjunction A f').counit.app (((g')^*[A]).obj F) =
      (Etale.squareUpperStarIso A sq).hom.app (((f)_*[A]).obj F) ≫
        ((g')^*[A]).map ((Etale.upperStarLowerStarAdjunction A f).counit.app F) :=
  mateEquiv_counit _ _ _ F

/-- **The unit form of the base change map**: for a sheaf `G` on `Y`,
`g^* (η_f G) ≫ baseChangeMap (f^* G) = η_{f'} (g^* G) ≫ f'_* (squareUpperStarIso G)`. -/
lemma Etale.map_unit_baseChangeMap_app (sq : CommSq g' f' f g)
    (G : Sheaf Y.smallEtaleTopology A) :
    ((g)^*[A]).map ((Etale.upperStarLowerStarAdjunction A f).unit.app G) ≫
        (Etale.baseChangeMap A sq).app (((f)^*[A]).obj G) =
      (Etale.upperStarLowerStarAdjunction A f').unit.app (((g)^*[A]).obj G) ≫
        ((f')_*[A]).map ((Etale.squareUpperStarIso A sq).hom.app G) :=
  unit_mateEquiv _ _ _ G

/-- **Naturality of the base change map** in the sheaf.
(blueprint: `lemma:weil-pbc-underived-exchange-naturality`) -/
lemma Etale.baseChangeMap_naturality (sq : CommSq g' f' f g)
    {F F' : Sheaf X.smallEtaleTopology A} (u : F ⟶ F') :
    ((g)^*[A]).map (((f)_*[A]).map u) ≫ (Etale.baseChangeMap A sq).app F' =
      (Etale.baseChangeMap A sq).app F ≫ ((f')_*[A]).map (((g')^*[A]).map u) :=
  (Etale.baseChangeMap A sq).naturality u

/-- The square isomorphism `g'_* ⋙ f_* ≅ f'_* ⋙ g_*` of pushforwards attached to a
commutative square `g' ≫ f = f' ≫ g`: both sides are identified with the pushforward along
the diagonal by `AlgebraicGeometry.Etale.lowerStarComp`. -/
noncomputable def Etale.squareLowerStarIso (sq : CommSq g' f' f g) :
    (g')_*[A] ⋙ (f)_*[A] ≅ (f')_*[A] ⋙ (g)_*[A] :=
  Etale.lowerStarComp A g' f ≪≫ (Etale.lowerStarComp A f' g (g' ≫ f) sq.w).symm

/-- **The pushforward form of the base change map**: the mate of the base change map with
respect to the adjunctions `g'^* ⊣ g'_*` and `g^* ⊣ g_*` is the square isomorphism of the
pushforwards `f_* g'_* ≅ g_* f'_*`. Equivalently, the base change map is the mate of the
square isomorphism `AlgebraicGeometry.Etale.squareLowerStarIso` along the horizontal
adjunctions, which is the usual description of the base change map. -/
lemma Etale.mateEquiv_baseChangeSquare (sq : CommSq g' f' f g) :
    (mateEquiv (Etale.upperStarLowerStarAdjunction A g') (Etale.upperStarLowerStarAdjunction A g)
      (Etale.baseChangeSquare A sq)).natTrans = (Etale.squareLowerStarIso A sq).hom := by
  rw [Etale.baseChangeSquare, iterated_mateEquiv_conjugateEquiv]
  change conjugateEquiv _ _ ((Etale.upperStarComp A f' g (g' ≫ f) sq.w).inv ≫
    (Etale.upperStarComp A g' f).hom) = (Etale.lowerStarComp A g' f).hom ≫
    (Etale.lowerStarComp A f' g (g' ≫ f) sq.w).inv
  rw [← conjugateEquiv_comp _ (Etale.upperStarLowerStarAdjunction A (g' ≫ f))]
  congr 1
  · exact congrArg Iso.hom (Etale.conjugateIsoEquiv_upperStarComp A g' f)
  · exact congrArg Iso.inv (Etale.conjugateIsoEquiv_upperStarComp A f' g (g' ≫ f) sq.w)

/-- The base change map is the inverse mate of the square isomorphism of the pushforwards
along the adjunctions `g'^* ⊣ g'_*` and `g^* ⊣ g_*`. -/
lemma Etale.baseChangeSquare_eq_mateEquiv_symm (sq : CommSq g' f' f g) :
    Etale.baseChangeSquare A sq =
      (mateEquiv (Etale.upperStarLowerStarAdjunction A g')
        (Etale.upperStarLowerStarAdjunction A g)).symm
        (TwoSquare.mk _ _ _ _ (Etale.squareLowerStarIso A sq).hom) := by
  rw [← Etale.mateEquiv_baseChangeSquare]
  exact (Equiv.symm_apply_apply _ _).symm

end Square

section IsIso

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- **The base change map is an isomorphism when the horizontal maps are universal
homeomorphisms**, in particular for the identity square: the pullbacks along `g` and `g'`
are then equivalences, so the adjunctions `g^* ⊣ g_*` and `g'^* ⊣ g'_*` have invertible unit
and counit, and the base change map is the mate along them of the square isomorphism of the
pushforwards (`AlgebraicGeometry.Etale.baseChangeSquare_eq_mateEquiv_symm`). -/
instance Etale.isIso_baseChangeMap_of_isUniversalHomeomorphism (sq : CommSq g' f' f g)
    [IsUniversalHomeomorphism g] [IsUniversalHomeomorphism g'] :
    IsIso (Etale.baseChangeMap A sq) := by
  have h₁ := Etale.isEquivalence_upperStar A g'
  have h₂ := Etale.isEquivalence_lowerStar A g
  have : IsIso (Etale.upperStarLowerStarAdjunction A g').unit := inferInstance
  have : IsIso (Etale.upperStarLowerStarAdjunction A g).counit := inferInstance
  change IsIso (Etale.baseChangeSquare A sq).natTrans
  rw [Etale.baseChangeSquare_eq_mateEquiv_symm]
  unfold mateEquiv
  dsimp only [Equiv.coe_fn_symm_mk]
  infer_instance

end IsIso

end AlgebraicGeometry
