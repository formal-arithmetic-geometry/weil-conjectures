/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.SixFunctors.ProEtale.Adic.Ring

/-!
# Sheaves of modules over the constant `ℓ`-adic sheaf

Let `X` be a scheme and `ℚ̄_ℓ,X = AlgebraicGeometry.ProEtale.adicConstantSheaf ℓ X` the sheaf of
rings of locally finite continuous `ℓ`-adic functions on the pro-étale site of `X`. Following
Bhatt–Scholze (*The pro-étale topology for schemes*, §6.8), the `ℓ`-adic sheaves on `X` are the
sheaves of `ℚ̄_ℓ,X`-modules: the module objects over the monoid `ℚ̄_ℓ,X` of the monoidal category
of sheaves of `ℚ̄_ℓ`-modules (`AlgebraicGeometry.ProEtale.AdicSheaf`). This is a Grothendieck
abelian category, in which kernels, cokernels and extensions are computed on the underlying
sheaves of `ℚ̄_ℓ`-modules; but its extensions are those of `ℚ̄_ℓ,X`-modules, not of sheaves of
modules over the discrete field `ℚ̄_ℓ`.

For a morphism `g : Z ⟶ Y` the pushforward `g_*` and the pullback `g^*` of sheaves of
`ℚ̄_ℓ`-modules lift to sheaves of modules over the constant `ℓ`-adic sheaves: `g_*` is lax
monoidal, so `g_* M` is a `g_* ℚ̄_ℓ,Z`-module, hence a `ℚ̄_ℓ,Y`-module along the ring morphism
`ℚ̄_ℓ,Y ⟶ g_* ℚ̄_ℓ,Z` (`AlgebraicGeometry.ProEtale.isMonHom_adicConstantSheafToLowerStar`); and
`g^*` is monoidal, so `g^* M` is a `g^* ℚ̄_ℓ,Y`-module, hence a `ℚ̄_ℓ,Z`-module along the ring
isomorphism `g^* ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,Z`. The underlying sheaves are those of the pushforward and the
pullback of sheaves of `ℚ̄_ℓ`-modules, so both functors are exact, and they are adjoint
(`AlgebraicGeometry.ProEtale.adicUpperStarLowerStarAdjunction`).

## Main definitions

- `AlgebraicGeometry.ProEtale.AdicSheaf`: sheaves of `ℚ̄_ℓ,X`-modules on `X_proét`.
- `AlgebraicGeometry.ProEtale.AdicSheaf.unit`: the constant `ℓ`-adic sheaf as a module over
  itself.
- `AlgebraicGeometry.ProEtale.adicLowerStar`, `AlgebraicGeometry.ProEtale.adicUpperStar`: `g_*`
  and `g^*`, with notations `(g)_*ᵃ[l]` and `(g)^*ᵃ[l]`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime]

/-- The sheaves of modules over the constant `ℓ`-adic sheaf `ℚ̄_ℓ,X` on the small pro-étale site
of `X` (Bhatt–Scholze, §6.8): module objects over the monoid `ℚ̄_ℓ,X` in the monoidal category of
sheaves of `ℚ̄_ℓ`-modules. -/
abbrev AdicSheaf (X : Scheme.{u}) : Type (u + 2) :=
  Mod (Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)) (adicConstantSheaf l X)

variable {l}

namespace AdicSheaf

variable (l) in
/-- The constant `ℓ`-adic sheaf `ℚ̄_ℓ,X`, as a module over itself. -/
noncomputable abbrev unit (X : Scheme.{u}) : AdicSheaf l X :=
  Mod.regular (adicConstantSheaf l X)

/-- The underlying sheaf of `ℚ̄_ℓ`-modules of a sheaf of `ℚ̄_ℓ,X`-modules. -/
noncomputable abbrev forget (X : Scheme.{u}) :
    AdicSheaf l X ⥤ Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l) :=
  Mod.forget _

noncomputable instance (X : Scheme.{u}) : Abelian (AdicSheaf l X) :=
  Mod.instAbelian _

instance (X : Scheme.{u}) : IsGrothendieckAbelian.{u + 1} (AdicSheaf l X) :=
  Mod.isGrothendieckAbelian _

end AdicSheaf

section Functors

open scoped Obj

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

noncomputable instance : IsIso (((upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g).homEquiv
    _ _).symm (adicConstantSheafToLowerStar l g)) :=
  inferInstanceAs (IsIso (upperStarAdicConstantSheafHom l g))

instance : IsMonHom ((g)^*[WeilCoefficients.{u} l].map (adicConstantSheafToLowerStar l g)) :=
  inferInstance

instance : IsMonHom (show (g)^*[WeilCoefficients.{u} l].obj ((g)_*[WeilCoefficients.{u} l].obj
      (adicConstantSheaf l Z)) ⟶ adicConstantSheaf l Z from
    (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g).counit.app
      (adicConstantSheaf l Z)) := by
  have h := NatTrans.isMonHom_app (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g).counit
    (adicConstantSheaf l Z)
  constructor
  · dsimp only
    simpa only [Functor.obj.η_def, Functor.LaxMonoidal.comp_ε, Functor.comp_map,
      Functor.map_comp, Category.assoc, Functor.LaxMonoidal.id_ε, Functor.id_map,
      Category.id_comp] using h.one_hom
  · dsimp only
    simpa only [Functor.obj.μ_def, Functor.LaxMonoidal.comp_μ, Functor.comp_map,
      Functor.map_comp, Category.assoc, Functor.LaxMonoidal.id_μ, Functor.id_map,
      Category.id_comp] using h.mul_hom

instance : IsMonHom (((upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g).homEquiv
    _ _).symm (adicConstantSheafToLowerStar l g)) := by
  rw [Adjunction.homEquiv_counit]
  exact CategoryTheory.instIsMonHomComp _ (show (g)^*[WeilCoefficients.{u} l].obj
      ((g)_*[WeilCoefficients.{u} l].obj (adicConstantSheaf l Z)) ⟶ adicConstantSheaf l Z from
    (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g).counit.app
      (adicConstantSheaf l Z))

variable (l) in
/-- The pushforward `g_*` of sheaves of modules over the constant `ℓ`-adic sheaves: the
pushforward of the underlying sheaf, a module over `ℚ̄_ℓ,Y` along `ℚ̄_ℓ,Y ⟶ g_* ℚ̄_ℓ,Z`. -/
noncomputable def adicLowerStar : AdicSheaf l Z ⥤ AdicSheaf l Y :=
  (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g).modRight
    (adicConstantSheafToLowerStar l g)

variable (l) in
/-- The pullback `g^*` of sheaves of modules over the constant `ℓ`-adic sheaves: the pullback of
the underlying sheaf, a module over `ℚ̄_ℓ,Z` along `g^* ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,Z`. -/
noncomputable def adicUpperStar : AdicSheaf l Y ⥤ AdicSheaf l Z :=
  (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g).modLeft
    (adicConstantSheafToLowerStar l g)

@[inherit_doc adicLowerStar]
scoped notation "(" g ")_*ᵃ[" l "]" => adicLowerStar l g

@[inherit_doc adicUpperStar]
scoped notation "(" g ")^*ᵃ[" l "]" => adicUpperStar l g

variable (l) in
/-- The adjunction `g^* ⊣ g_*` on sheaves of modules over the constant `ℓ`-adic sheaves. -/
noncomputable def adicUpperStarLowerStarAdjunction : (g)^*ᵃ[l] ⊣ (g)_*ᵃ[l] :=
  (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g).modAdjunction _

/-- The underlying sheaf of `g_* M` is the pushforward of the underlying sheaf of `M`. -/
lemma adicLowerStar_obj_X (M : AdicSheaf l Z) :
    ((g)_*ᵃ[l].obj M).X = (g)_*[WeilCoefficients.{u} l].obj M.X :=
  rfl

/-- The underlying sheaf of `g^* M` is the pullback of the underlying sheaf of `M`. -/
lemma adicUpperStar_obj_X (M : AdicSheaf l Y) :
    ((g)^*ᵃ[l].obj M).X = (g)^*[WeilCoefficients.{u} l].obj M.X :=
  rfl

lemma adicLowerStar_map_hom {M N : AdicSheaf l Z} (f : M ⟶ N) :
    ((g)_*ᵃ[l].map f).hom = (g)_*[WeilCoefficients.{u} l].map f.hom :=
  rfl

lemma adicUpperStar_map_hom {M N : AdicSheaf l Y} (f : M ⟶ N) :
    ((g)^*ᵃ[l].map f).hom = (g)^*[WeilCoefficients.{u} l].map f.hom :=
  rfl

instance : ((g)_*ᵃ[l]).Additive :=
  inferInstanceAs (Functor.mapMod _ _ ⋙ Mod.comap _).Additive

instance : ((g)^*ᵃ[l]).Additive :=
  inferInstanceAs (Functor.mapMod _ _ ⋙ Mod.comap _).Additive

instance : PreservesFiniteLimits (g)_*ᵃ[l] :=
  have : PreservesFiniteLimits ((g)_*ᵃ[l] ⋙ AdicSheaf.forget Y) :=
    inferInstanceAs (PreservesFiniteLimits (AdicSheaf.forget Z ⋙ (g)_*[WeilCoefficients.{u} l]))
  preservesFiniteLimits_of_reflects_of_preserves _ (AdicSheaf.forget Y)

instance : PreservesFiniteLimits (g)^*ᵃ[l] :=
  have : PreservesFiniteLimits ((g)^*ᵃ[l] ⋙ AdicSheaf.forget Z) :=
    inferInstanceAs (PreservesFiniteLimits (AdicSheaf.forget Y ⋙ (g)^*[WeilCoefficients.{u} l]))
  preservesFiniteLimits_of_reflects_of_preserves _ (AdicSheaf.forget Z)

instance : PreservesFiniteColimits (g)^*ᵃ[l] :=
  have : PreservesFiniteColimits ((g)^*ᵃ[l] ⋙ AdicSheaf.forget Z) :=
    inferInstanceAs
      (PreservesFiniteColimits (AdicSheaf.forget Y ⋙ (g)^*[WeilCoefficients.{u} l]))
  preservesFiniteColimits_of_reflects_of_preserves _ (AdicSheaf.forget Z)

end Functors

end AlgebraicGeometry.ProEtale
