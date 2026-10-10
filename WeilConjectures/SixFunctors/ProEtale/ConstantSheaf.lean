/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections
public import WeilConjectures.SixFunctors.ProEtale.Derived.LocalCocycle
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.GlobalSections

/-!
# Constant pro-étale sheaves of modules

Let `X` be a scheme and `Λ` a commutative ring. This file records the properties of the constant
sheaf functor `c : Mod_Λ ⥤ Sh(X_proét, Λ)` used to compare complexes of pro-étale sheaves with
complexes of `Λ`-modules.

## Main results

- `AlgebraicGeometry.ProEtale.monoidal_constantSheaf`: `c` is a monoidal functor.
- `AlgebraicGeometry.ProEtale.isDualizable_constantSheaf_obj`: the constant sheaf attached to a
  finite projective `Λ`-module is dualizable.
- `AlgebraicGeometry.ProEtale.subsingleton_of_isZero_constantSheaf_obj`: over a nonempty scheme,
  `c` reflects zero objects.
- `AlgebraicGeometry.ProEtale.upperStarConstantSheafIso`: the pullback of a constant sheaf is
  constant.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.ProEtale

open _root_.AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]

/-- The constant sheaf functor `Mod_Λ ⥤ Sh(X_proét, Λ)` is monoidal: it is the composite of the
constant presheaf functor and the sheafification, which are both monoidal. -/
noncomputable instance monoidal_constantSheaf :
    (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)).Monoidal :=
  inferInstanceAs ((Functor.const _ ⋙ presheafToSheaf _ _).Monoidal)

/-- The constant sheaf attached to a finite projective `Λ`-module is dualizable. -/
theorem isDualizable_constantSheaf_obj (V : ModuleCat.{u + 1} Λ) [Module.Finite Λ V]
    [Module.Projective Λ V] :
    IsDualizable ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)).obj V) :=
  (ModuleCat.isDualizable_of_projective V).map _

/-- The constant sheaf functor is left adjoint to the global sections. -/
noncomputable def constantSheafAdjunction (X : Scheme.{u}) :
    constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ) ⊣
      (sheafSections _ _).obj (op (terminalProEt X)) :=
  constantSheafAdj _ _ (Scheme.ProEt.isTerminalMkId X)

instance : (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)).IsLeftAdjoint :=
  (constantSheafAdjunction X).isLeftAdjoint

instance : PreservesFiniteLimits
    (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :=
  inferInstanceAs (PreservesFiniteLimits (Functor.const _ ⋙ presheafToSheaf _ _))

/-- Over a nonempty scheme, a `Λ`-module whose constant sheaf vanishes is zero: the constant
sections `V ⟶ c(V)(X)` are injective. -/
lemma subsingleton_of_isZero_constantSheaf_obj [Nonempty X] {V : ModuleCat.{u + 1} Λ}
    (h : IsZero ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)).obj V)) :
    Subsingleton V := by
  have : Nonempty (terminalProEt X).left := inferInstanceAs (Nonempty X)
  refine ⟨fun a b ↦ constantSheaf_toSheafify_app_injective V (U := terminalProEt X) ?_⟩
  have := (h.of_iso (Iso.refl _)).eq_of_src (𝟙 _) 0
  exact (congrArg (fun f ↦ f.hom.app (op (terminalProEt X))
    ((toSheafify _ ((Functor.const _).obj V)).app _ a)) (h.eq_of_src (𝟙 _) 0)).trans
      (congrArg (fun f ↦ f.hom.app (op (terminalProEt X))
        ((toSheafify _ ((Functor.const _).obj V)).app _ b)) (h.eq_of_src (𝟙 _) 0)).symm

/-- The sections over the terminal object of `Z_proét` are the sections of the pushforward along
`g : Z ⟶ Y` over the terminal object of `Y_proét`. -/
noncomputable def sectionsLowerStarIso {Y Z : Scheme.{u}} (g : Z ⟶ Y) :
    (sheafSections (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ)).obj (op (terminalProEt Z)) ≅
      (g)_*[ModuleCat.{u + 1} Λ] ⋙
        (sheafSections (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)).obj
          (op (terminalProEt Y)) :=
  (sheafSections _ _).mapIso
    (show (_ : Z.ProEt) ≅ terminalProEt Z from overPullbackObjMkIdIso g).op ≪≫
    NatIso.ofComponents (fun _ ↦ Iso.refl _)

/-- The pullback of a constant sheaf is the constant sheaf: both `c_Y ⋙ g^*` and `c_Z` are left
adjoint to `G ↦ Γ(Z, G) = Γ(Y, g_* G)`. -/
noncomputable def upperStarConstantSheafIso {Y Z : Scheme.{u}} (g : Z ⟶ Y) :
    constantSheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ) ⋙
        (g)^*[ModuleCat.{u + 1} Λ] ≅
      constantSheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ) :=
  ((constantSheafAdjunction Y).comp (upperStarLowerStarAdjunction _ g)).leftAdjointUniq
    ((constantSheafAdjunction Z).ofNatIsoRight (sectionsLowerStarIso g))

/-- The constant sheaf functor sends constant sections to constant sections. -/
lemma constantSheaf_map_hom_app_toSheafify {V W : ModuleCat.{u + 1} Λ} (f : V ⟶ W) (U : X.ProEt)
    (v : V) :
    ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)).map f).hom.app (op U)
        ((toSheafify (Scheme.ProEt.topology X) ((Functor.const _).obj V)).app (op U) v) =
      (toSheafify (Scheme.ProEt.topology X) ((Functor.const _).obj W)).app (op U) (f v) := by
  have h := congrArg (fun φ ↦ (φ.app (op U)) v)
    (toSheafify_naturality (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).map f))
  exact h.symm

/-- Over a nonempty scheme, the constant sheaf functor is faithful. -/
lemma constantSheaf_map_injective [Nonempty X] {V W : ModuleCat.{u + 1} Λ} {f g : V ⟶ W}
    (h : (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)).map f =
      (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)).map g) : f = g := by
  have : Nonempty (terminalProEt X).left := inferInstanceAs (Nonempty X)
  ext v
  apply constantSheaf_toSheafify_app_injective W (U := terminalProEt X)
  rw [← constantSheaf_map_hom_app_toSheafify, ← constantSheaf_map_hom_app_toSheafify, h]

end AlgebraicGeometry.ProEtale
