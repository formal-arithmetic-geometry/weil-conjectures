/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.KFlat
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal

/-!

# Flatness of étale sheaves of `Λ`-modules is checked on stalks

Let `Λ` be a commutative ring. An étale sheaf `F` of `Λ`-modules on a scheme `X` is a flat
object (`CategoryTheory.ObjectProperty.flat`: tensoring with `F` is exact) if and only if
its stalk `F_s` at every geometric point `s` of `X` is a flat object of `ModuleCat Λ`.

* If every stalk is flat, tensoring with `F` is exact: the fibre functors are exact and
  jointly reflect exactness, and the stalk of `F ⊗ G` is `F_s ⊗ G_s`
  (`AlgebraicGeometry.Etale.sheafFiberTensorIso`).
* If `F` is flat, then for an injective map `f : M ⟶ N` of `Λ`-modules the map of constant
  sheaves `M_X ⟶ N_X` is a monomorphism, hence so is `F ⊗ M_X ⟶ F ⊗ N_X` and its stalk
  `F_s ⊗ M ⟶ F_s ⊗ N` at `s`. As tensoring is right exact, `F_s` is flat.

Since the stalk of `g^* F` at `s` is the stalk of `F` at `s ≫ g`
(`AlgebraicGeometry.Etale.upperStarCompUliftSheafFiberIso`), the pullback `g^*` preserves
flat sheaves of `Λ`-modules, which is the instance
`AlgebraicGeometry.Etale.UpperStarPreservesFlat (ModuleCat Λ)`.

The monoidal structure on étale sheaves is the global instance
`CategoryTheory.GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall`.

## Main results

- `AlgebraicGeometry.Etale.flat_iff_sheafFiber`: an étale sheaf of `Λ`-modules is flat if
  and only if all its stalks at geometric points are flat.
- `AlgebraicGeometry.Etale.upperStarPreservesFlat_moduleCat`: for every morphism of
  schemes `g`, the pullback `g^*` sends flat étale sheaves of `Λ`-modules to flat ones.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

namespace Etale

/-- An additive endofunctor `T` of étale sheaves of `Λ`-modules is exact if, at every point `x`
of `X`, its composite with the stalk functor at the geometric point over `x` is isomorphic to
the stalk functor followed by an exact additive functor `T' x`: the stalk functors are exact
and jointly reflect exactness. -/
lemma exactFunctor_of_sheafFiber
    (T : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [T.Additive]
    (T' : X → ModuleCat.{u + 1} Λ ⥤ ModuleCat.{u + 1} Λ) [∀ x, (T' x).Additive]
    (hT' : ∀ x, exactFunctor _ _ (T' x))
    (e : ∀ x, T ⋙ (X.uliftPointSmallEtale x).sheafFiber ≅
      (X.uliftPointSmallEtale x).sheafFiber ⋙ T' x) :
    exactFunctor _ _ T := by
  refine ((Functor.exact_tfae T).out 1 3).1 fun S hS ↦ ?_
  rw [(jointlyReflectIsomorphisms_ulift_pointSmallEtale X (ModuleCat.{u + 1} Λ)).exact_iff]
  rintro ⟨-, ⟨x⟩⟩
  have := (hT' x).preservesFiniteLimits
  have := (hT' x).preservesFiniteColimits
  refine (ShortComplex.exact_iff_of_iso ?_).2
    ((hS.map (X.uliftPointSmallEtale x).sheafFiber).map (T' x))
  exact ShortComplex.isoMk ((e x).app _) ((e x).app _) ((e x).app _)
    ((e x).hom.naturality _).symm ((e x).hom.naturality _).symm

/-- An étale sheaf of `Λ`-modules whose stalks at all geometric points are flat is flat: the
stalk of `F ⊗ G` is `F_s ⊗ G_s`, so tensoring with `F` is exact on stalks. -/
lemma flat_of_flat_sheafFiber (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : ∀ {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      ObjectProperty.flat ((pointSmallEtale s).ulift.{u + 1}.sheafFiber.obj F)) :
    ObjectProperty.flat F :=
  ⟨exactFunctor_of_sheafFiber (tensorLeft F)
      (fun x ↦ tensorLeft ((X.uliftPointSmallEtale x).sheafFiber.obj F))
      (fun x ↦ (hF (X.algClosurePoint x)).tensorLeft)
      (fun x ↦ NatIso.ofComponents (fun G ↦ sheafFiberTensorIso (X.algClosurePoint x) F G)
        (fun g ↦ (Functor.OplaxMonoidal.δ_natural_right
          (pointSmallEtale (X.algClosurePoint x)).ulift.{u + 1}.sheafFiber F g).symm)),
    exactFunctor_of_sheafFiber (tensorRight F)
      (fun x ↦ tensorRight ((X.uliftPointSmallEtale x).sheafFiber.obj F))
      (fun x ↦ (hF (X.algClosurePoint x)).tensorRight)
      (fun x ↦ NatIso.ofComponents (fun G ↦ sheafFiberTensorIso (X.algClosurePoint x) G F)
        (fun g ↦ (Functor.OplaxMonoidal.δ_natural_left
          (pointSmallEtale (X.algClosurePoint x)).ulift.{u + 1}.sheafFiber g F).symm))⟩

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)

/-- If the étale sheaf `F` of `Λ`-modules is flat, then tensoring its stalk `F_s` with an
injective map `f : M ⟶ N` of `Λ`-modules gives an injective map. Indeed `F_s ◁ f` is, up to
isomorphism, the stalk of `F ◁ f_X`, where `f_X : M_X ⟶ N_X` is the map of constant sheaves,
which is a monomorphism since its stalks are `f`. -/
lemma mono_sheafFiber_obj_whiskerLeft {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (hF : ObjectProperty.flat F) {M N : ModuleCat.{u + 1} Λ} (f : M ⟶ N) [Mono f] :
    Mono ((pointSmallEtale s).ulift.{u + 1}.sheafFiber.obj F ◁ f) := by
  let c := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  have fac (Φ : X.smallEtaleTopology.Point.{u + 1}) {M N : ModuleCat.{u + 1} Λ} (f : M ⟶ N) :
      f = (Φ.sheafFiberConstantSheafIso M).inv ≫ Φ.sheafFiber.map (c.map f) ≫
        (Φ.sheafFiberConstantSheafIso N).hom :=
    (Iso.eq_inv_comp _).2
      (Φ.sheafFiber_map_constantSheaf_map_sheafFiberConstantSheafIso_hom f).symm
  have : Mono (c.map f) := by
    refine ((isConservativeFamilyOfPoints_ulift_pointSmallEtale X).jointlyReflectMonomorphisms
      (ModuleCat.{u + 1} Λ)).mono_iff _ |>.2 fun Φ ↦ ?_
    have := fac Φ.obj f
    rw [Iso.eq_inv_comp, ← Iso.comp_inv_eq, Category.assoc] at this
    rw [← this]
    infer_instance
  have := hF.tensorLeft.preservesFiniteLimits
  have : Mono (F ◁ c.map f) := (tensorLeft F).map_mono (c.map f)
  let Φ := (pointSmallEtale s).ulift.{u + 1}
  have : Mono (Φ.sheafFiber.obj F ◁ Φ.sheafFiber.map (c.map f)) := by
    rw [(IsIso.eq_inv_comp _).2 (Functor.OplaxMonoidal.δ_natural_right Φ.sheafFiber F (c.map f))]
    infer_instance
  rw [fac Φ f, MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_comp]
  infer_instance

/-- The stalks of a flat étale sheaf of `Λ`-modules at geometric points are flat. Tensoring
with the stalk is right exact, and it preserves monomorphisms by
`AlgebraicGeometry.Etale.mono_sheafFiber_obj_whiskerLeft`. -/
lemma flat_sheafFiber_of_flat {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (hF : ObjectProperty.flat F) :
    ObjectProperty.flat ((pointSmallEtale s).ulift.{u + 1}.sheafFiber.obj F) := by
  rw [ObjectProperty.flat_iff_preservesFiniteLimits]
  refine ((Functor.preservesFiniteLimits_tfae _).out 0 3).1 fun S hS ↦ ?_
  have := hS.mono_f
  exact ⟨((Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).1
    inferInstance S hS).1,
    mono_sheafFiber_obj_whiskerLeft s hF S.f⟩

variable (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))

/-- **Flatness of étale sheaves of `Λ`-modules is checked on stalks.** An étale sheaf of
`Λ`-modules is flat if and only if its stalk at every geometric point is flat. -/
theorem flat_iff_sheafFiber :
    ObjectProperty.flat F ↔ ∀ {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      ObjectProperty.flat ((pointSmallEtale s).ulift.{u + 1}.sheafFiber.obj F) :=
  ⟨fun hF _ _ _ s ↦ flat_sheafFiber_of_flat s hF, flat_of_flat_sheafFiber F⟩

/-- **The pullback of étale sheaves of `Λ`-modules preserves flatness.** For
`g : Y ⟶ Z` and a flat sheaf `F` on `Z`, the stalk of `g^* F` at a geometric point `s` of `Y`
is the stalk of `F` at `s ≫ g`, which is flat, so `g^* F` is flat by
`AlgebraicGeometry.Etale.flat_iff_sheafFiber`. -/
instance upperStarPreservesFlat_moduleCat :
    Etale.UpperStarPreservesFlat (ModuleCat.{u + 1} Λ) where
  preservesFlat {Y Z} g := by
    constructor
    intro F hF
    exact flat_of_flat_sheafFiber _ fun s ↦
      ObjectProperty.prop_of_iso _ ((upperStarCompUliftSheafFiberIso _ g s).app F).symm
        (flat_sheafFiber_of_flat (s ≫ g) hF)

end Etale

end AlgebraicGeometry
