/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import WeilConjectures.AlgebraicGeometry.Modules.Picard
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Presheaf
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Skeleton
public import WeilConjectures.Mathlib.Topology.Category.TopCat.Opens

/-!
# The pullback of `𝒪`-modules is monoidal, and the Picard group is a functor

Let `f : X ⟶ Y` be a morphism of schemes. The pullback functor
`AlgebraicGeometry.Scheme.Modules.pullback f : Y.Modules ⥤ X.Modules` is monoidal: it sends
the structure sheaf to the structure sheaf, and the tensor product of two `𝒪ᵧ`-modules to the
tensor product of their pullbacks.

The pullback functor is the left adjoint of the pushforward, which is lax monoidal, so it is
oplax monoidal; the point is that its structure maps are isomorphisms. This is reduced to the
same statement for presheaves of modules, proved in
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback`, via the universal
property of the category of sheaves of modules as a localization of presheaves of modules.

As a consequence, the pullback of an invertible `𝒪ᵧ`-module is an invertible `𝒪ₓ`-module, and
the pullback induces a group homomorphism `Pic(Y) ⟶ Pic(X)`, contravariantly functorial in the
morphism of schemes.

## Main declarations

- `AlgebraicGeometry.Scheme.Modules.pullback f` is monoidal (an instance).
- `SheafOfModules.Invertible.pullback`: the pullback of an invertible module is invertible.
- `AlgebraicGeometry.Scheme.Pic.map`: the pullback homomorphism `Pic(Y) →* Pic(X)`, with
  `AlgebraicGeometry.Scheme.Pic.map_id` and `AlgebraicGeometry.Scheme.Pic.map_comp`.
- `AlgebraicGeometry.Scheme.Modules.restrictFunctor f` is monoidal (an instance), obtained by
  transporting the monoidal structure of the pullback functor along
  `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`. Its structure maps are
  `CategoryTheory.Functor.Monoidal.εIso` and `CategoryTheory.Functor.Monoidal.μIso`.
- `AlgebraicGeometry.Scheme.Modules.restrictTensorIsoOfRestrictIsoTensorUnit`: on an open
  subscheme trivialising `L`, the restriction of `F ⊗ L` is isomorphic to that of `F`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The composition of the pullback functor on presheaves of modules with the sheafification
functor is monoidal. -/
noncomputable instance :
    (PresheafOfModules.pullbackOfCommRingCat f.toRingCatPresheafHom ⋙
      SheafOfModules.sheafification X.sheaf).Monoidal :=
  inferInstanceAs (PresheafOfModules.pullbackOfCommRingCat f.toRingCatPresheafHom ⋙
    SheafOfModules.sheafification X.sheaf).Monoidal

/-- The pullback functor on sheaves of modules lifts, along the sheafification functor, the
composition of the pullback functor on presheaves of modules with the sheafification. -/
noncomputable instance :
    Localization.Lifting (SheafOfModules.sheafification Y.sheaf)
      ((Opens.grothendieckTopology Y).W.inverseImage (PresheafOfModules.toPresheaf _))
      (PresheafOfModules.pullbackOfCommRingCat f.toRingCatPresheafHom ⋙
        SheafOfModules.sheafification X.sheaf)
      (SheafOfModules.pullback f.toRingCatSheafHom) :=
  ⟨SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom⟩

/-- The pullback functor on sheaves of modules over schemes is monoidal: the pullback of a
tensor product is the tensor product of the pullbacks. -/
noncomputable instance : (SheafOfModules.pullback f.toRingCatSheafHom).Monoidal :=
  Localization.Monoidal.functorMonoidalOfComp (SheafOfModules.sheafification Y.sheaf)
    ((Opens.grothendieckTopology Y).W.inverseImage (PresheafOfModules.toPresheaf _))
    (SheafOfModules.pullback f.toRingCatSheafHom)
    (PresheafOfModules.pullbackOfCommRingCat f.toRingCatPresheafHom ⋙
      SheafOfModules.sheafification X.sheaf)

/-- The pullback functor on `𝒪ₓ`-modules is monoidal. -/
noncomputable instance : (Modules.pullback f).Monoidal :=
  inferInstanceAs (SheafOfModules.pullback f.toRingCatSheafHom).Monoidal

/-- The pullback of an invertible `𝒪ᵧ`-module is an invertible `𝒪ₓ`-module. -/
lemma _root_.SheafOfModules.Invertible.pullback {M : Y.Modules} (hM : M.Invertible) :
    ((Modules.pullback f).obj M).Invertible := by
  obtain ⟨N, ⟨e⟩⟩ := SheafOfModules.invertible_iff_exists.{u, u, u}.1 hM
  exact SheafOfModules.Invertible.left.{u, u, u} (N := (Modules.pullback f).obj N)
    (Functor.Monoidal.mapIsoTensorUnit (Modules.pullback f) e)

/-- The pullback homomorphism on Picard groups attached to a morphism of schemes: the class of
an invertible `𝒪ᵧ`-module is sent to the class of its pullback. -/
noncomputable def Pic.map : Y.Pic →* X.Pic :=
  Units.map (Skeleton.monoidHom (Modules.pullback f))

variable (X) in
@[simp]
lemma Pic.map_id : Pic.map (𝟙 X) = MonoidHom.id X.Pic := by
  rw [Pic.map, Skeleton.monoidHom_congr (Modules.pullbackId X), Skeleton.monoidHom_id,
    Units.map_id]
  rfl

@[simp]
lemma Pic.map_comp {Z : Scheme.{u}} (g : Y ⟶ Z) :
    Pic.map (f ≫ g) = (Pic.map f).comp (Pic.map g) := by
  rw [Pic.map, Pic.map, Pic.map, ← Skeleton.monoidHom_congr (Modules.pullbackComp f g),
    Skeleton.monoidHom_comp, Units.map_comp]

@[simp]
lemma Pic.map_comp_apply {Z : Scheme.{u}} (g : Y ⟶ Z) (x : Z.Pic) :
    Pic.map (f ≫ g) x = Pic.map f (Pic.map g x) := by
  rw [Pic.map_comp]
  rfl

@[simp]
lemma Pic.map_mk {M : Y.Modules} (hM : M.Invertible) :
    Pic.map f (Pic.mk M hM) = Pic.mk ((Modules.pullback f).obj M) (hM.pullback f) := by
  change Units.map (Skeleton.monoidHom (Modules.pullback f)) hM.unit = (hM.pullback f).unit
  rw [← Units.val_inj, Units.coe_map, IsUnit.unit_spec, IsUnit.unit_spec,
    Skeleton.monoidHom_toSkeleton]
  rfl

section Restrict

variable [IsOpenImmersion f]

/-- **Restriction along an open immersion is monoidal.** It is isomorphic to the pullback
functor, which is monoidal, so the monoidal structure transports along
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`.

In particular `CategoryTheory.Functor.Monoidal.μIso (Modules.restrictFunctor f) M N` is an
isomorphism `M|ₓ ⊗ N|ₓ ≅ (M ⊗ N)|ₓ` and `CategoryTheory.Functor.Monoidal.εIso` is an
isomorphism `𝟙_ X.Modules ≅ (𝟙_ Y.Modules)|ₓ`; both are natural and satisfy the associativity
and unitality constraints. The `SheafOfModules.unit` version of the latter is
`AlgebraicGeometry.Scheme.Modules.restrictUnitIso`. -/
noncomputable instance : (Modules.restrictFunctor f).Monoidal :=
  .transport (Modules.restrictFunctorIsoPullback f).symm

/-- On an open subscheme trivialising `L`, the restriction of `F ⊗ L` is isomorphic to the
restriction of `F`:

```text
                 μ⁻¹                 1 ⊗ e                ρ
  (F ⊗ L)|ₓ ────────────▸ F|ₓ ⊗ L|ₓ ────────▸ F|ₓ ⊗ 𝟙_ ─────▸ F|ₓ
```
-/
noncomputable def Modules.restrictTensorIsoOfRestrictIsoTensorUnit (F : Y.Modules)
    {L : Y.Modules} (e : L.restrict f ≅ 𝟙_ X.Modules) :
    (F ⊗ L).restrict f ≅ F.restrict f :=
  (Functor.Monoidal.μIso (Modules.restrictFunctor f) F L).symm ≪≫
    tensorIso (Iso.refl _) e ≪≫ ρ_ _

end Restrict

end AlgebraicGeometry.Scheme
