/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!

# Weil sheaves of `ℚ̄_ℓ`-modules and their stalks

Let `ℓ` be a prime, `ℚ̲̄_ℓ = Profinite.padicAlgClRingObj ℓ` the condensed ring of `ℚ̄_ℓ`, and
let `X` be a scheme over `Spec k` with an automorphism `e : X ≅ X` over `Spec k`. Write
`Mod_X := Mod_{ℚ̲̄_ℓ,X}` for the category of sheaves of `ℚ̲̄_ℓ,X`-modules on the pro-étale site of
`X`, and `e^* = (e.hom.left)^*⟦ℚ̲̄_ℓ⟧` for the pullback on it.

A *Weil sheaf* of `ℚ̄_ℓ`-modules (`ProEtale.CondensedRing.WeilSheaf`) is an object `F` of
`Mod_X` together with an isomorphism `φ_F : e^* F ≅ F` as structure data, that is an object of
`CategoryTheory.Endofunctor.IsoAlgebra e^*`. Morphisms are morphisms of module objects
commuting with the structure isomorphisms.

## Stalks

Let `Ω` be a separably closed field and `x̄ : Spec Ω ⟶ X` a geometric point which is fixed by
`e` up to an automorphism `σ` of `Spec Ω`, that is `x̄ ≫ e = σ ≫ x̄`. The pullback `σ^*` on
`Mod_{Spec Ω}` is canonically isomorphic to the identity
(`ProEtale.CondensedRing.padicAlgClUpperStarIsoId`), so the stalk `x̄^* F` of a Weil sheaf is a
Weil object for the identity functor `𝟭` of `Mod_{Spec Ω}`, with structure isomorphism
```
x̄^* F ≅ σ^* x̄^* F ≅ (σ ≫ x̄)^* F = (x̄ ≫ e)^* F ≅ x̄^* e^* F --x̄^* φ_F--> x̄^* F,
```
the comparison `x̄^* ≅ e^* ⋙ x̄^*` being `ProEtale.CondensedRing.weilStalkComparison`. The
stalk functor `ProEtale.CondensedRing.WeilSheaf.stalkFunctor` is the transport
`CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso` along this comparison.

## The Frobenius

Let `k` be a finite field and `X₀` a scheme over `k` with structure morphism `f`. The geometric
fiber `X = X₀ ×_{Spec k} Spec k̄` is a scheme over `Spec k` through the projection to `X₀`
(`Scheme.Hom.geometricFiberOver`), and the geometric Galois Frobenius `g_X = 𝟙 X₀ × σ` is an
automorphism of it over `Spec k` (`Scheme.Hom.geometricFrobeniusOver`). Weil sheaves for
`g_X` are the classical Weil sheaves on `X₀`.

The geometric Galois Frobenius fixes no geometric point of `X`, being semilinear over `k̄`. A
`k`-rational point `x₀` of `X₀` instead gives the geometric point
`x̄ = (x₀, 𝟙) : Spec k̄ ⟶ X` (`Scheme.Hom.geometricPointOfSection`), which is fixed up to the
Frobenius `σ` of `Spec k̄`: `x̄ ≫ g_X = σ ≫ x̄`
(`Scheme.Hom.geometricPointOfSection_comp_geometricFrobenius`). The stalk at `x̄` with its
Frobenius action is `ProEtale.CondensedRing.WeilSheaf.frobeniusStalkFunctor`.

## Main definitions

- `ProEtale.CondensedRing.WeilSheaf`: the category of Weil sheaves of `ℚ̄_ℓ`-modules.
- `ProEtale.CondensedRing.WeilSheaf.stalkFunctor`: the stalk at a geometric point fixed by `e`
  up to an automorphism of `Spec Ω`, a functor `WeilSheaf ℓ e ⥤ IsoAlgebra (𝟭 Mod_{Spec Ω})`.
- `ProEtale.CondensedRing.WeilSheaf.frobeniusStalkFunctor`: the stalk of a Weil sheaf for the
  geometric Galois Frobenius at the geometric point over a `k`-rational point,
  a functor `WeilSheaf ℓ f.geometricFrobeniusOver ⥤ IsoAlgebra (𝟭 Mod_{Spec k̄})`.

## Sorried input

- `ProEtale.CondensedRing.padicAlgClUpperStarIsoId`: the pullback along an automorphism of the
  spectrum of a separably closed field is isomorphic to the identity. The pro-étale site of
  `Spec Ω` is equivalent to profinite sets, through `S ↦ Spec C(S, Ω)`, and base change along
  `σ` acts on it through the canonical isomorphisms `C(S, Ω) ⊗_{Ω, σ} Ω ≅ C(S, Ω)`.
- `ProEtale.CondensedRing.weilStalkComparison`: the composite displayed above.

-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

namespace ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]

section Stalk

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} (e : X ≅ X)

/-- A *Weil sheaf* of `ℚ̄_ℓ`-modules for an automorphism `e : X ≅ X` over `Spec k` is a sheaf `F`
of `ℚ̲̄_ℓ,X`-modules on the pro-étale site of `X` together with an isomorphism
`φ_F : e^* F ≅ F`, where `e^* = (e.hom.left)^*⟦ℚ̲̄_ℓ⟧`. The isomorphism `φ_F` is structure data,
and morphisms are morphisms of module objects commuting with the structure isomorphisms. -/
abbrev WeilSheaf : Type _ :=
  IsoAlgebra (e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧

variable {Ω : Type u} [Field Ω] [hΩ : IsSepClosed Ω] (σ : Spec (.of Ω) ≅ Spec (.of Ω))

include hΩ

/-- The pullback `σ^*` of `ℚ̲̄_ℓ`-modules along an automorphism `σ` of the spectrum of a
separably closed field `Ω` is isomorphic to the identity. See the module docstring for the
argument. -/
noncomputable def padicAlgClUpperStarIsoId :
    (σ.hom)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ≅ 𝟭 _ :=
  sorry

variable (x : Spec (.of Ω) ⟶ X.left)

/-- The Frobenius comparison of the stalk at a geometric point `x̄` fixed by `e` up to an
automorphism `σ` of `Spec Ω`: `x̄^* ≅ e^* ⋙ x̄^*`, that is `x̄^* F ≅ x̄^* e^* F`, the composite of
`padicAlgClUpperStarIsoId`, the composition isomorphisms of the pullback and
`x̄ ≫ e = σ ≫ x̄`. -/
noncomputable def weilStalkComparison (_hx : x ≫ e.hom.left = σ.hom ≫ x) :
    (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ⋙ 𝟭 _ ≅
      (e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ⋙ (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  sorry

/-- The stalk `x̄^* F` at a geometric point `x̄ : Spec Ω ⟶ X` fixed by `e` up to an automorphism
`σ` of `Spec Ω` of a Weil sheaf `(F, φ_F)`, as a Weil object for the identity functor: its
structure isomorphism is the automorphism `x̄^* F ≅ x̄^* e^* F ≅ x̄^* F` given by
`weilStalkComparison` and `x̄^* φ_F`. -/
noncomputable def WeilSheaf.stalkFunctor (hx : x ≫ e.hom.left = σ.hom ≫ x) :
    WeilSheaf ℓ e ⥤
      IsoAlgebra (𝟭 (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of Ω))))) :=
  IsoAlgebra.mapOfNatIso (weilStalkComparison ℓ e σ x hx)

omit hΩ in
@[simp]
lemma WeilSheaf.stalkFunctor_obj_carrier (hx : x ≫ e.hom.left = σ.hom ≫ x)
    (F : WeilSheaf ℓ e) :
    ((WeilSheaf.stalkFunctor ℓ e σ x hx).obj F).carrier =
      (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj F.carrier :=
  rfl

end Stalk

end ProEtale.CondensedRing

/-! ### The geometric Galois Frobenius -/

namespace Scheme.Hom

variable {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))

/-- The geometric fiber `X = X₀ ×_{Spec k} Spec k̄` as a scheme over `Spec k`, through the
projection `p_X : X ⟶ X₀` followed by `f`. -/
noncomputable def geometricFiberOver : Over (Spec (.of k)) :=
  Over.mk (f.geometricFiberProj ≫ f)

/-- The geometric Galois Frobenius `g_X = 𝟙 X₀ × σ` as an automorphism of the geometric fiber
over `Spec k`. -/
noncomputable def geometricFrobeniusOver : f.geometricFiberOver ≅ f.geometricFiberOver :=
  Over.isoMk f.geometricFrobenius (by simp [geometricFiberOver])

/-- The geometric point `x̄ = (x₀, 𝟙) : Spec k̄ ⟶ X₀ ×_{Spec k} Spec k̄` of the geometric fiber
lying over a `k`-rational point `x₀` of `X₀`, that is a section of `f`. -/
noncomputable def geometricPointOfSection (x₀ : Spec (.of k) ⟶ X₀) (hx₀ : x₀ ≫ f = 𝟙 _) :
    Spec (.of (AlgebraicClosure k)) ⟶ f.geometricFiber :=
  pullback.lift (specAlgebraicClosure k ≫ x₀) (𝟙 _) (by simp [hx₀])

/-- The geometric point over a `k`-rational point is fixed by the geometric Galois Frobenius up
to the Frobenius `σ` of `Spec k̄`: `x̄ ≫ g_X = σ ≫ x̄`. -/
theorem geometricPointOfSection_comp_geometricFrobenius (x₀ : Spec (.of k) ⟶ X₀)
    (hx₀ : x₀ ≫ f = 𝟙 _) :
    f.geometricPointOfSection x₀ hx₀ ≫ f.geometricFrobenius.hom =
      (geometricFrobeniusField k).hom ≫ f.geometricPointOfSection x₀ hx₀ := by
  apply pullback.hom_ext
  · change _ ≫ _ ≫ f.geometricFiberProj = _ ≫ _ ≫ f.geometricFiberProj
    rw [geometricFrobenius_hom_comp_geometricFiberProj]
    simp [geometricPointOfSection, geometricFiberProj]
  · change _ ≫ _ ≫ f.geometricFiberToAlgebraicClosure =
      _ ≫ _ ≫ f.geometricFiberToAlgebraicClosure
    rw [geometricFrobenius_hom_comp_geometricFiberToAlgebraicClosure]
    rw [geometricPointOfSection, geometricFiberToAlgebraicClosure, pullback.lift_snd_assoc,
      pullback.lift_snd, Category.comp_id]
    exact Category.id_comp _

end Scheme.Hom

namespace ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}}
  (f : X₀ ⟶ Spec (.of k))

/-- The stalk of a Weil sheaf on `X₀`, that is a Weil sheaf for the geometric Galois Frobenius
of the geometric fiber, at the geometric point `x̄` over a `k`-rational point `x₀` of `X₀`, as a
Weil object for the identity functor of `Mod_{Spec k̄}`: its structure isomorphism is the action
of Frobenius on the stalk. -/
noncomputable def WeilSheaf.frobeniusStalkFunctor (x₀ : Spec (.of k) ⟶ X₀)
    (hx₀ : x₀ ≫ f = 𝟙 _) :
    WeilSheaf ℓ f.geometricFrobeniusOver ⥤
      IsoAlgebra (𝟭 (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of (AlgebraicClosure k))))
        Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of (AlgebraicClosure k)))))) :=
  WeilSheaf.stalkFunctor ℓ f.geometricFrobeniusOver (geometricFrobeniusField k)
    (f.geometricPointOfSection x₀ hx₀)
    (f.geometricPointOfSection_comp_geometricFrobenius x₀ hx₀)

end ProEtale.CondensedRing

end AlgebraicGeometry
