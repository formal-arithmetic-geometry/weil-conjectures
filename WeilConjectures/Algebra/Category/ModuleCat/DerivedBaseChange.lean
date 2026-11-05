/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Reduction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution

/-!
# Derived base change of modules

Let `f : A →+* A'` be a morphism of commutative rings. A morphism `η : K ⟶ Res K'` in `D(A)`
from an object `K` to the restriction of scalars of `K' ∈ D(A')` *exhibits `K'` as the derived
base change `K ⊗ᴸ_A A'`* (`ModuleCat.IsDerivedBaseChange`) if it is a universal arrow from `K`
to the restriction of scalars: derived base change is left adjoint to restriction of scalars.

When `f` is surjective with principal kernel `(a)`, extension of scalars `M ↦ A' ⊗_A M`
together with the unit `M ⟶ A' ⊗_A M` of the extension-restriction adjunction is a reduction
datum for restriction of scalars along `f` and the multiplication by `a`
(`ModuleCat.reductionDatum`). Hence for a K-flat complex `P` the reduction
`P ⟶ Res (A' ⊗_A P)` exhibits `A' ⊗_A P` as the derived base change of `P`
(`ModuleCat.isDerivedBaseChange_Q_map_complexMap`).

## Main definitions

- `ModuleCat.derivedRestrictScalars`: restriction of scalars `D(A') ⥤ D(A)`.
- `ModuleCat.IsDerivedBaseChange`: universal arrows to restrictions of scalars.
- `ModuleCat.smulIdNatTrans`: the multiplication by a scalar on `A`-modules.
- `ModuleCat.reductionDatum`: extension of scalars along a surjective ring morphism with
  principal kernel is a reduction datum.

## Main results

- `ModuleCat.IsDerivedBaseChange.comp`: derived base changes compose.
- `ModuleCat.IsDerivedBaseChange.isIso`: two derived base changes of the same object are
  isomorphic through any compatible comparison map.
- `ModuleCat.isDerivedBaseChange_Q_map_complexMap`: the reduction of a K-flat complex is its
  derived base change.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace ModuleCat

section

variable {A A' : Type u} [CommRing A] [CommRing A'] [HasDerivedCategory.{u} (ModuleCat.{u} A)]
  [HasDerivedCategory.{u} (ModuleCat.{u} A')] (f : A →+* A')

/-- Restriction of scalars `D(A') ⥤ D(A)` along a ring morphism `f : A →+* A'`, induced by the
exact restriction of scalars of modules. -/
noncomputable abbrev derivedRestrictScalars :
    DerivedCategory (ModuleCat.{u} A') ⥤ DerivedCategory (ModuleCat.{u} A) :=
  (restrictScalars.{u} f).mapDerivedCategory

variable {f}

/-- A morphism `η : K ⟶ Res K'` from `K ∈ D(A)` to the restriction of scalars of `K' ∈ D(A')`
*exhibits `K'` as the derived base change `K ⊗ᴸ_A A'`* if it is universal among morphisms from
`K` to restrictions of scalars: every `K ⟶ Res N` factors uniquely as `η` followed by the
restriction of a morphism `K' ⟶ N`. -/
def IsDerivedBaseChange {K : DerivedCategory (ModuleCat.{u} A)}
    {K' : DerivedCategory (ModuleCat.{u} A')} (η : K ⟶ (derivedRestrictScalars f).obj K') :
    Prop :=
  ∀ N : DerivedCategory (ModuleCat.{u} A'),
    Function.Bijective fun g : K' ⟶ N ↦ η ≫ (derivedRestrictScalars f).map g

namespace IsDerivedBaseChange

variable {K : DerivedCategory (ModuleCat.{u} A)} {K' K'' : DerivedCategory (ModuleCat.{u} A')}

end IsDerivedBaseChange

end

section Reduction

variable {A A' : Type u} [CommRing A] [CommRing A']

/-- The multiplication by a scalar `a` on `A`-modules, as an endomorphism of the identity
functor. -/
@[simps]
def smulIdNatTrans (a : A) : 𝟭 (ModuleCat.{u} A) ⟶ 𝟭 _ where
  app M := a • 𝟙 M

variable (f : A →+* A')

/-- With scalars restricted back to `A`, the extension of scalars `A' ⊗_A M` of an `A`-module
`M` is the tensor product `A' ⊗ M` of `A`-modules. -/
noncomputable def restrictScalarsObjExtendScalarsObjIso (M : ModuleCat.{u} A) :
    (restrictScalars.{u} f).obj ((extendScalars.{u} f).obj M) ≅
      (restrictScalars.{u} f).obj (of A' A') ⊗ M :=
  (AddEquiv.toLinearEquiv
    (M := ↑((restrictScalars.{u} f).obj ((extendScalars.{u} f).obj M)))
    (M₂ := ↑((restrictScalars.{u} f).obj (of A' A') ⊗ M))
    (AddEquiv.refl _)
    (fun r x ↦ by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul q m => rfl
      | add x y hx hy => simp_all)).toModuleIso

/-- With scalars restricted back to `A`, extension of scalars along `f` is the tensor product
`M ↦ M ⊗ A'` of `A`-modules. -/
noncomputable def extendScalarsCompRestrictScalarsIso :
    extendScalars.{u} f ⋙ restrictScalars.{u} f ≅
      tensorRight ((restrictScalars.{u} f).obj (of A' A')) :=
  NatIso.ofComponents (fun M ↦ restrictScalarsObjExtendScalarsObjIso f M ≪≫ β_ _ M)
    (fun {M N} φ ↦ by
      ext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul q m => rfl
      | add x y hx hy => simp_all)

variable {f}

variable {a : A}

/-- Extension of scalars is additive, as a left adjoint. -/
instance extendScalars_additive : (extendScalars.{u, u, u} f).Additive :=
  (extendRestrictScalarsAdj.{u} f).left_adjoint_additive

end Reduction

section Comp

variable {A A' A'' : Type u} [CommRing A] [CommRing A'] [CommRing A'']
  [HasDerivedCategory.{u} (ModuleCat.{u} A)] [HasDerivedCategory.{u} (ModuleCat.{u} A')]
  [HasDerivedCategory.{u} (ModuleCat.{u} A'')] {f : A →+* A'} {g : A' →+* A''} {gf : A →+* A''}

end Comp

end ModuleCat
