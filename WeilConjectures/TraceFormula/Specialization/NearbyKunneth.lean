/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.Kunneth
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.TraceFormula.Specialization.TraitProduct

/-!

# Gabber's Künneth formula for nearby cycles

Let `M` and `N` be models of finite type over the strictly henselian trait `S = Spec k'⟦t⟧`
(`k'` separably closed) and let `P` be their fibre product over `S`, with the projections
`φ₁ : P ⟶ M` and `φ₂ : P ⟶ N`
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.IsTraitProduct`).
**Gabber's Künneth formula** (Illusie, *Autour du théorème de monodromie locale*, Thm. 4.7;
blueprint `sk-prop-tf-nearby-external-kunneth`) says that the Künneth map of nearby cycles
```
Π_{A,B} : Ψ_M A ⊠ Ψ_N B ⟶ Ψ_P (A ⊠ B)
```
(`NearbyCyclesModel.kunnethMap`) is an isomorphism for bounded constructible `A` and `B`
(`NearbyCyclesModel.isIso_kunnethMap`).

## Models over the trait

A model is *of finite type over the trait along `q : 𝒳 ⟶ S` and `g : 𝒳_η̄ ⟶ Spec Ω`*
(`NearbyCyclesModel.IsTraitModelOver`) if `q` is separated and of finite type and `j`, `i` are the
inclusions of the fibres of `q` over the geometric generic point and the closed point; this is
`NearbyCyclesModel.IsTraitModel` with the structure morphisms made explicit.

The identification `ε : 𝒳_η̄ ⟶ X` of a model is arbitrary. The nearby cycles of SGA 7 XIII are
defined on complexes on the generic fibre `𝒳_η`, not on all complexes on the geometric generic
fibre `𝒳_η̄`; so the finiteness and Künneth theorems are stated for models whose `ε` factors
through the total space, `ε = j ≫ e` (then `Lε^* A = Lj^* Le^* A` comes from `𝒳_η`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {k' : Type u} [Field k']

section Product

variable {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {N : NearbyCyclesModel Y Y'.left} {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X}
  {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y} {f₂' : Z'.left ⟶ Y'.left}

variable (ℓ : ℕ) [Fact ℓ.Prime] [IsSepClosed k'] [Fact (ringChar k' ≠ ℓ)]

/-- **Gabber's Künneth formula for nearby cycles** (Illusie, *Autour du théorème de monodromie
locale*, Thm. 4.7; SGA 7 XIII; blueprint `sk-prop-tf-nearby-external-kunneth`): for the product
`P` over the strictly henselian trait `Spec k'⟦t⟧` of two models `M`, `N` of finite type and
bounded constructible `A`, `B`, the Künneth map of nearby cycles
`Π_{A,B} : Ψ_M A ⊠ Ψ_N B ⟶ Ψ_P (A ⊠ B)` is an isomorphism. The blueprint node is stated for
finite `ℓ`-primary coefficients and `D^b_ctf`; the statement here, for bounded constructible
`ℚ̄_ℓ`-complexes, follows from it by passage to the limit (Bhatt–Scholze, §6.8). -/
theorem isIso_kunnethMap {φ₁ : P.Hom M f₁ f₁'} {φ₂ : P.Hom N f₂ f₂'} (h : IsTraitProduct φ₁ φ₂)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))}
    (hB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y) B) :
    IsIso (kunnethMap (Profinite.padicAlgClRingObj ℓ) φ₁ φ₂ A B) :=
  sorry

end Product

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
