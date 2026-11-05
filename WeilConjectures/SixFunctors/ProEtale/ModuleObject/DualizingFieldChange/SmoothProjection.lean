/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Comp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Global
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Smooth
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.WeaklyEtaleIhom
public import WeilConjectures.TraceFormula.PurityDevissage
public import WeilConjectures.PoincareDuality.Biduality.Reduction

/-!

# Base change of the exceptional inverse image of a smooth proper morphism across fields

Let `f : Z ⟶ P` be a proper morphism of separated `k₁`-schemes of finite type with a cartesian
square
```
Z' --πZ--> Z
 |f'       |f
 v         v
P' --πP--> P
```
where `f'` is a proper morphism of separated `k₂`-schemes of finite type, and let
`β : πZ^* Rf^! ⟶ Rf'^! πP^*` be the base change map of the exceptional inverse image
(`ProEtale.CondensedRing.upperShriekBaseChangeOfMap`). This file proves that `β` is an
isomorphism when `f` is smooth of pure relative dimension `d` (for instance the projection
`ℙⁿ_P ⟶ P`) and

* `πP` is weakly étale
  (`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_of_smooth_of_weaklyEtale`,
  `ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_of_projectiveSpace_of_weaklyEtale`), or
* `P` is the point `Spec k₁` and `πP : Spec k₂ ⟶ Spec k₁` is arbitrary, e.g. a field extension
  (`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_of_smooth_point`).

More generally `β(N)` is an isomorphism as soon as `πP^*` commutes with `RHom(Rf_* ℚ̄_ℓ, N)`
(`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_of_smooth`).

## Proof

*The endomorphism trick.* An endomorphism `t` of `Rf'^! M` with `Rf'_* t` invertible is invertible
(`CategoryTheory.Adjunction.isIso_of_isIso_map_leftAdjoint` for `Rf'_* ⊣ Rf'^!`). Hence `β(N)` is
invertible as soon as `Rf'_* β(N)` is and the two sides are isomorphic in some way
(`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_of_iso`).

*Global sections.* Relative Verdier duality says that the duality map
`Rf_* RHom(K, Rf^! N) ⟶ RHom(Rf_* K, N)` of `(Rf_*, ε_N)` is invertible
(`ProEtale.CondensedRing.isIso_nearbyDualityMap_lowerStar_counit`, from
`ProEtale.CondensedRing.isIso_verdierExchange`). By the counit property of `β`, the abstract
proper identity `CategoryTheory.Verdier.isIso_map_nearbyDualityMap_of_proper_natTrans` (with
`G = Rf_*`, `G' = Rf'_*`, `Ψ_X = πZ^*`, `Ψ_Y = πP^*`, the proper base change isomorphism as
exchange, the counits as traces and `β(N)`, `𝟙` as dualizing maps) shows that `Rf'_* β(N)` is
invertible as soon as `πP^* RHom(Rf_* ℚ̄_ℓ, N) ⟶ RHom(πP^* Rf_* ℚ̄_ℓ, πP^* N)` is
(`ProEtale.CondensedRing.isIso_lowerStar_map_upperShriekBaseChangeOfMap_app`). This holds for
weakly étale `πP` (`ProEtale.CondensedRing.isIso_nearbyDualityMap_upperStarOfMap_id_of_weaklyEtale`,
from `ProEtale.CondensedRing.isIso_ihomComparison_leftDerivedUpperStar_of_weaklyEtale`) and for any
morphism of points, every complex on a point being dualizable
(`ProEtale.CondensedRing.isIso_nearbyDualityMap_upperStarOfMap_id_point`,
`CategoryTheory.Verdier.isIso_ihomComparison_app_of_exactPairing`).

*An abstract isomorphism.* For `f` smooth of pure relative dimension `d`,
`πZ^* Rf^! N ≅ πZ^* (f^* N ⊗ ℚ̄_ℓ(d)[2d]) ≅ f'^* πP^* N ⊗ ℚ̄_ℓ(d)[2d] ≅ Rf'^! πP^* N`
(`ProEtale.CondensedRing.upperShriekBaseChangeIsoOfSmooth`), by the purity tensor maps
(`ProEtale.CondensedRing.isIso_upperShriekUnitTensorMap_of_smooth`), smooth purity
(`ProEtale.CondensedRing.isIso_smoothPurityMap`, a sorried input of the smooth purity section) and
the pullback of the Tate twists.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Verdier

open Functor.LaxMonoidal

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]
  {C' : Type*} [Category* C'] [MonoidalCategory C'] [MonoidalClosed C']

end CategoryTheory.Verdier

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- `Dᵇc` is monoidal through `ObjectProperty.fullMonoidalSubcategory` everywhere, so that the
-- monoidal structures of concrete statements and of instantiated abstract ones agree syntactically.
attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

set_option hygiene false in
/-- The coefficient ring `ℚ̲̄_ℓ`. -/
local notation "𝐐" => Profinite.padicAlgClRingObj.{u} ℓ

section Verdier

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {Z P : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom]
  [IsSeparated P.hom]

end Verdier

section GlobalSections

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)]
  {Z P : Over (Spec (.of k₁))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  {Z' P' : Over (Spec (.of k₂))} [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom]
  [IsSeparated Z'.hom] [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  {f : Z ⟶ P} {f' : Z' ⟶ P'} [IsProper f.left] [IsProper f'.left]
  {πP : P'.left ⟶ P.left} {πZ : Z'.left ⟶ Z.left}

end GlobalSections

section PullbackIhom

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)]

end PullbackIhom

section Smooth

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)]
  {Z P : Over (Spec (.of k₁))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  {Z' P' : Over (Spec (.of k₂))} [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom]
  [IsSeparated Z'.hom] [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  {πP : P'.left ⟶ P.left} {πZ : Z'.left ⟶ Z.left}

end Smooth

section Main

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)]
  {Z P : Over (Spec (.of k₁))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  {Z' P' : Over (Spec (.of k₂))} [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom]
  [IsSeparated Z'.hom] [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  {f : Z ⟶ P} {f' : Z' ⟶ P'} [IsProper f.left] [IsProper f'.left]
  {πP : P'.left ⟶ P.left} {πZ : Z'.left ⟶ Z.left}

end Main

section Point

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)]
  {Z : Over (Spec (.of k₁))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  {Z' : Over (Spec (.of k₂))} [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom]
  [IsSeparated Z'.hom] {f : Z ⟶ point k₁} {f' : Z' ⟶ point k₂} [IsProper f.left]
  [IsProper f'.left] {πₛ : Spec (.of k₂) ⟶ Spec (.of k₁)} {πZ : Z'.left ⟶ Z.left}

end Point

section Projective

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)]
  {Z P : Over (Spec (.of k₁))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  {Z' P' : Over (Spec (.of k₂))} [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom]
  [IsSeparated Z'.hom] [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  {f : Z ⟶ P} {f' : Z' ⟶ P'} [IsProper f.left] [IsProper f'.left]
  {πP : P'.left ⟶ P.left} {πZ : Z'.left ⟶ Z.left}

end Projective

end AlgebraicGeometry.ProEtale.CondensedRing
