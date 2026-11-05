/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangeGeometricFiber
public import WeilConjectures.WeilSheaf.SmoothUnitBaseChangeOpenImmersion
public import WeilConjectures.WeilSheaf.CondensedModelBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.GenericPoint

/-!
# The exceptional base change map at the unit over a point, through Nagata (A1')

Let `k` be a finite field with algebraic closure `k̄`, and `f : X ⟶ Spec k` a separated `k`-scheme
of finite type, with geometric fibre `f̄ : X̄ ⟶ Spec k̄` (`geometricFiberOverMap f`). Factor `f`
through the compactification `X --j--> X^c --p--> Spec k` defining `Rf_!`
(`compactificationOverField f`): `j` is an open immersion and `p` is proper. For any
compact-support base change isomorphism `bcj` of `j` along `X̄^c ⟶ X^c`, the pasting of `bcj`
with proper base change for `p` (`nagataLowerShriekBaseChange`) is a compact-support base change
isomorphism for `f`, and its exceptional base change map at the unit
`πX^* Rf^! ℚ̄_ℓ ⟶ Rf̄^! ℚ̄_ℓ` is invertible
(`ProEtale.CondensedRing.isIso_smoothUnitBaseChange_nagataLowerShriekBaseChange`).

## Proof

By the pasting law (`isIso_smoothUnitBaseChange_paste`) it is enough that

* the exceptional base change map at the unit of `p` is invertible: this is
  `ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_unit_point` for the proper
  `k`-scheme `X^c` (no smoothness is needed);
* the mate `πX^* Rj^! N ⟶ Rj̄^! πX^c^* N` of `bcj` is invertible at `N = Rp^! ℚ̄_ℓ`: for an open
  immersion this holds for **every** `N` and **every** base change isomorphism
  (`isIso_upperShriekMateOfMap_app_of_isOpenImmersion'`), since the units of `Rj_! ⊣ Rj^!` and
  `Rj̄_! ⊣ Rj̄^!` are invertible (`CategoryTheory.Adjunction.isIso_mateEquiv_app_of_isIso_unit`).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
  {a : C ⥤ D} {a' : D ⥤ C} (adj : a ⊣ a') {b : C' ⥤ D'} {b' : D' ⥤ C'} (adj' : b ⊣ b')
  {G : C ⥤ C'} {H : D ⥤ D'} (bc : a ⋙ H ⟶ G ⋙ b) [IsIso bc]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section OpenImmersion

variable (l : ℕ) [Fact l.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ l)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ l)]
  {U V : Over (Spec (.of k₁))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
  {U' V' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom] [IsSeparated U'.hom]
  [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
  (j : U ⟶ V) (j' : U' ⟶ V') [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
  {πU : U'.left ⟶ U.left} {πV : V'.left ⟶ V.left}
  (bc : boundedConstructibleLowerShriek l j ⋙ boundedConstructibleUpperStarOfMap l πV ≅
    boundedConstructibleUpperStarOfMap l πU ⋙ boundedConstructibleLowerShriek l j')

end OpenImmersion

section OpenImmersionBaseChange

variable (l : ℕ) [Fact l.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ l)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ l)]
  {U V : Over (Spec (.of k₁))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
  {U' V' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom] [IsSeparated U'.hom]
  [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
  {j : U ⟶ V} {j' : U' ⟶ V'} [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
  {πU : U'.left ⟶ U.left} {πV : V'.left ⟶ V.left}

end OpenImmersionBaseChange

section Point

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [Finite k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (f : X ⟶ point k)

end Point

end AlgebraicGeometry.ProEtale.CondensedRing
