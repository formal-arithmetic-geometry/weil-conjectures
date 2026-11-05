/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek
public import WeilConjectures.WeilSheaf.SmoothPurityDescendedTraceUniversal

/-!
# The exceptional base change map at the unit for an open immersion

Let `j : U ⟶ V` be an open immersion of separated `k₁`-schemes of finite type and
`j' : U' ⟶ V'` an open immersion of separated `k₂`-schemes of finite type, together with maps
`πU : U' ⟶ U`, `πV : V' ⟶ V` such that `πU ≫ j = j' ≫ πV`. For **any** compact-support base change
isomorphism `bc : Rj_! ⋙ πV^* ≅ πU^* ⋙ Rj'_!` and any isomorphism `e : πV^* ℚ̄_ℓ ≅ ℚ̄_ℓ`, the
exceptional base change map at the unit `smoothUnitBaseChange : πU^* Rj^! ℚ̄_ℓ ⟶ Rj'^! ℚ̄_ℓ` is an
isomorphism (`ProEtale.CondensedRing.isIso_smoothUnitBaseChange_of_isOpenImmersion`).

This is the open-immersion piece of the compatibility of `Rf^!` with a change of the base field
for a smooth `f`, factored locally as an étale map to `𝔸^d_Y`, the open immersion `𝔸^d_Y ⊆ ℙ^d_Y`
and the projection `ℙ^d_Y ⟶ Y`.

## Proof

The formal input is `CategoryTheory.Adjunction.isIso_unitBaseChange_of_isIso_unit`: for
adjunctions `a ⊣ a'`, `b ⊣ b'` with invertible units (`a`, `b` fully faithful) and a natural
isomorphism `a' ⋙ G ≅ H ⋙ b'`, the map `unitBaseChange` attached to an invertible base change
morphism and an invertible `e` is invertible, whatever the base change morphism is. Indeed it is
`η'_{G a' U} ≫ b'(bc⁻¹) ≫ b' H (ε_U) ≫ b'(e)`, and `b' H (ε_U)` is conjugate to `G a' (ε_U)`,
which is invertible by the triangle identity.

For `Rj_! ⊣ Rj^!`, `Rj_! ≅ j_!` is the extension by zero
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl`),
which is fully faithful, and `Rj^! ≅ j^*`
(`ProEtale.CondensedRing.boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl`), so that
`Rj^! ⋙ πU^* ≅ j^* ⋙ πU^* ≅ πV^* ⋙ j'^* ≅ πV^* ⋙ Rj'^!` by the composition isomorphisms of the
derived pullbacks.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
  {a : C ⥤ D} {a' : D ⥤ C} (adj : a ⊣ a') {b : C' ⥤ D'} {b' : D' ⥤ C'} (adj' : b ⊣ b')
  {G : C ⥤ C'} {H : D ⥤ D'} (bc : a ⋙ H ⟶ G ⋙ b) [IsIso bc] {U : D} {U' : D'}
  (e : H.obj U ⟶ U')

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section OpenImmersion

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {U X : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left]

end OpenImmersion

section BaseChange

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

variable (bc : boundedConstructibleLowerShriek l j ⋙ boundedConstructibleUpperStarOfMap l πV ≅
    boundedConstructibleUpperStarOfMap l πU ⋙ boundedConstructibleLowerShriek l j')
  (e : (boundedConstructibleUpperStarOfMap l πV).obj (𝟙_ _) ⟶ 𝟙_ _)

end BaseChange

end AlgebraicGeometry.ProEtale.CondensedRing
