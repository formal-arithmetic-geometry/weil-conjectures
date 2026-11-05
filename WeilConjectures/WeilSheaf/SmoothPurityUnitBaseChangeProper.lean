/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangeComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.SmoothProjection

/-!
# The exceptional base change map at the unit for a proper morphism (A1', the proper piece)

For a proper `f : Z ⟶ P` over `k₁` and a cartesian square `πZ ≫ f = f' ≫ πP` over `k₂`, the
compact-support base change isomorphism `Rf_! ⋙ πP^* ≅ πZ^* ⋙ Rf'_!` is proper base change
read through `Rf_! ≅ Rf_*` (`properLowerShriekBaseChangeOfMap`), and the exceptional base change
map at the unit `ProEtale.CondensedRing.smoothUnitBaseChange` attached to it is the library's
`ProEtale.CondensedRing.upperShriekBaseChangeOfMap` at the unit followed by `Rf'^!(e)`
(`smoothUnitBaseChange_proper_eq`). Hence it is invertible for `f` smooth proper along a weakly
étale base change (`isIso_smoothUnitBaseChange_of_smooth_of_weaklyEtale`), in particular for the
projection of a projective space (`isIso_smoothUnitBaseChange_of_projectiveSpace_of_weaklyEtale`),
and for a smooth proper scheme over a point along any change of the base field
(`isIso_smoothUnitBaseChange_of_smooth_point`).

The generic statement is `CategoryTheory.Adjunction.unitBaseChange_ofNatIsoLeft`: `unitBaseChange`
is compatible with the transport of the adjunctions along isomorphisms of the left adjoints.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace CategoryTheory.Adjunction

section OfNatIsoLeft

variable {C C' D D' : Type*} [Category* C] [Category* C'] [Category* D] [Category* D']
  {a : C ⥤ D} {a' : D ⥤ C} (adj : a ⊣ a') {b : C' ⥤ D'} {b' : D' ⥤ C'} (adj' : b ⊣ b')
  {G : C ⥤ C'} {H : D ⥤ D'} {s : C ⥤ D} {s' : C' ⥤ D'} (ι : a ≅ s) (ι' : b ≅ s')
  (bcs : s ⋙ H ⟶ G ⋙ s') [IsIso bcs] {U : D} {U' : D'} (e : H.obj U ⟶ U')

end OfNatIsoLeft

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Proper

variable (l : ℕ) [Fact l.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ l)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ l)]
  {Z P : Over (Spec (.of k₁))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  {Z' P' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  (f : Z ⟶ P) (f' : Z' ⟶ P') [IsProper f.left] [IsProper f'.left]
  {πP : P'.left ⟶ P.left} {πZ : Z'.left ⟶ Z.left} (sqf : IsPullback πZ f'.left f.left πP)
  (e : (boundedConstructibleUpperStarOfMap l πP).obj (𝟙_ _) ⟶ 𝟙_ _)

end Proper

section Point

variable (l : ℕ) [Fact l.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ l)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ l)]
  {Z : Over (Spec (.of k₁))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  {Z' : Over (Spec (.of k₂))} [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom]
  [IsSeparated Z'.hom] (f : Z ⟶ point k₁) (f' : Z' ⟶ point k₂) [IsProper f.left]
  [IsProper f'.left] {πₛ : Spec (.of k₂) ⟶ Spec (.of k₁)} {πZ : Z'.left ⟶ Z.left}
  (sqf : IsPullback πZ f'.left f.left πₛ)
  (e : (boundedConstructibleUpperStarOfMap l (X := point k₁) (Y := point k₂) πₛ).obj (𝟙_ _) ⟶
    𝟙_ _)

end Point

end AlgebraicGeometry.ProEtale.CondensedRing
