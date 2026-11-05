/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangePoint
public import WeilConjectures.PoincareDuality.Biduality.Constructible
public import WeilConjectures.CategoryTheory.Monoidal.Closed.ExceptionalHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.SmoothProjection

/-!
# The relative A1' for the proper part: `πZ^* Rp^! ℚ̄_ℓ ≅ Rp̄^! ℚ̄_ℓ` by Verdier duality

Let `k` be a finite field with algebraic closure `k̄`, and `f : X ⟶ Y` a morphism of separated
`k`-schemes of finite type, with geometric fibre `f̄ : X̄ ⟶ Ȳ`. We build **an** isomorphism of
bounded constructible `ℚ̄_ℓ`-complexes `πX^* Rf^! ℚ̄_ℓ ≅ Rf̄^! ℚ̄_ℓ`
(`geometricFiberUpperShriekUnitIso`), by Verdier duality, following Houyi's reduction of the
relative case to the point case:

1. `Rf^! ℚ̄_ℓ ≅ Rf^! RHom(ω_Y, ω_Y) ≅ RHom(f^* ω_Y, Rf^! ω_Y) ≅ RHom(f^* ω_Y, ω_X)`, by biduality
   at the unit (`isIso_verdierBiduality`), the exceptional internal hom exchange
   `RHom(f^* M, Rf^! N) ≅ Rf^! RHom(M, N)` (`CategoryTheory.Verdier.exceptionalHomMap`) and
   `Rf^! ω_Y ≅ ω_X` (`upperShriekDualizingComplexIso`);
2. `πX^* RHom(A, ω_X) ≅ RHom(πX^* A, ω_X̄)`: weakly étale pullback commutes with internal homs
   (`isIso_nearbyDualityMap_upperStarOfMap_id_of_weaklyEtale`) and `πX^* ω_X ≅ ω_X̄` is the point
   case `isIso_smoothUnitBaseChange_geometricFiberLowerShriekBaseChangePoint` (A1' over a point,
   for the structure morphism of `X`);
3. `πX^* f^* ω_Y ≅ f̄^* πY^* ω_Y ≅ f̄^* ω_Ȳ`, by the point case for `Y`;
4. step 1 backwards on `X̄ ⟶ Ȳ`.

No smoothness or properness of `f` is used. For `p` **proper**, the **endomorphism trick**
`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_of_iso` turns the existence of
such an isomorphism into the invertibility of the canonical base change map
`πZ^* Rp^! ℚ̄_ℓ ⟶ Rp̄^! πP^* ℚ̄_ℓ` of `Rp^!` at the unit
(`isIso_upperShriekBaseChangeOfMap_app_unit_of_iso`, for any proper `p` in a cartesian square
over a weakly étale `πP`, and `isIso_upperShriekBaseChangeOfMap_app_unit_geometricFiber` for the
geometric fibre). The relative Nagata pasting is in
`WeilConjectures.WeilSheaf.SmoothPurityVerdierUnitBaseChangeRelative`.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

/-! ### The absolute part: `Rf^! ℚ̄_ℓ ≅ RHom(f^* ω_Y, ω_X)`, over any field -/

section Absolute

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

variable (f : X ⟶ Y)

end Absolute

/-! ### Pullbacks commute with pullbacks across fields (no open-immersion hypothesis) -/

section Square

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ ℓ)]
  {X Y : Over (Spec (.of k₁))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  (f : X ⟶ Y) (f' : X' ⟶ Y') {πX : X'.left ⟶ X.left} {πY : Y'.left ⟶ Y.left}

end Square

/-! ### Pullbacks across the base field `k ⟶ k̄` -/

section GeometricFiber

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Finite k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

variable (X : Over (Spec (.of k)))
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

variable {X} {Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

end GeometricFiber

/-! ### The endomorphism trick for a proper morphism -/

section Trick

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ ℓ)]
  {Z P : Over (Spec (.of k₁))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  {Z' P' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  {p : Z ⟶ P} {p' : Z' ⟶ P'} [IsProper p.left] [IsProper p'.left]
  {πP : P'.left ⟶ P.left} {πZ : Z'.left ⟶ Z.left}

end Trick

end AlgebraicGeometry.ProEtale.CondensedRing
