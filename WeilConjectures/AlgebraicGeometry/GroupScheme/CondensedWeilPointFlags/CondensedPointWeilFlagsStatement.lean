/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfFinitelyPresented.FiberRank
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.IntrinsicCondensedCoefficientPoint

/-! # Full flags of actual condensed Weil modules at a point

Source: latest blueprint, sec-deligne-laumon-general/sk-i-dl-general-real/
thm-zl-real-mixed-by-curves.proof.md, paragraph 7
(blueprint: lem-zl-condensed-point-weil-flags).

The matrix entries use actual point sections, with the existing scalar normalization.
The quotients belong to the native Weil-module category and use its recorded purity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedWeilPointFlags

/-- The ground-field point with its identity structure map.
Source: latest blueprint, paragraph 7 (blueprint: lem-zl-condensed-point-weil-flags). -/
abbrev pointModel (D : FiniteFieldDatum.{u}) : Over (Spec (.of D.k₀)) :=
  Over.mk (𝟙 (Spec (.of D.k₀)))

/-- The geometric base change of the point.
Source: latest blueprint, paragraph 7 (blueprint: lem-zl-condensed-point-weil-flags). -/
abbrev pointSpace (D : FiniteFieldDatum.{u}) := (D.geometricFiber (pointModel D)).left

/-- The inverse of the canonical projection identifying the base change with Spec k.
Source: latest blueprint, paragraph 7 (blueprint: lem-zl-condensed-point-weil-flags). -/
def pointLift (D : FiniteFieldDatum.{u}) : Spec (.of D.k) ⟶ pointSpace D :=
  inv (pullback.snd (𝟙 (Spec (.of D.k₀)))
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))

/-- Finite powers of the actual pulled-back coefficient module.
Source: latest blueprint, paragraph 7 (blueprint: lem-zl-condensed-point-weil-flags). -/
abbrev free (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (n : ℕ) :=
  Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj l) (pointSpace D)) n

/-- Entries of a finite-free sheaf map, evaluated on Spec k and in scalar coordinates.
The inverse unit-section isomorphism removes the standard universe lift.
Source: latest blueprint, paragraph 7 (blueprint: lem-zl-condensed-point-weil-flags). -/
def matrix (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] {a b : ℕ}
    (f : free D l a ⟶ free D l b) : Matrix (Fin b) (Fin a) (PadicAlgCl l) :=
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  fun i j ↦
    ((NativeCondensedModule.pointSectionsUnitIso l D.k).inv.hom
      ((NativeCondensedModule.pointSections l D.k).map
        (CondensedRing.restrictEnd (Profinite.padicAlgClRingObj l) (pointLift D)
          (Mod.finFreeEntry f i j)) (NativeCondensedModule.pointSectionsUnit l D.k))).down

/-- The matrix of the specified Weil isomorphism in a global basis, using the canonical
comparison of inverse image of a free module with that free module.
Source: latest blueprint, paragraph 7 (blueprint: lem-zl-condensed-point-weil-flags). -/
def frobeniusMatrix (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (M : NativeL2.WeilModule D l (pointModel D)) {n : ℕ}
    (e : M.carrier ≅ free D l n) : Matrix (Fin n) (Fin n) (PadicAlgCl l) :=
  matrix D l ((CondensedRing.upperStarFiniteFreeIso (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius (pointModel D)).hom n).inv ≫
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius (pointModel D)).hom).map e.inv ≫ M.str.hom ≫ e.hom)

end WeilConjectures.CondensedWeilPointFlags
