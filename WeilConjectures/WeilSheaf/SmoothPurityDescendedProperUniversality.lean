/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityProperTraceCoordinates
public import WeilConjectures.WeilSheaf.SmoothPurityCondensedCarrier

/-!
# Universality of the geometric carrier of a descended proper trace

The descent comparison identifies this carrier with ordinary proper base
change. Thus invertibility of exceptional base change proves its universal
property on bounded constructible geometric complexes.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [Finite k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) [IsProper f.left]

local instance : Fact (ringChar (AlgebraicClosure k)).Prime :=
  ⟨CharP.prime_ringChar (AlgebraicClosure k)⟩
local instance : Fact (ringChar (AlgebraicClosure k) ≠ l) :=
  ⟨ringChar_algebraicClosure_ne (k₀ := k) (l := l)⟩

/-- The geometric fibre of an arrow, viewed over the algebraic closure. -/
noncomputable abbrev traceGeometricFiberOverMap :
    Over.mk X.hom.geometricFiberToAlgebraicClosure ⟶
      Over.mk Y.hom.geometricFiberToAlgebraicClosure :=
  Over.homMk (Scheme.Hom.geometricFiberMap f.left (Over.w f)) (by
    simp [Scheme.Hom.geometricFiberToAlgebraicClosure, Scheme.Hom.geometricFiberMap])

local instance : LocallyOfFiniteType (Over.mk X.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
local instance : QuasiCompact (Over.mk X.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (QuasiCompact (pullback.snd _ _))
local instance : IsSeparated (Over.mk X.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (IsSeparated (pullback.snd _ _))
local instance : LocallyOfFiniteType (Over.mk Y.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
local instance : QuasiCompact (Over.mk Y.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (QuasiCompact (pullback.snd _ _))
local instance : IsSeparated (Over.mk Y.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (IsSeparated (pullback.snd _ _))
local instance : IsProper (traceGeometricFiberOverMap f).left :=
  Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsProper)
    f.left (Over.w f) inferInstance

variable (hc : UpperStarWeilCompatible (Profinite.padicAlgClRingObj l) f.left (Over.w f))
  {P : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj l⟧}
  {N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj l⟧}
  (γ : P ⟶ (boundedConstructibleUpperShriek l f).obj N)

/-- The actual descended trace is geometrically universal for a smooth proper map. -/
theorem bijective_map_comp_geometricFiberWeilDirectTrace [IsIso γ]
    (d : ℕ) [SmoothOfRelativeDimension d f.left]
    (K : Dᵇc(X.hom.geometricFiber)⟦Profinite.padicAlgClRingObj l⟧) :
    Function.Bijective fun φ : K.obj ⟶
        (Endofunctor.IsoAlgebra.forget _).mapDerivedCategory.obj
          ((geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l) X.hom).
            mapDerivedCategory.obj P.obj) ↦
      (lowerStar (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap f.left (Over.w f))).rightDerivedFunctor.map φ ≫
      (Endofunctor.IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso _
        (lowerStarGeometricFiberMapCompFrobeniusIso (Profinite.padicAlgClRingObj l)
          f.left (Over.w f))).inv.app
            ((geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l) X.hom).
              mapDerivedCategory.obj P.obj) ≫
      (Endofunctor.IsoAlgebra.forget _).mapDerivedCategory.map
        (geometricFiberWeilDirectTrace (Profinite.padicAlgClRingObj l) hc
          (((boundedConstructibleLowerStar l f).map γ ≫
            (lowerStarUpperShriekAdjunction l f).counit.app N).hom)) := by
  simp_rw [geometricFiberWeilDirectTrace_forget]
  exact Functor.bijective_map_comp_iso_trace _
    ((Functor.mapDerivedCategoryCompIso
      (geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l) X.hom)
      (Endofunctor.IsoAlgebra.forget _)).symm.app P.obj)
    ((Functor.mapDerivedCategoryCompIso
      (geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l) Y.hom)
      (Endofunctor.IsoAlgebra.forget _)).app N.obj) _
    (bijective_map_comp_properTrace_levelwise l f (traceGeometricFiberOverMap f)
      (Scheme.Hom.isPullback_geometricFiberMap f.left (Over.w f)).flip γ d K)

end AlgebraicGeometry.ProEtale.CondensedRing
