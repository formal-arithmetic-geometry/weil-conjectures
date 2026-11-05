/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.ProperExceptionalForget
public import WeilConjectures.WeilSheaf.Native.Projection.ProperForgetNormalization
public import WeilConjectures.WeilSheaf.Native.Projection.CompactForgetComparison

/-! # The canonical proper forget square on bounded constructible complexes -/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits Endofunctor
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.WeilComplex

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (g : X ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))] [IsProper g]

local notation "gb" => geometricFiberHom (k₀ := k₀) g
local notation "EX" => boundedConstructibleAdicEquivBoundedConstructible l k₀
  (Over.mk (Scheme.Hom.geometricFiberToAlgebraicClosure (X ↘ Spec (CommRingCat.of k₀))))
local notation "EY" => boundedConstructibleAdicEquivBoundedConstructible l k₀
  (Over.mk (Scheme.Hom.geometricFiberToAlgebraicClosure (Y ↘ Spec (CommRingCat.of k₀))))

/-- The proper geometric comparison chosen as the derived mate of the pullback comparison. -/
def projectionBoundedAdicCondensedPushIso :
    properProjectionAdicPush k₀ l g ⋙ (EY).functor ≅
      (EX).functor ⋙ CondensedRing.boundedConstructibleLowerStar l gb :=
  NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    ((projectionAdicCondensedDerivedPushIso l (gb).left).app M.obj))
    (fun φ ↦ ObjectProperty.hom_ext _
      ((projectionAdicCondensedDerivedPushIso l (gb).left).hom.naturality φ.hom))

/-- The canonical proper forget comparison, expressed through the adic model. -/
def projectionProperForgetIso :
    derivedLowerStar g ⋙ compactProjectionForget k₀ l Y ≅
      compactProjectionForget k₀ l X ⋙ CondensedRing.boundedConstructibleLowerStar l gb :=
  (Functor.isoHComp (properProjectionAdicForgetIso k₀ l g).symm
    (projectionBoundedAdicCondensedPushIso k₀ l g).symm).symm

/-- Its exceptional mate is invertible for every choice of right adjoints. -/
theorem isIso_mateEquiv_projectionProperForgetIso
    {R : WeilComplex k₀ l Y ⥤ WeilComplex k₀ l X} (adj : derivedLowerStar g ⊣ R)
    {R' : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l)
        (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber) ⥤
      BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)}
    (adj' : CondensedRing.boundedConstructibleLowerStar l gb ⊣ R') :
    IsIso (mateEquiv adj adj' (projectionProperForgetIso k₀ l g).inv).natTrans := by
  let δ := projectionBoundedAdicCondensedPushIso k₀ l g
  let aa := ((EX).toAdjunction.comp (adj'.comp (EY).symm.toAdjunction)).ofNatIsoLeft
    δ.isoCompInverse.symm
  have h₁ : IsIso (mateEquiv adj aa (properProjectionAdicForgetIso k₀ l g).symm.hom).natTrans :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun M ↦
      isIso_mateEquiv_properProjectionAdicForgetIso k₀ l g adj aa M)
  have h₂ : IsIso (mateEquiv aa adj' δ.symm.hom).natTrans :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun M ↦
      Adjunction.isIso_mateEquiv_app_of_isIso aa adj' δ.symm
        (EX).toAdjunction (EY).toAdjunction M)
  exact isIso_mateEquiv_isoHComp adj aa adj'
    (properProjectionAdicForgetIso k₀ l g).symm δ.symm

end AlgebraicGeometry.WeilComplex
