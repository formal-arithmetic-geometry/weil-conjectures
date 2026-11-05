/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangeProper
public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangeGeometricFiber
public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangeEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.GenericPoint

/-!
# The exceptional base change at the unit through a compactification (A1' without charts)

Let `X` be a separated `k`-scheme of finite type with structure morphism `a : X ⟶ Spec k`, and
`X ⟶[j] X^c ⟶[p] Spec k` its chosen Nagata compactification (`compactificationOverField`). The
exceptional base change map at the unit of `a = j ≫ p` along the geometric fibre
`π : X̄ = X ×_k k̄ ⟶ X` is, by the pasting law `isIso_smoothUnitBaseChange_paste`, invertible as
soon as

* the exceptional base change map of the open immersion `j` is invertible at `Rp^! ℚ̄_ℓ`
  (`isIso_upperShriekMate_app_of_isOpenImmersion`, for a compact-support base change
  isomorphism `bcj` of `j` whose mate under `Rj_! ⊣ j^*` is the composition isomorphism of the
  pullbacks), and
* the exceptional base change map at the unit of the proper morphism `p` over the point is
  invertible: `isIso_smoothUnitBaseChange_of_proper_point`, from the library
  `isIso_upperShriekBaseChangeOfMap_app_unit_point` (the comparison of the dualizing complexes
  of a proper scheme across a field extension).

No chart, étale normal form or étale base change is needed:
`isIso_smoothUnitBaseChange_structureCompactification` proves
`IsIso (smoothUnitBaseChange l (j ≫ p) (j̄ ≫ p̄) (pasteLowerShriekBaseChange bcj bcp) e)` for
the pasted compact-support base change isomorphism, which is the restriction to bounded
constructible complexes of the ambient
`ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactificationBaseChangeIso`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Transport along equalities of morphisms -/

section Congr

variable (l : ℕ) [Fact l.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ l)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ l)]
  {X Y : Over (Spec (.of k₁))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {πX : X'.left ⟶ X.left} {πY : Y'.left ⟶ Y.left}

/-- Invertibility of the exceptional base change map at the unit is transported along
equalities of the morphisms. -/
theorem isIso_smoothUnitBaseChange_of_eq {f₁ f₂ : X ⟶ Y} (h : f₁ = f₂) {f₁' f₂' : X' ⟶ Y'}
    (h' : f₁' = f₂')
    (bc : boundedConstructibleLowerShriek l f₁ ⋙ boundedConstructibleUpperStarOfMap l πY ≅
      boundedConstructibleUpperStarOfMap l πX ⋙ boundedConstructibleLowerShriek l f₁')
    (e : (boundedConstructibleUpperStarOfMap l πY).obj (𝟙_ _) ⟶ 𝟙_ _)
    [IsIso (smoothUnitBaseChange l f₁ f₁' bc e)] :
    IsIso (smoothUnitBaseChange l f₂ f₂'
      (eqToIso (by rw [h]) ≪≫ bc ≪≫ eqToIso (by rw [h'])) e) := by
  subst h h'
  simpa

end Congr

/-! ### The proper piece over a point -/

section ProperPoint

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [Finite k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  {Z' P' : Over (Spec (.of (AlgebraicClosure k)))}
  [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  (f : Z ⟶ point k) (f' : Z' ⟶ P') [IsProper f.left] [IsProper f'.left]
  {πZ : Z'.left ⟶ Z.left} {πP : P'.left ⟶ (point k).left}
  (hP : IsPullback πP P'.hom (point k).hom
    (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))
  (sq : IsPullback πZ f'.left f.left πP)
  (e : (boundedConstructibleUpperStarOfMap l πP).obj (𝟙_ _) ⟶ 𝟙_ _) [IsIso e]

/-- **The proper piece over a point**: for a proper `k`-scheme `Z` and its base change to `k̄`,
the exceptional base change map at the unit is invertible
(`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_unit_point`). -/
theorem isIso_smoothUnitBaseChange_of_proper_point :
    IsIso (smoothUnitBaseChange l f f' (properLowerShriekBaseChangeOfMap l f f' sq) e) :=
  haveI := isIso_upperShriekBaseChangeOfMap_app_unit_point l hP sq
  isIso_smoothUnitBaseChange_of_isIso_upperShriekBaseChangeOfMap l f f' sq e

end ProperPoint

/-! ### Assembly through the chosen compactification -/

section Compactification

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [Finite k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The chosen compactification `X ⟶[j] X^c ⟶[p] Spec k` of the structure morphism of `X`. -/
noncomputable abbrev structureCompactification : Compactification (toPoint X).left :=
  compactificationOverField (toPoint X)

/-- The defining square of the geometric fibre of the point is cartesian. -/
lemma isPullback_point_geometricFiber :
    IsPullback (point k).hom.geometricFiberProj (geometricFiberOver (point k)).hom (point k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))) :=
  IsPullback.of_hasPullback _ _

variable {X}

/-- **The exceptional base change map at the unit through the chosen compactification**: for
`X ⟶[j] X^c ⟶[p] Spec k` the chosen compactification of the structure morphism of `X` and a
compact-support base change isomorphism `bcj` of `j` along the geometric fibre whose mate under
`Rj_! ⊣ j^*` is the composition isomorphism of the pullbacks, the exceptional base change map at
the unit of `j ≫ p`, for the pasted compact-support base change isomorphism of `bcj` and of the
proper base change of `p`, is invertible. -/
theorem isIso_smoothUnitBaseChange_structureCompactification
    (bcj : boundedConstructibleLowerShriek l (structureCompactification X).overI ⋙
        boundedConstructibleUpperStarOfMap l
          (structureCompactification X).overObj.hom.geometricFiberProj ≅
      boundedConstructibleUpperStarOfMap l X.hom.geometricFiberProj ⋙
        boundedConstructibleLowerShriek l (geometricFiberOverMap (structureCompactification X).overI))
    (hEx : (mateEquiv
        (boundedConstructibleOpenImmersionUpperStarAdjunction l (structureCompactification X).overI)
        (boundedConstructibleOpenImmersionUpperStarAdjunction l
          (geometricFiberOverMap (structureCompactification X).overI)) (inv bcj.hom)).natTrans =
      (upperStarOfMapSquareIso l (structureCompactification X).overI
        (geometricFiberOverMap (structureCompactification X).overI)
        (isPullback_geometricFiberOverMap (structureCompactification X).overI).w).hom)
    (e : (boundedConstructibleUpperStarOfMap l (point k).hom.geometricFiberProj).obj (𝟙_ _) ⟶
      𝟙_ _) [IsIso e] :
    IsIso (smoothUnitBaseChange l
      ((structureCompactification X).overI ≫ (structureCompactification X).overG)
      (geometricFiberOverMap (structureCompactification X).overI ≫
        geometricFiberOverMap (structureCompactification X).overG)
      (pasteLowerShriekBaseChange l (structureCompactification X).overI
        (structureCompactification X).overG _ _ bcj
        (properLowerShriekBaseChangeOfMap l (structureCompactification X).overG
          (geometricFiberOverMap (structureCompactification X).overG)
          (isPullback_geometricFiberOverMap (structureCompactification X).overG))) e) := by
  haveI := isIso_upperShriekMate_app_of_isOpenImmersion l (structureCompactification X).overI
    (geometricFiberOverMap (structureCompactification X).overI) bcj
    (isPullback_geometricFiberOverMap (structureCompactification X).overI).w hEx
    ((boundedConstructibleUpperShriek l (structureCompactification X).overG).obj (𝟙_ _))
  haveI := isIso_smoothUnitBaseChange_of_proper_point l (structureCompactification X).overG
    (geometricFiberOverMap (structureCompactification X).overG) (isPullback_point_geometricFiber X)
    (isPullback_geometricFiberOverMap (structureCompactification X).overG) e
  exact isIso_smoothUnitBaseChange_paste l (structureCompactification X).overI
    (structureCompactification X).overG _ _ bcj _ e

/-- **The compact-support base change isomorphism of the structure morphism through the chosen
compactification**: for `X ⟶[j] X^c ⟶[p] Spec k` the chosen compactification of `a_X = toPoint X`
and `bcj` a compact-support base change isomorphism of `j` along the geometric fibre, the pasted
isomorphism `R(a_X)_! ⋙ π_s^* ≅ π_X^* ⋙ R(ā_X)_!`, transported along `j ≫ p = a_X`. This is the
`bc` that the bridge to the ambient `rightDerivedLowerShriekGeometricFiberIso` has to match. -/
noncomputable def compactificationLowerShriekBaseChange
    (bcj : boundedConstructibleLowerShriek l (structureCompactification X).overI ⋙
        boundedConstructibleUpperStarOfMap l
          (structureCompactification X).overObj.hom.geometricFiberProj ≅
      boundedConstructibleUpperStarOfMap l X.hom.geometricFiberProj ⋙
        boundedConstructibleLowerShriek l (geometricFiberOverMap (structureCompactification X).overI)) :
    boundedConstructibleLowerShriek l (toPoint X) ⋙
        boundedConstructibleUpperStarOfMap l (point k).hom.geometricFiberProj ≅
      boundedConstructibleUpperStarOfMap l X.hom.geometricFiberProj ⋙
        boundedConstructibleLowerShriek l (geometricFiberOverMap (toPoint X)) :=
  eqToIso (by rw [(structureCompactification X).overI_overG]) ≪≫
    pasteLowerShriekBaseChange l (structureCompactification X).overI
      (structureCompactification X).overG _ _ bcj
      (properLowerShriekBaseChangeOfMap l (structureCompactification X).overG
        (geometricFiberOverMap (structureCompactification X).overG)
        (isPullback_geometricFiberOverMap (structureCompactification X).overG)) ≪≫
    eqToIso (by rw [← geometricFiberOverMap_comp, (structureCompactification X).overI_overG])

/-- **A1' over a point through the chosen compactification**: the exceptional base change map
at the unit of the structure morphism `a_X : X ⟶ Spec k` along the geometric fibre is invertible
for the pasted compact-support base change isomorphism `compactificationLowerShriekBaseChange`.
The only input is `bcj` with `hEx` (the open-immersion compact-support base change on bounded
constructible complexes and its mate). -/
theorem isIso_smoothUnitBaseChange_toPoint
    (bcj : boundedConstructibleLowerShriek l (structureCompactification X).overI ⋙
        boundedConstructibleUpperStarOfMap l
          (structureCompactification X).overObj.hom.geometricFiberProj ≅
      boundedConstructibleUpperStarOfMap l X.hom.geometricFiberProj ⋙
        boundedConstructibleLowerShriek l (geometricFiberOverMap (structureCompactification X).overI))
    (hEx : (mateEquiv
        (boundedConstructibleOpenImmersionUpperStarAdjunction l (structureCompactification X).overI)
        (boundedConstructibleOpenImmersionUpperStarAdjunction l
          (geometricFiberOverMap (structureCompactification X).overI)) (inv bcj.hom)).natTrans =
      (upperStarOfMapSquareIso l (structureCompactification X).overI
        (geometricFiberOverMap (structureCompactification X).overI)
        (isPullback_geometricFiberOverMap (structureCompactification X).overI).w).hom)
    (e : (boundedConstructibleUpperStarOfMap l (point k).hom.geometricFiberProj).obj (𝟙_ _) ⟶
      𝟙_ _) [IsIso e] :
    IsIso (smoothUnitBaseChange l (toPoint X) (geometricFiberOverMap (toPoint X))
      (compactificationLowerShriekBaseChange l bcj) e) := by
  haveI := isIso_smoothUnitBaseChange_structureCompactification l bcj hEx e
  exact isIso_smoothUnitBaseChange_of_eq l (structureCompactification X).overI_overG
    (by rw [← geometricFiberOverMap_comp, (structureCompactification X).overI_overG]) _ e

end Compactification

end AlgebraicGeometry.ProEtale.CondensedRing
