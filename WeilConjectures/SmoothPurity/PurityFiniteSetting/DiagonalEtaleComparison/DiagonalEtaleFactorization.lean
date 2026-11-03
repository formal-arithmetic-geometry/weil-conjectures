/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalEtaleComparison.DiagonalEtaleSourceTransport
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionRestrictionData
import all WeilConjectures.AlgebraicGeometry.ChartNormalDifferential.ChartNormalDifferential

/-! # A Cartesian-centre span for an etale diagonal map

Source: diagonal-dualizing proof Step 1; orientation-charts proof Steps 1--3.
(blueprint: lem-pur-diagonal-etale-cartesian-centre-span).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting.DiagonalEtaleComparison
open SectionRestriction

/-- The actual self-product diagonal as a smooth section pair.
Source: diagonal-dualizing Step 1
(blueprint: lem-pur-diagonal-etale-cartesian-centre-span). -/
def diagonalPair {X Y : Scheme.{u}} (d : ℕ) (g : X ⟶ Y)
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g] : Pair X d :=
  ⟨_, pullback.fst g g, pullback.diagonal g, inferInstance, inferInstance,
    inferInstance, inferInstance, pullback.diagonal_fst _⟩

/-- Pull back the diagonal pair along e, without choosing a neighbourhood.
Source: orientation-charts Step 1
(blueprint: lem-pur-diagonal-etale-cartesian-centre-span). -/
def basePair {U X Y : Scheme.{u}} (d : ℕ) (g : X ⟶ Y)
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g] (e : U ⟶ X) : Pair U d :=
  letI : IsClosedImmersion (Scheme.Hom.baseChangeSection (pullback.fst g g)
      (pullback.diagonal g) (pullback.diagonal_fst _) e) :=
    MorphismProperty.of_isPullback
      (Scheme.Hom.isPullback_baseChangeSection (pullback.fst g g)
        (pullback.diagonal g) (pullback.diagonal_fst _) e).flip inferInstance
  ⟨_, pullback.snd (pullback.fst g g) e,
    Scheme.Hom.baseChangeSection (pullback.fst g g) (pullback.diagonal g)
      (pullback.diagonal_fst _) e,
    inferInstance, inferInstance, inferInstance, inferInstance,
    Scheme.Hom.baseChangeSection_snd _ _ _ _⟩

/-- The actual base-change square, with its specified section.
Source: orientation-charts Step 1
(blueprint: lem-pur-diagonal-etale-cartesian-centre-span). -/
def baseSquare {U X Y : Scheme.{u}} (d : ℕ) (g : X ⟶ Y)
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g] (e : U ⟶ X) :
    BaseChange e (basePair d g e) (diagonalPair d g) :=
  ⟨pullback.fst (pullback.fst g g) e, IsPullback.of_hasPullback _ _,
    Scheme.Hom.baseChangeSection_fst (pullback.fst g g) (pullback.diagonal g)
      (pullback.diagonal_fst _) e⟩

/-- A common etale neighbourhood of the two section pairs. Both arrows have
Cartesian centre squares. The last equation fixes the ambient map, so it also
fixes the induced Rees and normal maps; no endpoint comparison is assumed.
Source: orientation-charts Steps 1--3
(blueprint: lem-pur-diagonal-etale-cartesian-centre-span). -/
structure CentreSpan {U X Y : Scheme.{u}} (d : ℕ) (g : X ⟶ Y)
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g]
    (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h] (e : U ⟶ X) (w : e ≫ g = h) where
  pair : Pair U d
  left : EtaleMap pair (diagonalPair d h)
  right : EtaleMap pair (basePair d g e)
  factorization : left.map ≫ sourceLift d g h e w = right.map

/-- The complement of the off-diagonal sheets supplies a common neighbourhood.
Source: diagonal-dualizing Step 1; orientation-charts Steps 1--3.
Proof: remove the closed off-diagonal part of U times_X U from U times_Y U,
using that the diagonal of e is clopen. The diagonal factors through the resulting
open. Its inclusion gives the left map. Compose this inclusion with sourceLift
for the right map. The centre square for the composite to X times_Y X is Cartesian;
cancel the Cartesian base-change square to obtain the right centre square. Both
maps are etale, and separatedness and quasi-compactness follow from their composites
with the separated quasi-compact projections. The empty open and rank zero obey
the same pullback argument.
(blueprint: lem-pur-diagonal-etale-cartesian-centre-span). -/
theorem centreSpan_nonempty {U X Y : Scheme.{u}} [IsNoetherian U]
    (d : ℕ) (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g]
    (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h] (e : U ⟶ X) [Etale e] (w : e ≫ g = h) :
    Nonempty (CentreSpan d g h e w) := by
  subst h
  obtain ⟨O, δ, _, hδ, hcart, het, hclosed⟩ := ChartNormalDifferential.chartGeometry g e
  let : IsClosedImmersion δ := hclosed
  let p := pullback.fst (e ≫ g) (e ≫ g)
  let m := selfMap d g (e ≫ g) e rfl
  have hδp : δ ≫ (O.ι ≫ p) = 𝟙 U := by
    rw [← Category.assoc, hδ]
    exact pullback.diagonal_fst _
  let := SmoothOfRelativeDimension.smooth d p
  let : IsLocallyNoetherian (pullback (e ≫ g) (e ≫ g)) :=
    LocallyOfFiniteType.isLocallyNoetherian p
  let : IsNoetherian (pullback (e ≫ g) (e ≫ g)) :=
    ⟨⟩
  let : SmoothOfRelativeDimension 0 O.ι :=
    (Etale.iff_smoothOfRelativeDimension_zero O.ι).mp inferInstance
  have hd : SmoothOfRelativeDimension (0 + d) (O.ι ≫ p) := inferInstance
  have : SmoothOfRelativeDimension d (O.ι ≫ p) := by simpa only [Nat.zero_add] using hd
  let R : Pair U d :=
    ⟨O.toScheme, O.ι ≫ p, δ, inferInstance, inferInstance,
      inferInstance, inferInstance, hδp⟩
  have hr : IsPullback δ (𝟙 U) O.ι (pullback.diagonal (e ≫ g)) :=
    IsPullback.of_vert_isIso_mono ⟨by simpa using hδ⟩
  have hgeom := sourceLift_geometry d g (e ≫ g) e rfl
  let := hgeom.1
  let := hgeom.2.1
  let := hgeom.2.2.1
  let b := O.ι ≫ sourceLift d g (e ≫ g) e rfl
  have hb : b ≫ (basePair d g e).g = R.g := by
    simp only [b, basePair, sourceLift, Category.assoc, pullback.lift_snd, R, p]
  have hbs : δ ≫ b = (basePair d g e).s := by
    dsimp only [b]
    rw [← Category.assoc, hδ]
    exact hgeom.2.2.2
  have hbottom : IsPullback (basePair d g e).s e
      (baseSquare d g e).map (pullback.diagonal g) :=
    Scheme.Hom.isPullback_baseChangeSection (pullback.fst g g)
      (pullback.diagonal g) (pullback.diagonal_fst _) e
  have hbc : b ≫ (baseSquare d g e).map = O.ι ≫ m := by
    simp only [b, baseSquare, sourceLift, Category.assoc, pullback.lift_fst, m]
  have hcentres : IsPullback δ (𝟙 U) b (basePair d g e).s := by
    apply IsPullback.of_bot (t := hbottom) ?_ hbs
    simpa only [Category.id_comp, hbc, m, selfMap] using hcart
  exact ⟨⟨R,
    ⟨O.ι, inferInstance, inferInstance, inferInstance, rfl, hδ, hr⟩,
    ⟨b, inferInstance, inferInstance, inferInstance, hb, hbs, hcentres⟩, rfl⟩⟩

end WeilConjectures.PurityFiniteSetting.DiagonalEtaleComparison
