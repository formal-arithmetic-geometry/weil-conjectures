/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryResolutionRule
public import Sheaf.AlgebraicGeometry.OrdinaryTowerCartesianMap
public import Sheaf.AlgebraicGeometry.NormalizedTowerDescentData
public import Sheaf.AlgebraicGeometry.RegularSchemeMorphism
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

import WeilConjectures.Blowup.InvertibleCenter
import WeilConjectures.Blowup.Proper
import WeilConjectures.RingTheory.JapaneseDomain
import WeilConjectures.RingTheory.NagataRing
import Sheaf.RingTheory.QuasiExcellentNagata
import Sheaf.AlgebraicGeometry.ComponentwiseNormalizationAffineCharts
import Sheaf.AlgebraicGeometry.NoetherianNormalizedBlowupFinality
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.RingTheory.FilteredColimitNormalRing
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.RingTheory.PopescuSmoothing
import WeilConjectures.RingTheory.SmoothNormalRing
import Mathlib.RingTheory.Smooth.Basic
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition

/-! # Normalization of centered towers and regular pullback

Source: ILO, Travaux de Gabber, VIII Proposition 2.2.4(ii), 2.2.6,
Lemma 2.2.9, Remark 2.3.3(i) and Remark 2.3.12(i), printed pp.90--94
(blueprint: lem-per-normalized-tower-regular-pullback).

All tower notions, blowups, componentwise normalizations and extended ideals are the
published ones. The auxiliary records specify comparisons without choosing their data
from existence theorems. Selective deletion allows additional unit stages to be retained.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A normalization of an ordinary centered tower. At level zero the comparison is an
isomorphism; at every positive level it is exactly the componentwise normalization map.
The arrow and ideal equations specify the normalized tower over the original tower.
Source: ILO VIII 2.2.4(ii), 2.2.6
(blueprint: lem-per-normalized-tower-regular-pullback). -/
structure OrdinaryTowerNormalization {X : Scheme.{u}} (A : OrdinaryBlowupTower X) where
  tower : Monoscheme.NormalizedTower.{u} A.length
  map : ∀ i, tower.level i ⟶ A.level i
  initial : IsIso (map 0)
  positive : ∀ i : Fin A.length,
    ∃ e : tower.level i.succ ≅ (A.level i.succ).reducedNormalization,
      e.hom ≫ (A.level i.succ).fromReducedNormalization = map i.succ
  arrows : ∀ i : Fin A.length,
    tower.arrow i ≫ map i.castSucc = map i.succ ≫
      A.transition i.castSucc i.succ (le_of_lt i.castSucc_lt_succ)
  centers : ∀ i : Fin A.length, tower.center i = (A.center i).comap (map i.castSucc)

namespace Monoscheme.NormalizedTower

/-- A selective deletion of unit-center isomorphisms. In contrast to
`Monoscheme.NormalizedContraction`, this need not delete every eligible stage: regular
pullback can create additional unit stages. A nonisomorphism normalization is never
eligible, even if its ideal is the unit ideal. The remaining centers keep their order.
Source: ILO VIII 2.3.4--2.3.5, 2.3.12(i)
(blueprint: lem-per-normalized-tower-regular-pullback). -/
structure UnitStageDeletion {n m : ℕ} (T : NormalizedTower.{u} n)
    (S : NormalizedTower.{u} m) where
  index : Fin (n + 1) →o Fin (m + 1)
  surjective : Function.Surjective index
  first : index 0 = 0
  last : index (Fin.last n) = Fin.last m
  iso : ∀ i, T.level i ≅ S.level (index i)
  adjacent : ∀ i : Fin n, index i.succ = index i.castSucc ∨
    ∃ k : Fin m, index i.castSucc = k.castSucc ∧ index i.succ = k.succ
  deleted : ∀ i : Fin n, index i.succ = index i.castSucc →
    T.center i = ⊤ ∧ IsIso (T.arrow i)
  deletedMap : ∀ (i : Fin n) (e : index i.succ = index i.castSucc),
    T.arrow i ≫ (iso i.castSucc).hom =
      (iso i.succ).hom ≫ eqToHom (congrArg S.level e)
  keptMap : ∀ (i : Fin n) (k : Fin m)
    (e₀ : index i.castSucc = k.castSucc) (e₁ : index i.succ = k.succ),
    T.arrow i ≫ (iso i.castSucc).hom =
      (iso i.succ).hom ≫ eqToHom (congrArg S.level e₁) ≫
        S.arrow k ≫ eqToHom (congrArg S.level e₀.symm)
  keptCenter : ∀ (i : Fin n) (k : Fin m)
    (e₀ : index i.castSucc = k.castSucc) (_e₁ : index i.succ = k.succ),
    T.center i = (S.center k).comap
      ((iso i.castSucc).hom ≫ eqToHom (congrArg S.level e₀))

end Monoscheme.NormalizedTower

/-- Normalizing an ordinary tower gives the displayed normalized stages, with coherent,
nonempty nowhere dense centers. The final comparison is an isomorphism if the final
ordinary stage is regular. The level-zero comparison is an isomorphism even at length zero.
Source: ILO VIII 2.2.4(ii), 2.2.6, Remark 2.3.3(i)
(blueprint: lem-per-normalized-tower-regular-pullback).

Proof (node steps 1--3): proper ordinary blowups are finite type. Apply
lem-per-quasi-excellent-finite-type-stability to every stage, then
lem-exc-quasi-excellent-nagata. The Japanese-domain condition for the fraction field and
lem-per-componentwise-normalization-affine-charts make each normalization finite, hence
Noetherian. By pqf-lem-coherent-ft-locnoeth the extended finite-type ideals are coherent.
For one step, lem-sfb-component-dominant-normalization-lift and
lem-per-noetherian-normalized-blowup-finality give inverse maps between the two normal
principalizations; uniqueness makes their composites identities. Induct, leaving level
zero unchanged. The generic-point bijection and surjectivity in
lem-sfb-componentwise-normalization-generic-properties preserve nonemptiness and nowhere
density of the centers. By rem-pc-regular-normal and
lem-sfb-normalization-normal-locally-finite, a regular last level is its own normalization.
There is no step in a length-zero tower. -/
theorem ordinaryTower_normalization (X : Scheme.{u}) [IsReduced X] [IsNoetherian X]
    (hQE : ∀ U : X.affineOpens, IsQuasiExcellent Γ(X, U))
    (A : OrdinaryBlowupTower X)
    (hCenters : ∀ i : Fin A.length,
      (∀ U : (A.level i.castSucc).affineOpens, ((A.center i).ideal U).FG) ∧
      Set.Nonempty ((A.center i).support : Set (A.level i.castSucc)) ∧
      IsNowhereDense ((A.center i).support : Set (A.level i.castSucc))) :
    ∃ D : OrdinaryTowerNormalization A,
      (∀ i : Fin (A.length + 1), IsNoetherian (D.tower.level i)) ∧
      (∀ i : Fin A.length,
        Set.Nonempty ((D.tower.center i).support : Set (D.tower.level i.castSucc)) ∧
        IsNowhereDense ((D.tower.center i).support : Set (D.tower.level i.castSucc))) ∧
      (IsRegularScheme (A.level (Fin.last A.length)) → IsIso (D.map (Fin.last A.length))) := by
  sorry

/-- Normalization commutes with regular pullback, with its canonical map characterized
uniquely over the original scheme. The pullback square is the displayed fibre-product
isomorphism, including nonfinite normalization and the empty scheme.
Source: ILO VIII Lemma 2.2.9 (blueprint: lem-per-normalized-tower-regular-pullback).

Proof (node steps 4--5): on Noetherian affines apply lem-weil-pbc-popescu-smoothing.
Smooth base change, lem-weil-pbc-smooth-over-normal-ring-normal and
lem-weil-pbc-filtered-colimit-normal-ring show that tensoring any normal algebra with the
regular algebra is normal. The tensor pushout universal property identifies the filtered
colimit with the tensor algebra. By lem-per-flat-integral-total-fractions this algebra is
the integral closure in total fractions. Use lem-sfb-normalization-affine-total-fractions
and glue the pure-tensor formulas, which agree on smaller affine opens. The
component-dominating normalization universal property gives uniqueness of the lift. -/
theorem reducedNormalization_regular_pullback {T S : Scheme.{u}}
    [IsReduced T] [IsReduced S] [IsNoetherian T] [IsNoetherian S]
    (h : T ⟶ S) (hRegular : IsRegularSchemeMorphism h) :
    ∃! l : T.reducedNormalization ⟶ S.reducedNormalization,
      l ≫ S.fromReducedNormalization = T.fromReducedNormalization ≫ h ∧
      IsPullback l T.fromReducedNormalization S.fromReducedNormalization h := by
  sorry

/-- The normalization comparisons respect identities and composition as equations of
actual morphisms, rather than merely isomorphism classes.
Source: ILO VIII 2.2.9, Remark 2.3.12(i)
(blueprint: lem-per-normalized-tower-regular-pullback).

Proof (node step 7): on pure tensors both composite maps send r tensor b to r Q(f)(b).
The tensor and localization relations give equality on affine charts; restriction and
gluing give equality on schemes. For the identity the same formula is the identity map.
Equivalently apply the uniqueness of the component-dominating normalization lift. -/
theorem reducedNormalization_regular_functoriality :
    (∀ (S : Scheme.{u}) [IsReduced S] [IsNoetherian S]
      (l : S.reducedNormalization ⟶ S.reducedNormalization),
      l ≫ S.fromReducedNormalization = S.fromReducedNormalization → l = 𝟙 _) ∧
    (∀ (S T U : Scheme.{u}) [IsReduced S] [IsReduced T] [IsReduced U]
      [IsNoetherian S] [IsNoetherian T] [IsNoetherian U]
      (h : T ⟶ S) (k : U ⟶ T),
      IsRegularSchemeMorphism h → IsRegularSchemeMorphism k →
      ∀ (a : T.reducedNormalization ⟶ S.reducedNormalization)
        (b : U.reducedNormalization ⟶ T.reducedNormalization)
        (c : U.reducedNormalization ⟶ S.reducedNormalization),
        a ≫ S.fromReducedNormalization = T.fromReducedNormalization ≫ h →
        b ≫ T.fromReducedNormalization = U.fromReducedNormalization ≫ k →
        c ≫ S.fromReducedNormalization = U.fromReducedNormalization ≫ (k ≫ h) →
        c = b ≫ a) := by
  sorry

namespace Monoscheme.NormalizedTower

/-- Every finite normalized tower with Noetherian intermediate schemes admits an
uncontracted regular pullback. All levels are cartesian and all centers are the actual
extended ideals. No Noetherianity of the pulled-back intermediate schemes is assumed.
Source: ILO VIII 2.2.7--2.2.9
(blueprint: lem-per-normalized-tower-regular-pullback).

Proof (node step 6): apply lem-sfb-flat-pullback-blowup-chart-restrictions and the
normalization calculation of steps 4--5 recursively. The projections are base changes
of the regular map. Their tensor algebras are filtered colimits of smooth algebras, so
normality does not require Noetherian pulled-back levels. Flat tensor exactness embeds
the pulled-back reduced algebra into its normalization tensor algebra, proving
reducedness. Flat going-down and the unchanged generic fields of blowup and normalization
show that each affine has finitely many components: generic fibres are localizations of
Noetherian affine rings of the source. Thus the total-fraction normalization formula
applies at every stage. Ideal extension identifies the centers. Start with the source
itself at level zero, retaining every unit-center stage. -/
theorem regular_pullback {n : ℕ} (A : NormalizedTower.{u} n)
    (hNoeth : ∀ i, IsNoetherian (A.level i))
    (T : Scheme.{u}) [IsReduced T] [IsNoetherian T]
    (h : T ⟶ A.level 0) (hRegular : IsRegularSchemeMorphism h) :
    ∃ (B : NormalizedTower.{u} n) (e : B.level 0 ≅ T) (c : CenterMap B A),
      c.map 0 = e.hom ≫ h ∧ c.IsCartesian := by
  sorry

/-- Identity and composite tower comparisons are the identity and the stagewise
composites, with all ordered ideal centers retained.
Source: ILO VIII 2.2.7--2.2.9, Remark 2.3.12(i)
(blueprint: lem-per-normalized-tower-regular-pullback).

Proof (node step 7): the affine normalization comparisons agree on pure tensors; blowup
chart comparisons agree on every extended fraction x/a. Their universal properties and
affine gluing give equality of each stage map. Induction from the initial level gives
the stated equations, including length zero. The center equations are the composition
law for ideal extension, already recorded by each CenterMap. -/
theorem regular_pullback_functoriality {n : ℕ} (A : NormalizedTower.{u} n)
    (hNoeth : ∀ i, IsNoetherian (A.level i)) :
    (∀ c : CenterMap A A, c.map 0 = 𝟙 _ → c.IsCartesian →
      ∀ i, c.map i = 𝟙 _) ∧
    (∀ (B C : NormalizedTower.{u} n) [IsNoetherian (B.level 0)]
      [IsNoetherian (C.level 0)] (c : CenterMap B A) (d : CenterMap C B)
      (e : CenterMap C A),
      IsRegularSchemeMorphism (c.map 0) → IsRegularSchemeMorphism (d.map 0) →
      c.IsCartesian → d.IsCartesian → e.IsCartesian →
      e.map 0 = d.map 0 ≫ c.map 0 → ∀ i, e.map i = d.map i ≫ c.map i) := by
  sorry

/-- Any specified unit-center isomorphism can be deleted on its own, without deleting
other eligible stages. Nonisomorphism normalizations therefore remain in the tower.
Source: ILO VIII 2.3.4--2.3.5, Remark 2.3.12(i)
(blueprint: lem-per-normalized-tower-regular-pullback).

Proof (node step 8): remove the repeated level using the inverse of its isomorphism
arrow. Compose the adjacent arrows and transport the next ideal along that inverse.
All other levels and centers retain their order. These operations preserve the
normalized-blowup presentations. The order map identifies just the chosen adjacent pair;
its comparison isomorphisms give every field of UnitStageDeletion. -/
theorem delete_unit_stage {n : ℕ} (A : NormalizedTower.{u} (n + 1)) (i : Fin (n + 1))
    (hUnit : A.center i = ⊤) (hIso : IsIso (A.arrow i)) :
    ∃ (B : NormalizedTower.{u} n) (D : UnitStageDeletion A B),
      ∀ j : Fin (n + 1), D.index j.succ = D.index j.castSucc ↔ j = i := by
  sorry

/-- Selectively deleting unit-center isomorphisms commutes with regular pullback.
Exactly the same selected stages are deleted; newly trivial stages may be retained.
The `deleted` field forbids deleting a nonisomorphism normalization with unit center.
Source: ILO VIII 2.3.4--2.3.5, Remark 2.3.12(i)
(blueprint: lem-per-normalized-tower-regular-pullback).

Proof (node step 8): a pullback of an isomorphism is an isomorphism by pulling back its
inverse, and a unit ideal extends to a unit ideal. Delete the specified stages by
composing adjacent arrows. The composition equations in step 7 identify the remaining
maps and centers. A unit-center normalized blowup is its normalization morphism by
cor-nagata-blowup-cartier-iso; it is retained whenever it is not an isomorphism. -/
theorem regular_pullback_unit_deletion {n m : ℕ} (A : NormalizedTower.{u} n)
    (A' : NormalizedTower.{u} m) (D : UnitStageDeletion A A')
    (hNoeth : ∀ i, IsNoetherian (A.level i))
    (B : NormalizedTower.{u} n) [IsNoetherian (B.level 0)]
    (c : CenterMap B A) (hRegular : IsRegularSchemeMorphism (c.map 0))
    (hCartesian : c.IsCartesian) :
    ∃ (B' : NormalizedTower.{u} m) (E : UnitStageDeletion B B') (d : CenterMap B' A')
      (he : E.index = D.index), d.IsCartesian ∧
      ∀ i : Fin (n + 1), (E.iso i).hom ≫ d.map (E.index i) =
        c.map i ≫ (D.iso i).hom ≫ eqToHom (congrArg A'.level
          (congrArg (fun j : Fin (n + 1) →o Fin (m + 1) ↦ j i)
            he.symm)) := by
  sorry

end Monoscheme.NormalizedTower

/-- For a cartesian ordinary tower, normalizing after regular pullback and pulling back
the normalized tower agree, with their structural maps, arrows and extended centers.
Source: ILO VIII 2.2.4(ii), 2.2.6--2.2.9, Remark 2.3.12(i)
(blueprint: lem-per-normalized-tower-regular-pullback).

Proof (node step 7): at each positive level use the normalization comparison of steps
4--5 for the cartesian square of ordinary levels. The stage-zero comparison is the
given base map, transported by the two initial isomorphisms. On one-step blowup charts
these comparisons preserve extended fractions, and on normalizations they preserve
pure tensors. Hence they commute with all arrows and identify the extended ideals.
Induction gives the whole centered tower comparison, also for length zero. -/
theorem ordinaryTower_normalization_regular_pullback {X Y : Scheme.{u}}
    [IsReduced X] [IsReduced Y] [IsNoetherian X] [IsNoetherian Y]
    (hQE : ∀ U : X.affineOpens, IsQuasiExcellent Γ(X, U))
    (h : Y ⟶ X) (hRegular : IsRegularSchemeMorphism h)
    (A : OrdinaryBlowupTower X) (B : OrdinaryBlowupTower Y)
    (p : OrdinaryTowerCartesianMap h A B)
    (hCenters : ∀ i : Fin A.length,
      (∀ U : (A.level i.castSucc).affineOpens, ((A.center i).ideal U).FG) ∧
      Set.Nonempty ((A.center i).support : Set (A.level i.castSucc)) ∧
      IsNowhereDense ((A.center i).support : Set (A.level i.castSucc)))
    (D : OrdinaryTowerNormalization A) :
    ∃ (E : OrdinaryTowerNormalization B)
      (c : ∀ i : Fin (B.length + 1),
        E.tower.level i ⟶ D.tower.level (Fin.cast (congrArg Nat.succ p.length_eq) i)),
      (∀ i, IsPullback (c i) (E.map i)
        (D.map (Fin.cast (congrArg Nat.succ p.length_eq) i)) (p.map i)) ∧
      (∀ i : Fin B.length,
        E.tower.arrow i ≫ c i.castSucc = c i.succ ≫
          D.tower.arrow (Fin.cast p.length_eq i)) ∧
      (∀ i : Fin B.length,
        E.tower.center i = (D.tower.center (Fin.cast p.length_eq i)).comap (c i.castSucc)) := by
  sorry

/-- Noetherian schemes admit finite affine covers by Noetherian rings, including the
empty cover for the empty scheme.
Source: ILO VIII 2.2.1 and the finite affine reductions in 2.4.1
(blueprint: lem-per-normalized-tower-regular-pullback).

Proof (node step 8): local Noetherianity supplies Noetherian affine neighborhoods.
Quasi-compactness supplies a finite subcover; index that finite list by Fin t. -/
theorem noetherian_finite_affine_cover (X : Scheme.{u}) [IsNoetherian X] :
    ∃ (t : ℕ) (U : Fin t → X.affineOpens),
      (⨆ i, (U i).1) = ⊤ ∧ ∀ i, IsNoetherianRing Γ(X, (U i).1) := by
  sorry

end AlgebraicGeometry
