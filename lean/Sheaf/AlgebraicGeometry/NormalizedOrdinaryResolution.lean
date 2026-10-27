module

public import Sheaf.AlgebraicGeometry.OrdinaryResolutionRule
public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Sheaf.AlgebraicGeometry.NormalizedBlowup
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.QENormalizedResolutionRule
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.NormalizedBlowupCalculus
import WeilConjectures.Blowup.Affine.ChartAlgebra
import WeilConjectures.Blowup.FiniteDegree.Algebra
import WeilConjectures.AlgebraicGeometry.FormallySmooth
import WeilConjectures.AlgebraicGeometry.ModulePullbackIdealQuotient
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

/-! # Levelwise normalization of an ordinary resolution rule

Source: ILO, Travaux de Gabber, Exposé VIII, Proposition 2.2.4(ii), 2.2.6,
Lemma 2.2.9, 2.3.3(i), 2.3.4 and Remark 2.3.12(i), printed pp. 90--93
(blueprint: lem-trf-normalized-resolution-on-normal-inputs).

The tower and contraction notions are the published normalized towers. The records below
specify their identification with the prescribed ordinary levels and comparisons.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open Monoscheme

/-- The prescribed levels: the input itself at zero and componentwise normalization at
positive indices. Source: ILO VIII 2.2.6
(blueprint: lem-trf-normalized-resolution-on-normal-inputs). -/
noncomputable def OrdinaryBlowupTower.normalizedLevel {X : Scheme.{u}}
    (A : OrdinaryBlowupTower X) (i : Fin (A.length + 1)) : Scheme.{u} :=
  match i with
  | ⟨0, _⟩ => X
  | ⟨k + 1, hk⟩ => (A.level ⟨k + 1, hk⟩).reducedNormalization

/-- The normalization projection, with the given identification of the ordinary initial
level at zero. Source: ILO VIII 2.2.6
(blueprint: lem-trf-normalized-resolution-on-normal-inputs). -/
noncomputable def OrdinaryBlowupTower.normalizedProjection {X : Scheme.{u}}
    (A : OrdinaryBlowupTower X) (i : Fin (A.length + 1)) :
    A.normalizedLevel i ⟶ A.level i :=
  match i with
  | ⟨0, _⟩ => A.initial.inv
  | ⟨k + 1, hk⟩ => (A.level ⟨k + 1, hk⟩).fromReducedNormalization

/-- A realization of the prescribed levelwise normalization, using the existing normalized
resolution tower. `levelIso` fixes the objects, `centers` fixes their actual extended ideals,
and `arrows` fixes the induced transitions over the ordinary tower. The initial level maps
to the input by `levelIso 0`; composing its normalization projection with `A.initial.hom`
is that same map. Source: ILO VIII 2.2.4(ii), 2.2.6 and 2.3.3(i)
(blueprint: lem-trf-normalized-resolution-on-normal-inputs). -/
structure NormalizedOrdinaryResolution (S : RationalResolutionInput.{u})
    (A : OrdinaryBlowupTower S.scheme) where
  tower : NormalizedTower.{u} A.length
  levelIso : ∀ i, tower.level i ≅ A.normalizedLevel i
  centers : ∀ i : Fin A.length,
    tower.center i = (A.center i).comap
      ((levelIso i.castSucc).hom ≫ A.normalizedProjection i.castSucc)
  arrows : ∀ i : Fin A.length,
    tower.arrow i ≫ (levelIso i.castSucc).hom ≫ A.normalizedProjection i.castSucc =
      (levelIso i.succ).hom ≫ A.normalizedProjection i.succ ≫
        A.transition i.castSucc i.succ (le_of_lt i.castSucc_lt_succ)
  normal : ∀ i (x : tower.level i),
    IsDomain ((tower.level i).presheaf.stalk x) ∧
      IsIntegrallyClosed ((tower.level i).presheaf.stalk x)
  finiteType : ∀ i,
    LocallyOfFiniteType (tower.toFirst i ≫ (levelIso 0).hom ≫ S.structureMap)
  quasiCompact : ∀ i,
    QuasiCompact (tower.toFirst i ≫ (levelIso 0).hom ≫ S.structureMap)
  coherent : ∀ i : Fin A.length,
    RingedSpace.IsCoherent (tower.level i.castSucc).toRingedSpace (tower.center i).toModules
  nonempty : ∀ i : Fin A.length,
    Set.Nonempty ((tower.center i).support : Set (tower.level i.castSucc))
  nowhereDense : tower.HasNowhereDenseCenters
  regular : tower.IsDesingularization
  terminal : IsIso ((levelIso (Fin.last A.length)).hom ≫
    A.normalizedProjection (Fin.last A.length))

/-- The canonical map to the corresponding ordinary level.
Source: ILO VIII 2.2.6 (blueprint: lem-trf-normalized-resolution-on-normal-inputs). -/
noncomputable def NormalizedOrdinaryResolution.projection
    {S : RationalResolutionInput.{u}} {A : OrdinaryBlowupTower S.scheme}
    (N : NormalizedOrdinaryResolution S A) (i : Fin (A.length + 1)) :
    N.tower.level i ⟶ A.level i :=
  (N.levelIso i).hom ≫ A.normalizedProjection i

/-- Forget the comparison with the ordinary tower, retaining the published based resolution.
Source: ILO VIII 2.3.2--2.3.3(i)
(blueprint: lem-trf-normalized-resolution-on-normal-inputs). -/
noncomputable def NormalizedOrdinaryResolution.toResolution
    {S : RationalResolutionInput.{u}} {A : OrdinaryBlowupTower S.scheme}
    (N : NormalizedOrdinaryResolution S A) : QENormalizedResolutionTower S.scheme where
  length := A.length
  tower := N.tower
  initial := N.levelIso 0
  coherent := N.coherent
  nonempty := N.nonempty
  nowhereDense := N.nowhereDense
  regular := N.regular

/-- The simultaneous normalization of a fixed ordinary rule on its normal inputs. The
canonical normalization squares are part of the data, so a comparison cannot be replaced
by an unrelated cartesian identification. Counts are the ordinary counts, retaining exactly
the original ordered stages. Unit stages are isomorphisms by the published comparison;
its contraction deletes precisely those stages. The map and retained-index laws are written
explicitly, including all transports of level indices.
Source: ILO VIII 2.2.6--2.2.9, 2.3.4--2.3.5(i) and Remark 2.3.12(i)
(blueprint: lem-trf-normalized-resolution-on-normal-inputs). -/
structure NormalizedOrdinaryResolutionRule (R : SmoothFunctorialOrdinaryResolution.{u}) where
  realization : ∀ (S : RationalResolutionInput.{u}),
    (∀ x : S.scheme, IsDomain (S.scheme.presheaf.stalk x) ∧
      IsIntegrallyClosed (S.scheme.presheaf.stalk x)) →
    NormalizedOrdinaryResolution S (R.tower S)
  comparison : ∀ (S T : RationalResolutionInput.{u})
    (hnS : ∀ x : S.scheme, IsDomain (S.scheme.presheaf.stalk x) ∧
      IsIntegrallyClosed (S.scheme.presheaf.stalk x))
    (hnT : ∀ x : T.scheme, IsDomain (T.scheme.presheaf.stalk x) ∧
      IsIntegrallyClosed (T.scheme.presheaf.stalk x))
    (h : T.scheme ⟶ S.scheme) (_over : h ≫ S.structureMap = T.structureMap) [Smooth h],
    QENormalizedResolutionComparison h
      (realization S hnS).toResolution (realization T hnT).toResolution
  count_eq : ∀ S T hnS hnT h over [Smooth h],
    (comparison S T hnS hnT h over).contraction.index = (R.comparison S T h over).count
  normalization_square : ∀ S T hnS hnT h over [Smooth h] i,
    (comparison S T hnS hnT h over).levelMap i ≫ (realization S hnS).projection i =
      (realization T hnT).projection
          ((comparison S T hnS hnT h over).contraction.index i) ≫
        eqToHom (congrArg (R.tower T).level
          (congrArg (fun c ↦ c i) (count_eq S T hnS hnT h over))) ≫
        (R.comparison S T h over).levelMap i
  deleted_iff_unit : ∀ S T hnS hnT h over [Smooth h] (i : Fin (R.tower S).length),
    i ∉ Set.range (R.comparison S T h over).retainedStage ↔
      ((comparison S T hnS hnT h over).pulled.center i) = ⊤
  retained_before : ∀ S T hnS hnT h over [Smooth h] k,
    (comparison S T hnS hnT h over).contraction.index
      ((R.comparison S T h over).retainedStage k).castSucc = k.castSucc
  retained_after : ∀ S T hnS hnT h over [Smooth h] k,
    (comparison S T hnS hnT h over).contraction.index
      ((R.comparison S T h over).retainedStage k).succ = k.succ
  identity_map : ∀ S hnS i,
    HEq ((comparison S S hnS hnS (𝟙 S.scheme) (by simp)).levelMap i)
      (𝟙 ((realization S hnS).tower.level i))
  composition_map : ∀ S T U hnS hnT hnU (h : T.scheme ⟶ S.scheme)
    (k : U.scheme ⟶ T.scheme) (overH : h ≫ S.structureMap = T.structureMap)
    (overK : k ≫ T.structureMap = U.structureMap) [Smooth h] [Smooth k] i,
    HEq ((comparison S U hnS hnU (k ≫ h)
      (by rw [Category.assoc, overH, overK])).levelMap i)
      ((comparison T U hnT hnU k overK).levelMap
          ((comparison S T hnS hnT h overH).contraction.index i) ≫
        (comparison S T hnS hnT h overH).levelMap i)
  identity_retained : ∀ (S : RationalResolutionInput.{u})
    (_hnS : ∀ x : S.scheme, IsDomain (S.scheme.presheaf.stalk x) ∧
      IsIntegrallyClosed (S.scheme.presheaf.stalk x)) k,
    (R.comparison S S (𝟙 S.scheme) (by simp)).retainedStage k = k
  composition_retained : ∀ (S T U : RationalResolutionInput.{u})
    (_hnS : ∀ x : S.scheme, IsDomain (S.scheme.presheaf.stalk x) ∧
      IsIntegrallyClosed (S.scheme.presheaf.stalk x))
    (_hnT : ∀ x : T.scheme, IsDomain (T.scheme.presheaf.stalk x) ∧
      IsIntegrallyClosed (T.scheme.presheaf.stalk x))
    (_hnU : ∀ x : U.scheme, IsDomain (U.scheme.presheaf.stalk x) ∧
      IsIntegrallyClosed (U.scheme.presheaf.stalk x))
    (h : T.scheme ⟶ S.scheme) (k : U.scheme ⟶ T.scheme)
    (overH : h ≫ S.structureMap = T.structureMap)
    (overK : k ≫ T.structureMap = U.structureMap) [Smooth h] [Smooth k] i,
    (R.comparison S U (k ≫ h)
      (by rw [Category.assoc, overH, overK])).retainedStage i =
      (R.comparison S T h overH).retainedStage ((R.comparison T U k overK).retainedStage i)
  surjective_no_deletion : ∀ S T hnS hnT h over [Smooth h] [Surjective h],
    Function.Injective (comparison S T hnS hnT h over).contraction.index
  empty : ∀ S, IsEmpty S.scheme → (R.tower S).length = 0

/-- Normalizing a fixed ordinary resolution rule on normal rational inputs produces the
prescribed normalized rule, with the same ordered contraction indices.
Source: ILO VIII 2.2.4(ii), 2.2.6, 2.2.9, 2.3.3(i), 2.3.4, Remark 2.3.12(i)
(blueprint: lem-trf-normalized-resolution-on-normal-inputs).

Proof:
1. Induct on the ordinary levels. The charts A[I/a] are finitely generated subalgebras of
reduced localizations, so all ordinary levels are reduced and finite type over the rationals
(def-nagata-blowup-chart-ring, prop-nagata-affine-blowup-chart-cover, def-pc-reduced-scheme,
def-weil-finite-type-morphism). Empty charts cause no exception.
2. These levels are Noetherian (lem-weil-pbc-finite-type-over-noetherian). Locally finitely
generated quasi-coherent centers are coherent (pqf-lem-coherent-ft-locnoeth), with nonempty
nowhere dense zero schemes by def-trf-ordinary-resolution-rule.
3. Starting with the normal input, apply lem-trf-normalized-blowup-calculus inductively:
normalizing the ordinary next blowup gives the normalized blowup of the extended ideal on
the current normalized level, over that level. This also gives normality, reducedness and
finite type for every level (def-trf-normalized-blowup).
4. Normalization is surjective and bijective on generic points
(lem-sfb-componentwise-normalization-generic-properties). Extended ideals are locally
generated by the images of the same finite generators
(lem-weil-pbc-module-pullback-ideal-quotient); their zero sets are inverse images of the old
zero sets. They remain nonempty, nowhere dense and coherent by Step 2. Normalization of
the regular terminal scheme is its canonical identity. Length zero is the trivial tower;
on the empty input no nonempty center is possible.
5. Smoothness is stable under base change: local finite presentation is stable
(lem-weil-pbc-qcqs-morphism-permanence), and lift affine square-zero thickenings using
formal smoothness, then pair the lift with the map to the new base
(def-sbc-formally-smooth, def-sbc-smooth-morphisms, def-pc-fibre-product).
6. Normalize each ordinary cartesian comparison. Smooth compatibility of normalization
and normalized blowup (lem-trf-normalized-blowup-calculus) makes each new square cartesian,
with the indicated commutative normalization square. Extended centers agree by successive
extension of the same local generators (lem-weil-pbc-module-pullback-ideal-quotient).
7. A unit ideal stays unit; a nonunit ideal stays nonunit under the surjective normalization
map. Thus the retained indices are exactly the ordinary retained indices. On a normal level
the normalized blowup of the unit ideal is an isomorphism, so precisely those stages can be
deleted. A nonunit Cartier ideal remains retained, even if its blowup is an isomorphism.
8. The ordinary count and map laws, together with uniqueness of the normalization and
blowup comparisons, give the identity and composition laws, including retained indices.
Surjectivity deletes no ordinary stage and therefore no normalized stage. -/
theorem nonempty_normalizedOrdinaryResolutionRule
    (R : SmoothFunctorialOrdinaryResolution.{u}) :
    Nonempty (NormalizedOrdinaryResolutionRule R) := by
  sorry

end AlgebraicGeometry
