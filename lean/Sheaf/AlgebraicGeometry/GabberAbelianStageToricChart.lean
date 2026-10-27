/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q90
-/
module

public import Sheaf.AlgebraicGeometry.GabberAbsoluteEquivariantModification
public import Sheaf.AlgebraicGeometry.FSLogSmoothEtale
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.GroupTheory.Exponent
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
import Sheaf.AlgebraicGeometry.FineFanBlowup
import Sheaf.AlgebraicGeometry.LogSmoothInvertibleTorsionLogRegular
import Sheaf.AlgebraicGeometry.CoherentLogIdealChartConstruction
import Sheaf.AlgebraicGeometry.LogFanChartBlowup
import Sheaf.TraceFormula.LogRegularDivisorialStructure
import Sheaf.AlgebraicGeometry.MonoidalResolutionTower
import Sheaf.AlgebraicGeometry.StrictFanChartLocalComparison
import WeilConjectures.RingTheory.FiniteProjectiveStandardFreeCover
import WeilConjectures.RingTheory.LocalizationOfRegularRing
import WeilConjectures.RingTheory.RegularRingSmoothAscent
import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.LinearAlgebra.FreeModule.PID

/-! # Local invariant-monoid charts of the abelian fourth stage

Source: ILO, Travaux de Gabber, VIII 5.3.8, 5.4.4, 5.5.3--5.5.5; X 1.8,
diagrams (1.a)--(1.d), pp. 146--148
(blueprint: lem-per-gabber-abelian-stage-toric-chart).

The diagram data below describe the actual invariant monoids and monomial maps.
They do not select a modification from a mere existence assertion.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.GabberAbelianStage

/-- The geometric inertia subgroup, with its actual inclusion in the acting group.
Source: ILO X 1.8 (blueprint: lem-per-gabber-abelian-stage-toric-chart). -/
def inertia {G : Type v} [Group G] {X : FineSaturatedLogScheme.{u}}
    (a : FSLogGroupAction G X) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X.scheme) : Subgroup G where
  carrier := {g | x ≫ (a.baseAction g).hom = x}
  one_mem' := by
    change x ≫ (a.baseAction 1).hom = x
    rw [map_one]
    exact Category.comp_id x
  mul_mem' := by
    intro g h hg hh
    change x ≫ (a.baseAction (g * h)).hom = x
    rw [map_mul]
    change x ≫ ((a.baseAction h).hom ≫ (a.baseAction g).hom) = x
    rw [← Category.assoc, hh, hg]
  inv_mem' := by
    intro g hg
    change x ≫ (a.baseAction g⁻¹).hom = x
    rw [map_inv]
    change x ≫ (a.baseAction g).inv = x
    have he := congrArg (fun k ↦ k ≫ (a.baseAction g).inv) hg
    simpa [Category.assoc] using he.symm

/-- A chart is normalized by its monomial structural map, including its coefficients.
Source: ILO X 1.8 (1.c)--(1.d)
(blueprint: lem-per-gabber-abelian-stage-toric-chart). -/
def IsMonomialChart {A M L : Type u} [CommRing A] [CommMonoid M] [CommMonoid L]
    (X : FineSaturatedLogScheme.{u}) (W : X.scheme.Etale)
    (β : L →* X.logStructure.monoidSheaf.obj.obj (op W)) (ι : L →* M)
    (h : W.left ⟶ Spec (.of (MonoidAlgebra A M))) : Prop :=
  X.logStructure.IsChart W β ∧ ∀ m : L,
    X.logStructure.alpha.app (op W) (β m) =
      h.appTop ((Scheme.ΓSpecIso (.of (MonoidAlgebra A M))).inv (MonoidAlgebra.single (ι m) 1))

/-- Algebraic data of the local invariant-monoid construction. The coefficient ring
is a localization of the cyclotomic integer ring in which the inertia exponent is inverted.
`P` is the non-sharp boundary chart and `Pbar` adds the smooth eigenvector coordinates.
Source: ILO X 1.8, (1.c)--(1.d)
(blueprint: lem-per-gabber-abelian-stage-toric-chart). -/
structure ToricData (H : Type v) [Group H] where
  N : ℕ
  exponent : N = Monoid.exponent H
  positive : 0 < N
  Λ : Type u
  ring : CommRing Λ
  cyclotomic : Algebra (CyclotomicRing N ℤ ℚ) Λ
  denominators : Submonoid (CyclotomicRing N ℤ ℚ)
  localization : IsLocalization denominators Λ
  invertExponent : (N : CyclotomicRing N ℤ ℚ) ∈ denominators
  Q : Type u
  monoidQ : CommMonoid Q
  fsQ : IsFineSaturatedMonoid Q
  sharpQ : ∀ q : Q, IsUnit q → q = 1
  t : ℕ
  r : ℕ
  s : ℕ
  P : Type u
  monoidP : CommMonoid P
  coordinates : P ≃* ULift.{u} (Multiplicative ((Fin t → ℤ) × (Fin r → ℕ)))
  γ : Q →* P
  injective : Function.Injective
    (Algebra.GrothendieckGroup.lift (Algebra.GrothendieckGroup.of.comp γ))
  torsionFinite : Finite (CommGroup.torsion
    (Algebra.GrothendieckGroup P ⧸
      (Algebra.GrothendieckGroup.lift (Algebra.GrothendieckGroup.of.comp γ)).range))
  torsionUnit : IsUnit (Nat.card (CommGroup.torsion
    (Algebra.GrothendieckGroup P ⧸
      (Algebra.GrothendieckGroup.lift (Algebra.GrothendieckGroup.of.comp γ)).range)) : Λ)

attribute [instance] ToricData.ring ToricData.cyclotomic ToricData.monoidQ ToricData.monoidP

/-- The enlarged monoid, with actual additional eigenvector coordinates. Source: ILO X 1.8
(blueprint: lem-per-gabber-abelian-stage-toric-chart). -/
abbrev ToricData.Pbar {H : Type v} [Group H] (d : ToricData.{u, v} H) :=
  d.P × ULift.{u} (Multiplicative (Fin d.s → ℕ))

/-- Inclusion of the original boundary chart. Source: ILO X 1.8, (1.c)
(blueprint: lem-per-gabber-abelian-stage-toric-chart). -/
def ToricData.includeP {H : Type v} [Group H] (d : ToricData.{u, v} H) : d.P →* d.Pbar :=
  MonoidHom.inl _ _

/-- The invariant enlarged monoid is the character kernel intersected with the monoid,
not a freely chosen submonoid. Source: ILO X 1.8, (1.c)
(blueprint: lem-per-gabber-abelian-stage-toric-chart). -/
def invariantMonoid {H : Type v} [Group H] (d : ToricData.{u, v} H)
    (χ : Algebra.GrothendieckGroup d.Pbar →* (H →* rootsOfUnity d.N d.Λ)) :
    Submonoid d.Pbar :=
  MonoidHom.mker (χ.comp (Algebra.GrothendieckGroup.of (M := d.Pbar)))

/-- The original invariant monoid is the inverse image of the enlarged invariant monoid.
Source: ILO X 1.8, (1.d) (blueprint: lem-per-gabber-abelian-stage-toric-chart). -/
def originalInvariantMonoid {H : Type v} [Group H] (d : ToricData.{u, v} H)
    (χ : Algebra.GrothendieckGroup d.Pbar →* (H →* rootsOfUnity d.N d.Λ)) :
    Submonoid d.P :=
  (invariantMonoid d χ).comap d.includeP

/-- All invariant-monoid data, including the factorization from the base and the finite
Kummer index in the enlarged lattice. Source: ILO X 1.8
(blueprint: lem-per-gabber-abelian-stage-toric-chart). -/
structure InvariantData {H : Type v} [Group H] (d : ToricData.{u, v} H) where
  χ : Algebra.GrothendieckGroup d.Pbar →* (H →* rootsOfUnity d.N d.Λ)
  baseInvariant : ∀ q : d.Q, d.γ q ∈ originalInvariantMonoid d χ
  fs : IsFineSaturatedMonoid (invariantMonoid d χ)
  fsOriginal : IsFineSaturatedMonoid (originalInvariantMonoid d χ)
  groupInjective : Function.Injective (Algebra.GrothendieckGroup.lift
      (Algebra.GrothendieckGroup.of.comp (invariantMonoid d χ).subtype))
  finiteIndex : Finite (Algebra.GrothendieckGroup d.Pbar ⧸
    (Algebra.GrothendieckGroup.lift
      (Algebra.GrothendieckGroup.of.comp (invariantMonoid d χ).subtype)).range)
  indexAnnihilator : ∃ n : ℕ, 0 < n ∧ IsUnit (n : d.Λ) ∧
    ∀ g : Algebra.GrothendieckGroup d.Pbar,
      g ^ n ∈ (Algebra.GrothendieckGroup.lift
      (Algebra.GrothendieckGroup.of.comp (invariantMonoid d χ).subtype)).range

/-- The actual factorization through the original invariant monoid. Source: ILO X 1.8
(blueprint: lem-per-gabber-abelian-stage-toric-chart). -/
def InvariantData.baseMap {H : Type v} [Group H] {d : ToricData.{u, v} H}
    (e : InvariantData d) : d.Q →* originalInvariantMonoid d e.χ :=
  d.γ.codRestrict _ e.baseInvariant


/-- The omitted coordinates of a retained-boundary chart have exponent zero.
Source: ILO X 1.8, (1.d)
(blueprint: lem-per-gabber-abelian-stage-toric-chart). -/
def retainedMonoid {M : Type u} [CommMonoid M] {a b : ℕ}
    (coordinates : M ≃* ULift.{u} (Multiplicative ((Fin a → ℤ) × (Fin b → ℕ))))
    (c : ℕ) : Submonoid M where
  carrier := {m | ∀ j : Fin b, c ≤ j.val → (coordinates m).down.toAdd.2 j = 0}
  one_mem' := by simp
  mul_mem' := by
    intro m n hm hn j hj
    simpa using congrArg₂ (· + ·) (hm j hj) (hn j hj)

/-- A regular resolved monoid chart, retaining exactly the first `c` boundary coordinates.
All group maps are induced by the displayed monoid maps. Source: ILO X 1.8, (1.d)
(blueprint: lem-per-gabber-abelian-stage-toric-chart). -/
structure ResolvedMonoid {H : Type v} [Group H] {d : ToricData.{u, v} H}
    (e : InvariantData d) where
  M : Type u
  monoidM : CommMonoid M
  a : ℕ
  b : ℕ
  c : ℕ
  bound : c ≤ b
  coordinates : M ≃* ULift.{u} (Multiplicative ((Fin a → ℤ) × (Fin b → ℕ)))
  ν : invariantMonoid d e.χ →* M
  groupIso : Function.Bijective
    (Algebra.GrothendieckGroup.lift (Algebra.GrothendieckGroup.of.comp ν))
  retained : ∀ r : originalInvariantMonoid d e.χ,
    ν ⟨d.includeP r.val, r.property⟩ ∈ retainedMonoid coordinates c
  affineSpace : Spec (.of (MonoidAlgebra d.Λ M)) ≅
    𝔸(ULift.{u} (Fin (b - c));
      Spec (.of (MonoidAlgebra d.Λ (retainedMonoid coordinates c))))
  affineSpace_over : affineSpace.hom ≫
      𝔸(ULift.{u} (Fin (b - c));
        Spec (.of (MonoidAlgebra d.Λ (retainedMonoid coordinates c)))) ↘
          Spec (.of (MonoidAlgebra d.Λ (retainedMonoid coordinates c))) =
    Spec.map (CommRingCat.ofHom
      (MonoidAlgebra.mapDomainRingHom d.Λ (retainedMonoid coordinates c).subtype))

attribute [instance] ResolvedMonoid.monoidM

/-- The projection of a saturated tower to its first level, by actual composition.
Source: ILO VIII 3.3.8--3.3.10
(blueprint: lem-per-gabber-abelian-stage-toric-chart). -/
def towerProjection (T : SaturatedLogBlowupTower.{u}) :
    (i : ℕ) → (hi : i ≤ T.length) →
      (T.level ⟨i, Nat.lt_succ_of_le hi⟩).scheme ⟶ (T.level 0).scheme
  | 0, _ => 𝟙 _
  | i + 1, hi => (T.arrow ⟨i, Nat.lt_of_succ_le hi⟩).base ≫
      towerProjection T i (Nat.le_of_succ_le hi)

/-- A monomial section transported through a specified affine-spectrum identification.
Source: ILO X 1.8, (1.c)
(blueprint: lem-per-gabber-abelian-stage-toric-chart). -/
def monomialSection {A M : Type u} [CommRing A] [CommMonoid M]
    {X : Scheme.{u}} (e : X ≅ Spec (.of (MonoidAlgebra A M))) (m : M) (a : A) :
    Γ(X, ⊤) :=
  e.hom.appTop ((Scheme.ΓSpecIso (.of (MonoidAlgebra A M))).inv
    (MonoidAlgebra.single m a))

/-- The product of the original boundary coordinates; smooth eigenvector coordinates
are excluded. Source: ILO X 1.8, pp.146--147
(blueprint: lem-per-gabber-abelian-stage-toric-chart). -/
def ToricData.boundaryMonomial {H : Type v} [Group H] (d : ToricData.{u, v} H) : d.Pbar :=
  d.includeP (d.coordinates.symm ⟨Multiplicative.ofAdd (0, fun _ ↦ 1)⟩)

/-- The toric fourth-stage diagram, with the chosen quotient resolution and its actual
fs pullback tower. The final quotient keeps only the original boundary; its underlying
scheme is the final enlarged quotient resolution. Source: ILO VIII 5.3.8; X 1.8 (1.a)--(1.d)
(blueprint: lem-per-gabber-abelian-stage-toric-chart). -/
structure ToricConstruction (P : GabberModification.FourthProcedure.{u, v})
    {H : Type v} [Group H] [Finite H] (d : ToricData.{u, v} H) (e : InvariantData d) where
  Y : FineSaturatedLogScheme.{u}
  affine : Y.scheme ≅ Spec (.of (MonoidAlgebra d.Λ d.Pbar))
  action : FSLogGroupAction H Y
  diagonal : ∀ (h : H) (m : d.Pbar) (a : d.Λ),
    (action.baseAction h).hom.appTop (monomialSection affine m a) =
      monomialSection affine m
        (((e.χ (Algebra.GrothendieckGroup.of m) h).val : d.Λ) * a)
  chart : d.P →* Y.logStructure.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 Y.scheme)))
  chart_spec : IsMonomialChart Y (Scheme.Etale.mk (𝟙 Y.scheme)) chart d.includeP affine.hom
  boundary : Y.scheme.IdealSheafData
  boundary_support : (boundary.support : Set Y.scheme) =
    {y | MonoidAlgebra.single d.boundaryMonomial (1 : d.Λ) ∈ (affine.hom y).asIdeal}
  input : GabberModification.AbelianInput action boundary
  rigidification : GabberModification.Rigidification action
  enlargedAffine : rigidification.enlarged.scheme ≅ Spec (.of (MonoidAlgebra d.Λ d.Pbar))
  sameAffine : rigidification.forget.base ≫ affine.hom = enlargedAffine.hom
  enlargedChart : d.Pbar →* rigidification.enlarged.logStructure.monoidSheaf.obj.obj
    (op (Scheme.Etale.mk (𝟙 rigidification.enlarged.scheme)))
  enlargedChart_spec : IsMonomialChart rigidification.enlarged
    (Scheme.Etale.mk (𝟙 rigidification.enlarged.scheme)) enlargedChart
    (MonoidHom.id _) enlargedAffine.hom
  quotient : GabberModification.RigidifiedQuotient rigidification
  quotientAffine : quotient.quotient.scheme ≅
    Spec (.of (MonoidAlgebra d.Λ (invariantMonoid d e.χ)))
  quotient_spec : quotient.map.base ≫ quotientAffine.hom = enlargedAffine.hom ≫
    Spec.map (CommRingCat.ofHom
      (MonoidAlgebra.mapDomainRingHom d.Λ (invariantMonoid d e.χ).subtype))
  quotientChart : invariantMonoid d e.χ →* quotient.quotient.logStructure.monoidSheaf.obj.obj
    (op (Scheme.Etale.mk (𝟙 quotient.quotient.scheme)))
  quotientChart_spec : IsMonomialChart quotient.quotient
    (Scheme.Etale.mk (𝟙 quotient.quotient.scheme)) quotientChart
    (MonoidHom.id _) quotientAffine.hom
  construction : GabberModification.RigidifiedConstruction P.resolution
    (P.tower H Y action boundary input) rigidification quotient
  finalQuotient : FineSaturatedLogScheme.{u}
  finalMap : EtaleLogHom (P.tower H Y action boundary input).source finalQuotient
  finalIsQuotient : ((P.tower H Y action boundary input).action
    (Fin.last (P.tower H Y action boundary input).length)).IsQuotient finalMap
  finalAffine : finalQuotient.scheme ≅
    ((P.resolution.tower quotient.quotient quotient.input).tower.level
      (Fin.last (P.resolution.tower quotient.quotient quotient.input).tower.length)).scheme
  enlargedFinalMap :
    (construction.enlargedLevel (Fin.last (P.tower H Y action boundary input).length)).scheme ⟶
      ((P.resolution.tower quotient.quotient quotient.input).tower.level
        (Fin.last (P.resolution.tower quotient.quotient quotient.input).tower.length)).scheme
  enlargedFinalMap_eq : HEq enlargedFinalMap
    (construction.quotientMap (Fin.last (P.tower H Y action boundary input).length)).base
  finalMap_eq : finalMap.base ≫ finalAffine.hom =
    (construction.schemeIso (Fin.last (P.tower H Y action boundary input).length)).inv ≫
      enlargedFinalMap
  retainedBoundary : finalQuotient.scheme.IdealSheafData
  retainedBoundary_support : (retainedBoundary.support : Set finalQuotient.scheme) =
    finalQuotient.logStructure.trivialityLocusᶜ
  originalBoundary : finalMap.base ⁻¹' (retainedBoundary.support : Set finalQuotient.scheme) =
    (P.tower H Y action boundary input).map.base ⁻¹' (boundary.support : Set Y.scheme)

/-- The final enlarged quotient log scheme of the chosen resolution tower.
Source: ILO VIII 5.3.8; X 1.8 (1.a)
(blueprint: lem-per-gabber-abelian-stage-toric-chart). -/
def ToricConstruction.resolved {P : GabberModification.FourthProcedure.{u, v}}
    {H : Type v} [Group H] [Finite H] {d : ToricData.{u, v} H} {e : InvariantData d}
    (C : ToricConstruction P d e) : FineSaturatedLogScheme.{u} :=
  (P.resolution.tower C.quotient.quotient C.quotient.input).tower.level
    (Fin.last (P.resolution.tower C.quotient.quotient C.quotient.input).tower.length)

/-- One affine chart on the resolved quotient, with both the enlarged and retained log
charts, the actual blowup monoid map, and the original-boundary support. Source: ILO X 1.8
(blueprint: lem-per-gabber-abelian-stage-toric-chart). -/
structure ToricConstruction.Chart {P : GabberModification.FourthProcedure.{u, v}}
    {H : Type v} [Group H] [Finite H] {d : ToricData.{u, v} H} {e : InvariantData d}
    (C : ToricConstruction P d e) where
  monoids : ResolvedMonoid e
  U : C.finalQuotient.scheme.Opens
  affine : U.toScheme ≅ Spec (.of (MonoidAlgebra d.Λ monoids.M))
  chart : retainedMonoid monoids.coordinates monoids.c →*
    C.finalQuotient.logStructure.monoidSheaf.obj.obj (op (Scheme.Etale.mk U.ι))
  chart_spec : IsMonomialChart C.finalQuotient (Scheme.Etale.mk U.ι) chart
    (retainedMonoid monoids.coordinates monoids.c).subtype affine.hom
  fullChart : monoids.M →* C.resolved.logStructure.monoidSheaf.obj.obj
    (op (Scheme.Etale.mk (U.ι ≫ C.finalAffine.hom)))
  fullChart_spec : IsMonomialChart C.resolved
    (Scheme.Etale.mk (U.ι ≫ C.finalAffine.hom)) fullChart (MonoidHom.id _) affine.hom
  ν_spec : affine.hom ≫ Spec.map
      (CommRingCat.ofHom (MonoidAlgebra.mapDomainRingHom d.Λ monoids.ν)) =
    U.ι ≫ C.finalAffine.hom ≫
      towerProjection (P.resolution.tower C.quotient.quotient C.quotient.input).tower
        (P.resolution.tower C.quotient.quotient C.quotient.input).tower.length (le_refl _) ≫
      eqToHom (congrArg FineSaturatedLogScheme.scheme
        (P.resolution.tower C.quotient.quotient C.quotient.input).initial) ≫
      C.quotientAffine.hom
  boundary : (C.retainedBoundary.support : Set C.finalQuotient.scheme) ∩ (U : Set _) =
    U.ι '' {y | ∃ j : Fin monoids.b, j.val < monoids.c ∧
      MonoidAlgebra.single
        (monoids.coordinates.symm ⟨Multiplicative.ofAdd (0, Pi.single j 1)⟩) (1 : d.Λ) ∈
          (affine.hom y).asIdeal}


/-- Inclusion of original invariants into enlarged invariants, with its prescribed data.
Source: ILO X 1.8, (1.d)
(blueprint: lem-per-gabber-abelian-stage-toric-chart). -/
def InvariantData.includeOriginal {H : Type v} [Group H] {d : ToricData.{u, v} H}
    (e : InvariantData d) : originalInvariantMonoid d e.χ →* invariantMonoid d e.χ :=
  (d.includeP.comp (originalInvariantMonoid d e.χ).subtype).codRestrict _
    (fun r ↦ r.property)

/-- The base map of a resolved affine chart is induced by all the maps in (1.d).
Source: ILO X 1.8 (blueprint: lem-per-gabber-abelian-stage-toric-chart). -/
def ResolvedMonoid.baseMap {H : Type v} [Group H] {d : ToricData.{u, v} H}
    {e : InvariantData d} (m : ResolvedMonoid e) :
    d.Q →* retainedMonoid m.coordinates m.c :=
  ((m.ν.comp e.includeOriginal).comp e.baseMap).codRestrict _
    (fun q ↦ m.retained (e.baseMap q))

/-- A compatible coefficient map and monoid chart give their prescribed scheme map.
Source: ILO X 1.2--1.3, 1.8
(blueprint: lem-per-gabber-abelian-stage-toric-chart). -/
def chartSchemeMap {A M : Type u} [CommRing A] [CommMonoid M] {X : Scheme.{u}}
    (coeff : A →+* Γ(X, ⊤)) (β : M →* Γ(X, ⊤)) :
    X ⟶ Spec (.of (MonoidAlgebra A M)) :=
  (ΓSpec.adjunction.homEquiv X (op (.of (MonoidAlgebra A M))))
    (CommRingCat.ofHom (MonoidAlgebra.liftNCRingHom coeff β
      (fun _ _ ↦ Commute.all _ _))).op

/-- The canonical scheme comparison of a commuting log square.
Source: ILO X 1.8, strict base changes of (1.a)
(blueprint: lem-per-gabber-abelian-stage-toric-chart). -/
def squareComparison {A B C D : FineSaturatedLogScheme.{u}}
    (f : EtaleLogHom A B) (g : EtaleLogHom B D) (h : EtaleLogHom A C)
    (k : EtaleLogHom C D) (s : f.Square g h k) : A.scheme ⟶ pullback g.base k.base :=
  pullback.lift f.base h.base (by
    obtain ⟨l, hf, hh⟩ := s
    exact hf.1.trans hh.1.symm)

/-- The final map of an ordered comparison, transported along its terminal-index equation.
Source: ILO VIII 5.4.4--5.5.5
(blueprint: lem-per-gabber-abelian-stage-toric-chart). -/
def finalComparison {G H : Type v} [Group G] [Group H]
    {X Y : FineSaturatedLogScheme.{u}} {a : FSLogGroupAction G X}
    {b : FSLogGroupAction H Y} {f : EtaleLogHom Y X}
    {T : GabberModification.Tower G X a} {K : GabberModification.Tower H Y b}
    (c : GabberModification.Comparison f T K) : K.source.scheme ⟶ T.source.scheme :=
  eqToHom (congrArg (fun i ↦ (K.level i).scheme) c.last.symm) ≫
    (c.lift (Fin.last T.length)).base

/-- The relative toric construction over its sharp base chart. The base arrows and the
quotient's arrows are monomial-normalized, and the resolved affine charts cover the quotient.
Source: ILO X 1.8, diagrams (1.a)--(1.d)
(blueprint: lem-per-gabber-abelian-stage-toric-chart). -/
structure RelativeModel (P : GabberModification.FourthProcedure.{u, v})
    {H : Type v} [Group H] [Finite H] (d : ToricData.{u, v} H) (e : InvariantData d) where
  toric : ToricConstruction P d e
  sigma : FineSaturatedLogScheme.{u}
  baseAffine : sigma.scheme ≅ Spec (.of (MonoidAlgebra d.Λ d.Q))
  baseChart : d.Q →* sigma.logStructure.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 sigma.scheme)))
  baseChart_spec : IsMonomialChart sigma (Scheme.Etale.mk (𝟙 sigma.scheme)) baseChart
    (MonoidHom.id _) baseAffine.hom
  toBase : EtaleLogHom toric.Y sigma
  toBase_spec : toBase.base ≫ baseAffine.hom = toric.affine.hom ≫
    Spec.map (CommRingCat.ofHom
      (MonoidAlgebra.mapDomainRingHom d.Λ (d.includeP.comp d.γ)))
  finalToBase : EtaleLogHom toric.finalQuotient sigma
  square : (P.tower H toric.Y toric.action toric.boundary toric.input).map.Square
    toBase toric.finalMap finalToBase
  chartsCover : ∀ y : toric.finalQuotient.scheme,
    ∃ K : toric.Chart, y ∈ K.U
  chart_base : ∀ K : toric.Chart,
    K.U.ι ≫ finalToBase.base ≫ baseAffine.hom = K.affine.hom ≫
      Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapDomainRingHom d.Λ
        ((retainedMonoid K.monoids.coordinates K.monoids.c).subtype.comp
          K.monoids.baseMap)))

/-- A pointed strict inertia-preserving local comparison and its quotient after the
fourth stage. Both scheme comparisons are the canonical maps into ordinary fibre products.
The ordered tower comparison is that of the SAME global fourth-stage procedure.
Source: ILO VIII 5.3.8, 5.4.4, 5.5.5; X 1.8
(blueprint: lem-per-gabber-abelian-stage-toric-chart). -/
structure LocalModel (P : GabberModification.FourthProcedure.{u, v})
    {G : Type v} [Group G] [Finite G] {X S : FineSaturatedLogScheme.{u}}
    (a : FSLogGroupAction G X) (Z : X.scheme.IdealSheafData)
    (hX : GabberModification.AbelianInput a Z) (f : EtaleLogHom X S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X.scheme) where
  data : ToricData.{u, v} (inertia a x)
  invariants : InvariantData data
  model : RelativeModel P data invariants
  Slocal : FineSaturatedLogScheme.{u}
  toS : EtaleLogHom Slocal S
  etaleS : Etale toS.base
  strictS : toS.IsStrict
  coefficient : data.Λ →+* Γ(Slocal.scheme, ⊤)
  baseChart : data.Q →* Slocal.logStructure.monoidSheaf.obj.obj
    (op (Scheme.Etale.mk (𝟙 Slocal.scheme)))
  baseIsChart : Slocal.logStructure.IsChart (Scheme.Etale.mk (𝟙 Slocal.scheme)) baseChart
  baseMap : EtaleLogHom Slocal model.sigma
  strictBase : baseMap.IsStrict
  baseMap_spec : baseMap.base ≫ model.baseAffine.hom =
    chartSchemeMap coefficient
      ((Slocal.logStructure.alpha.app (op (Scheme.Etale.mk (𝟙 Slocal.scheme)))).hom.comp
        baseChart)
  U : FineSaturatedLogScheme.{u}
  action : FSLogGroupAction (inertia a x) U
  boundary : U.scheme.IdealSheafData
  input : GabberModification.AbelianInput action boundary
  toX : EtaleLogHom U X
  strictX : toX.IsStrict
  etaleX : Etale toX.base
  inertX : GabberModification.Inert action a (inertia a x).subtype toX
  point : Spec (.of Ω) ⟶ U.scheme
  point_over : point ≫ toX.base = x
  boundary_eq : boundary = (Z.comap toX.base).radical
  toLocalBase : EtaleLogHom U Slocal
  overS : toX.Square f toLocalBase toS
  toToric : EtaleLogHom U model.toric.Y
  strictToric : toToric.IsStrict
  inertToric : GabberModification.Inert action model.toric.action
    (MonoidHom.id (inertia a x)) toToric
  modelSquare : toToric.Square model.toBase toLocalBase baseMap
  etaleModel : Etale (squareComparison toToric model.toBase toLocalBase baseMap modelSquare)
  finalQuotient : FineSaturatedLogScheme.{u}
  finalMap : EtaleLogHom (P.tower (inertia a x) U action boundary input).source finalQuotient
  finalIsQuotient : ((P.tower (inertia a x) U action boundary input).action
    (Fin.last (P.tower (inertia a x) U action boundary input).length)).IsQuotient finalMap
  quotientToToric : EtaleLogHom finalQuotient model.toric.finalQuotient
  strictQuotient : quotientToToric.IsStrict
  quotient_eq : finalMap.base ≫ quotientToToric.base =
    finalComparison (P.comparison (inertia a x) (inertia a x) model.toric.Y U
      model.toric.action action model.toric.boundary boundary model.toric.input input
      (MonoidHom.id _) toToric strictToric inertToric) ≫ model.toric.finalMap.base
  quotientToBase : EtaleLogHom finalQuotient Slocal
  finalSquare : (P.tower (inertia a x) U action boundary input).map.Square
    toLocalBase finalMap quotientToBase
  quotientSquare : quotientToToric.Square model.finalToBase quotientToBase baseMap
  etaleQuotientModel : Etale
    (squareComparison quotientToToric model.finalToBase quotientToBase baseMap quotientSquare)
  finalEtaleX : Etale (finalComparison
    (P.comparison G (inertia a x) X U a action Z boundary hX input
      (inertia a x).subtype toX strictX inertX))

/-- The simultaneous absolute procedure admits the invariant-monoid local description
for its fourth stage, with the inverse image of the original boundary retained.
Source: ILO VIII 5.3.8, 5.4.4, 5.5.3--5.5.5; X 1.8, pp.146--148
(blueprint: lem-per-gabber-abelian-stage-toric-chart).

Proof plan:
1. Use the fixed-locus log chart at a geometric point and replace the group by its inertia.
Localize the cyclotomic ring and split the abelian representation into character lines,
using local cyclotomic group-algebra splitting and finite-projective standard free covers.
This gives Q, P, the injective base lattice map, the added eigenvector coordinates, and χ.
2. The cyclotomic ring is standard étale over Z[1/N], hence regular; localization and
polynomial-ring regularity give regular Laurent-polynomial coordinate models. Their coordinate
boundaries are strict normal crossings, hence log regular by the divisorial-chart lemma.
3. Reynolds averaging fixes a monomial exactly when its character is trivial: nontrivial
character sums vanish because 1 minus a nontrivial Nth root is a unit. Tame invariants commute
with arbitrary coefficient base change. Thus the quotient is Λ[Rbar], and the base map lands
in R. N times the ambient lattice lies in the kernel. Remainders modulo N prove finite
generation; positive-coordinate shifting identifies the group completion with the kernel;
coordinate nonnegativity proves saturation. This gives the finite invertible Kummer index.
4. Use the fixed smooth-functorial fan desingularization rule. Log-fan chart blowups and
strict fan comparison identify its local towers; functorial étale descent glues them. Each
saturated affine blowup chart preserves group completion. Free final characteristics and the
free unit lattice give Rbar' = Z^a × N^b (monoidal resolution and toric-monoid comparison).
5. The invariant power of the product of the original boundary coordinates defines the
quotient boundary. Its pullback is a monomial, so its zero set is exactly a union of coordinate
divisors. Relabel these as the first c. The regular-boundary divisorial chart is then
R' = Z^a × N^c. For g in R its zeros lie in that boundary. Pullback shows ν(g) has no positive
exponent in an omitted coordinate, proving ν(R) ⊆ R'. All arrows of (1.d) are now induced
by the actual monoid maps. The monomial basis identifies the remaining map with affine
(b-c)-space, also when c=0, c=b or b=0.
6. Tame invariants commute with the possibly nonflat strict base change from S. Very-tame
quotient log regularity and log-regular divisorial uniqueness identify the enlarged quotient's
log structure with its invariant monoid chart. Strict pullback is already fs on the ordinary
scheme fibre product. The quotient resolution tower is therefore the strict pullback of the
chosen toric tower, with the retained boundary just described.
7. The eigencharacters separate group elements by generic freeness, giving the Kummer
G-cover. Stability under fs base change identifies the pulled-back fourth stage. The inert
étale quotient-comparison theorem gives the strict étale quotient neighborhoods. The strict
inertia-preserving comparisons, their identity and composition laws, and independence from
the enlarged rigidification are those of the absolute fourth-stage procedure, so the models
and their quotients compute that globally glued fourth stage.
-/
theorem exists_abelian_stage_toric_chart :
    ∃ P : GabberModification.FourthProcedure.{u, v},
      (∃ choice : ∀ (G : Type v) [Group G] [Finite G] (X : FineSaturatedLogScheme.{u})
          (a : FSLogGroupAction G X), GabberModification.Input a →
            GabberModification.FourStage P G X a,
        ∀ (G : Type v) [Group G] [Finite G] (X : FineSaturatedLogScheme.{u})
          (a : FSLogGroupAction G X) (h : GabberModification.Input a),
          (choice G X a h).Output) ∧
      ∀ (G : Type v) [Group G] [Finite G] (X S : FineSaturatedLogScheme.{u})
        [IsIntegral X.scheme] [IsNoetherian S.scheme]
        (hS : GabberModification.QuasiExcellent S.scheme)
        (hsep : S.scheme.IsSeparated) (hlog : S.IsLogRegular)
        (a : FSLogGroupAction G X) (Z : X.scheme.IdealSheafData)
        (hX : GabberModification.AbelianInput a Z) (f : EtaleLogHom X S),
        f.IsLogSmooth → (∀ g : G, (a.logMap g).CompEq f f) →
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X.scheme),
          Nonempty (LocalModel P a Z hX f x) := by
  sorry

end AlgebraicGeometry.GabberAbelianStage
