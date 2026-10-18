/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q82
-/
module

public import Sheaf.AlgebraicGeometry.FSLogSmoothEtale
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Sheaf.AlgebraicGeometry.NormalCrossingsDivisor
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Compactification.StrictTransform
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Topology.Irreducible
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Sheaf.AlgebraicGeometry.FreeCharacteristicRegularBoundary
import Sheaf.TraceFormula.FsFaceSharpening
import Sheaf.RingTheory.ProjectiveOverLocalFree
import Sheaf.AlgebraicGeometry.BlowupChartRegularSequencePresentation
import WeilConjectures.Blowup.Affine.Defs

/-!
# Equivariant fixed-locus log charts and their coordinate blowups

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose X, Proposition 1.2,
1.3, Lemmas 1.5--1.6, and 1.7, printed pp.136--146
(blueprint: lem-per-gabber-fixed-locus-log-chart).

The coordinate monoid is multiplicatively written `Z^t + N^r`; the coefficient
ring is a localization of the cyclotomic integer ring with the group exponent
inverted. Fixed subschemes are specified by their functor of points. Blowups and
strict transforms use the existing Rees-Proj and scheme-theoretic image constructions.
- right.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.GabberFixedLocus

/-- The boundary chart, including the invertible coordinates. Source: ILO X 1.3(1.c)
(blueprint: lem-per-gabber-fixed-locus-log-chart). -/
abbrev ToricMonoid (t r : ℕ) := Multiplicative ((Fin t → ℤ) × (Fin r → ℕ))

/-- The displayed Laurent/polynomial model ring. Source: ILO X 1.7, p.144
(blueprint: lem-per-gabber-fixed-locus-log-chart). -/
abbrev ModelRing (Λ : Type u) [CommRing Λ] (t r : ℕ) (J : Type v) :=
  MvPolynomial J (MonoidAlgebra Λ (ToricMonoid t r))

/-- The canonical monomial map into the model ring. Source: ILO X 1.3(ii), 1.7
(blueprint: lem-per-gabber-fixed-locus-log-chart). -/
def monomial (Λ : Type u) [CommRing Λ] (t r : ℕ) (J : Type v) :
    ToricMonoid t r →* ModelRing Λ t r J :=
  MvPolynomial.C.toMonoidHom.comp (MonoidAlgebra.of Λ (ToricMonoid t r))

/-- The invertible coordinate `u_j`. Source: ILO X 1.7, p.144
(blueprint: lem-per-gabber-fixed-locus-log-chart). -/
def unitCoordinate (Λ : Type u) [CommRing Λ] (t r : ℕ) (J : Type v) (j : Fin t) :
    ModelRing Λ t r J :=
  monomial Λ t r J (Multiplicative.ofAdd (Pi.single j 1, 0))

/-- The boundary coordinate `z_j`. Source: ILO X 1.7, p.144
(blueprint: lem-per-gabber-fixed-locus-log-chart). -/
def boundaryCoordinate (Λ : Type u) [CommRing Λ] (t r : ℕ) (J : Type v) (j : Fin r) :
    ModelRing Λ t r J :=
  monomial Λ t r J (Multiplicative.ofAdd (0, Pi.single j 1))

/-- The ordinary polynomial coordinate `y_j`. Source: ILO X 1.7, p.144
(blueprint: lem-per-gabber-fixed-locus-log-chart). -/
def polynomialCoordinate (Λ : Type u) [CommRing Λ] (t r : ℕ) (J : Type v) (j : J) :
    ModelRing Λ t r J := MvPolynomial.X j

/-- Extension of an affine ring ideal to its canonical ideal sheaf. Source: ILO X 1.7
(blueprint: lem-per-gabber-fixed-locus-log-chart). -/
def affineIdeal {R : Type u} [CommRing R] (I : Ideal R) :
    (Spec (.of R)).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso (.of R)).inv.hom)

/-- The coordinate centre `(z_1,...,z_m,y_1,...,y_n)`, allowing empty lists.
Source: ILO X 1.7, p.144 (blueprint: lem-per-gabber-fixed-locus-log-chart). -/
def center (Λ : Type u) [CommRing Λ] (t r s m n : ℕ) :
    (Spec (.of (ModelRing Λ t r (Fin s)))).IdealSheafData :=
  affineIdeal (Ideal.span
    ({x | ∃ j : Fin r, j.val < m ∧ boundaryCoordinate Λ t r (Fin s) j = x} ∪
      {x | ∃ j : Fin s, j.val < n ∧ polynomialCoordinate Λ t r (Fin s) j = x}))

/-- The reduced coordinate boundary, with equation the product of the `z_j`.
Source: ILO X 1.7, p.145 (blueprint: lem-per-gabber-fixed-locus-log-chart). -/
def boundary (Λ : Type u) [CommRing Λ] (t r : ℕ) (J : Type v) :
    (Spec (.of (ModelRing Λ t r J))).IdealSheafData :=
  affineIdeal (Ideal.span {∏ j : Fin r, boundaryCoordinate Λ t r J j})

/-- Scheme-theoretic strict transform as a closed subscheme of the blowup, via its ideal.
Source: ILO X 1.6--1.7 (blueprint: lem-per-gabber-fixed-locus-log-chart). -/
def strictIdeal {X : Scheme.{u}} (D I : X.IdealSheafData) : I.blowup.IdealSheafData :=
  (strictTransformMap D.subschemeι I.blowupMap I.support.compl).ker

/-- The two canonical base-change assertions, with their structure maps and embedded ideals.
Source: ILO X 1.7 Claim (1.a)--(1.b)
(blueprint: lem-per-gabber-fixed-locus-log-chart). -/
def BlowupComparison {X Y : Scheme.{u}} (q : X ⟶ Y) (I D : Y.IdealSheafData) : Prop :=
  ∃ k : (I.comap q).blowup ⟶ I.blowup,
    IsPullback (I.comap q).blowupMap k q I.blowupMap ∧
      strictIdeal (D.comap q) (I.comap q) = (strictIdeal D I).comap k

/-- The simultaneous scheme-theoretic equalizer of a subgroup, tested on all schemes.
Source: ILO X 1.4--1.7 (blueprint: lem-per-gabber-fixed-locus-log-chart). -/
def IsFixedSubscheme {X F : Scheme.{u}} {G : Type v} [Group G]
    (a : G →* Aut X) (H : Subgroup G) (i : F ⟶ X) : Prop :=
  (∀ h : H, i ≫ (a h.val).hom = i) ∧
    ∀ (T : Scheme.{u}) (b : T ⟶ X),
      (∀ h : H, b ≫ (a h.val).hom = b) → ∃! k : T ⟶ F, k ≫ i = b

/-- Distinct translates of each irreducible boundary component are disjoint.
Source: ILO VIII 4.1.1, X 1.3 (blueprint: lem-per-gabber-fixed-locus-log-chart). -/
def IsGroupStrict {X : Scheme.{u}} {G : Type v} [Group G]
    (a : G →* Aut X) (D : X.IdealSheafData) : Prop :=
  ∀ C ∈ irreducibleComponents (D.support : Set X), ∀ g : G,
    (a g).hom '' (Subtype.val '' C) = Subtype.val '' C ∨
      Disjoint ((a g).hom '' (Subtype.val '' C)) (Subtype.val '' C)

/-- The beta substitution on the boundary monoid, fixing all invertible coordinates.
Source: ILO X 1.7(a), p.145 (blueprint: lem-per-gabber-fixed-locus-log-chart). -/
def beta (t r m : ℕ) (i : Fin r) : ToricMonoid t r →* ToricMonoid t r where
  toFun p := Multiplicative.ofAdd (p.toAdd.1,
    p.toAdd.2 + (∑ k ∈ Finset.univ.filter (fun k : Fin r ↦ k.val < m ∧ k ≠ i),
      p.toAdd.2 k) • Pi.single i 1)
  map_one' := by ext j <;> simp
  map_mul' p q := by ext j <;> simp [Finset.sum_add_distrib, add_smul]; omega

/-- The delta substitution: the last boundary coordinate is the exceptional `y_i`.
Source: ILO X 1.7(b), pp.145--146 (blueprint: lem-per-gabber-fixed-locus-log-chart). -/
def delta (t r m : ℕ) : ToricMonoid t r →* ToricMonoid t (r + 1) where
  toFun p := Multiplicative.ofAdd (p.toAdd.1, fun j ↦
    if h : j.val < r then p.toAdd.2 ⟨j.val, h⟩
    else ∑ k ∈ Finset.univ.filter (fun k : Fin r ↦ k.val < m), p.toAdd.2 k)
  map_one' := by ext j <;> simp
  map_mul' p q := by ext j <;> simp [Finset.sum_add_distrib]; split <;> rfl

/-- The ring substitution on the `z_i` chart, with `y_j` replaced by `z_i y'_j` for `j<n`.
Source: ILO X 1.7, Ui chart (blueprint: lem-per-gabber-fixed-locus-log-chart). -/
def zSubstitution (Λ : Type u) [CommRing Λ] (t r s m n : ℕ) (i : Fin r) :
    ModelRing Λ t r (Fin s) →+* ModelRing Λ t r (Fin s) :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C.comp (MonoidAlgebra.mapDomainRingHom Λ (beta t r m i)))
    (fun j ↦ if j.val < n then boundaryCoordinate Λ t r (Fin s) i * MvPolynomial.X j
      else MvPolynomial.X j)

/-- The ring substitution on the `y_i` chart, omitting the polynomial variable `i`.
Source: ILO X 1.7, Vi chart (blueprint: lem-per-gabber-fixed-locus-log-chart). -/
def ySubstitution (Λ : Type u) [CommRing Λ] (t r s m n : ℕ) (i : Fin s) :
    ModelRing Λ t r (Fin s) →+* ModelRing Λ t (r + 1) {j : Fin s // j ≠ i} :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C.comp (MonoidAlgebra.mapDomainRingHom Λ (delta t r m)))
    (fun j ↦ if h : j = i then boundaryCoordinate Λ t (r + 1) _ (Fin.last r)
      else if j.val < n then
        boundaryCoordinate Λ t (r + 1) _ (Fin.last r) * MvPolynomial.X ⟨j, h⟩
      else MvPolynomial.X ⟨j, h⟩)

/-- Pullback on functions expressed in the affine coordinate ring itself.
Source: ILO X 1.3(ii), 1.7 (blueprint: lem-per-gabber-fixed-locus-log-chart). -/
def affinePullback {R : Type u} [CommRing R] (g : Spec (.of R) ⟶ Spec (.of R)) : R →+* R :=
  (Scheme.ΓSpecIso (.of R)).hom.hom.comp
    (g.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)


/-- The given log structure is the divisorial one through its structural homomorphism.
Source: ILO VI 1.4, X 1.3 (blueprint: lem-per-gabber-fixed-locus-log-chart). -/
def IsDivisorial (X : FineSaturatedLogScheme.{u}) (D : X.scheme.IdealSheafData) : Prop :=
  ∀ W : X.scheme.Etale,
    Function.Injective (X.logStructure.alpha.app (op W)) ∧
      Set.range (X.logStructure.alpha.app (op W)) =
        (divisorialSections (Scheme.Opens.ι D.support.compl) W : Set Γ(W.left, ⊤))

/-- Evaluate a monoid algebra using the coefficient map and chart sections.
Source: ILO X 1.3(1.b) (blueprint: lem-per-gabber-fixed-locus-log-chart). -/
def chartRingMap {Λ A Q : Type u} [CommRing Λ] [CommRing A] [CommMonoid Q]
    (c : Λ →+* A) (b : Q →* A) : MonoidAlgebra Λ Q →+* A :=
  MonoidAlgebra.liftNCRingHom c b (fun _ _ ↦ Commute.all _ _)

/-- The scheme map prescribed by a coefficient-valued monoid chart.
Source: ILO X 1.3(1.b) (blueprint: lem-per-gabber-fixed-locus-log-chart). -/
def chartSchemeMap {W : Scheme.{u}} {Λ Q : Type u} [CommRing Λ] [CommMonoid Q]
    (c : Λ →+* Γ(W, ⊤)) (b : Q →* Γ(W, ⊤)) : W ⟶ Spec (.of (MonoidAlgebra Λ Q)) :=
  (ΓSpec.adjunction.homEquiv W (op (.of (MonoidAlgebra Λ Q))))
    (CommRingCat.ofHom (chartRingMap c b)).op

/-- The map from the affine coordinate model to its base toric scheme.
Source: ILO X 1.3(iv), 1.7 (blueprint: lem-per-gabber-fixed-locus-log-chart). -/
def modelBase {Λ Q : Type u} [CommRing Λ] [CommMonoid Q] (t r : ℕ) (J : Type)
    (γ : Q →* ToricMonoid t r) :
    Spec (.of (ModelRing Λ t r J)) ⟶ Spec (.of (MonoidAlgebra Λ Q)) :=
  Spec.map (CommRingCat.ofHom
    (MvPolynomial.C.comp (MonoidAlgebra.mapDomainRingHom Λ γ)))

/-- The canonical homomorphism on group completions of the model chart.
Source: ILO X 1.3(iv) (blueprint: lem-per-gabber-fixed-locus-log-chart). -/
def groupMap {Q : Type u} [CommMonoid Q] {t r : ℕ} (γ : Q →* ToricMonoid t r) :
    Algebra.GrothendieckGroup Q →* Algebra.GrothendieckGroup (ToricMonoid t r) :=
  Algebra.GrothendieckGroup.lift ((Algebra.GrothendieckGroup.of (M := _)).comp γ)

/-- The equivariant strict chart with a lifted geometric point. A chart by the lifted
monoid is used because the fs interface fixes the chart universe to the scheme universe.
Its map to functions is explicitly the prescribed monomial map, so no alternative
log structure or arbitrary comparison map is substituted.
Source: ILO X 1.2--1.3 (blueprint: lem-per-gabber-fixed-locus-log-chart). -/
structure LocalChart {X S : FineSaturatedLogScheme.{u}} (f : EtaleLogHom X S)
    {G : Type v} [Group G] (a : G →* Aut X.scheme)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X.scheme)
    (Λ Q : Type u) [CommRing Λ] [CommMonoid Q] (t r s : ℕ)
    (γ : Q →* ToricMonoid t r) where
  W : S.scheme.Etale
  V : X.scheme.Etale
  point : Spec (.of Ω) ⟶ V.left
  point_over : point ≫ V.hom = x
  toBase : V.left ⟶ W.left
  over : toBase ≫ W.hom = V.hom ≫ f.base
  baseChart : Q →* S.logStructure.monoidSheaf.obj.obj (op W)
  base_isChart : S.logStructure.IsChart W baseChart
  sharp_at_point : ∀ q : Q,
    IsUnit (S.logStructure.toEtalePrelogStructure.stalkAlpha (x ≫ f.base)
      (S.logStructure.toEtalePrelogStructure.germ (x ≫ f.base) W
        (Over.homMk (point ≫ toBase) (by
          change (point ≫ toBase) ≫ W.hom = x ≫ f.base
          rw [Category.assoc, over, ← Category.assoc, point_over]))
        (baseChart q))) → q = 1
  coefficient : Λ →+* Γ(W.left, ⊤)
  toModel : V.left ⟶ Spec (.of (ModelRing Λ t r (Fin s)))
  square : toBase ≫ chartSchemeMap coefficient
      ((S.logStructure.alpha.app (op W)).hom.comp baseChart) =
    toModel ≫ modelBase t r (Fin s) γ
  sourceChart : ULift.{u} (ToricMonoid t r) →*
    X.logStructure.monoidSheaf.obj.obj (op V)
  source_isChart : X.logStructure.IsChart V sourceChart
  source_alpha : ∀ p : ULift.{u} (ToricMonoid t r),
    X.logStructure.alpha.app (op V) (sourceChart p) =
      toModel.appTop ((Scheme.ΓSpecIso (.of (ModelRing Λ t r (Fin s)))).inv
        (monomial Λ t r (Fin s) p.down))
  compatibility : ∀ q : Q,
    f.sectionMap W V toBase over (baseChart q) = sourceChart ⟨γ q⟩
  sourceAction : G →* Aut V.left
  point_inertia : ∀ g : G, point ≫ (sourceAction g).hom = point
  action_over : ∀ g : G, (sourceAction g).hom ≫ V.hom = V.hom ≫ (a g).hom
  base_invariant : ∀ g : G, (sourceAction g).hom ≫ toBase = toBase
  modelAction : G →* Aut (Spec (.of (ModelRing Λ t r (Fin s))))
  equivariant : ∀ g : G,
    (sourceAction g).hom ≫ toModel = toModel ≫ (modelAction g).hom
  model_over : ∀ g : G,
    (modelAction g).hom ≫ modelBase t r (Fin s) γ = modelBase t r (Fin s) γ
  coefficient_fixed : ∀ (g : G) (b : Λ),
    affinePullback (modelAction g).hom (MvPolynomial.C (MonoidAlgebra.single 1 b)) =
      MvPolynomial.C (MonoidAlgebra.single 1 b)
  units_fixed : ∀ (g : G) (j : Fin t),
    affinePullback (modelAction g).hom (unitCoordinate Λ t r (Fin s) j) =
      unitCoordinate Λ t r (Fin s) j
  character : Fin r → G →* Λˣ
  eigenvectors : ∀ (g : G) (j : Fin r),
    affinePullback (modelAction g).hom (boundaryCoordinate Λ t r (Fin s) j) =
      MvPolynomial.C (MonoidAlgebra.single 1 (character j g : Λ)) *
        boundaryCoordinate Λ t r (Fin s) j
  linear : ∀ (g : G) (j : Fin s), ∃ b : Fin s → Λ,
    affinePullback (modelAction g).hom (polynomialCoordinate Λ t r (Fin s) j) =
      ∑ k : Fin s, MvPolynomial.C (MonoidAlgebra.single 1 (b k)) * MvPolynomial.X k

/-- The canonical comparison to the base change of the coordinate model.
Source: ILO X 1.3(1.b) (blueprint: lem-per-gabber-fixed-locus-log-chart). -/
def LocalChart.comparison {X S : FineSaturatedLogScheme.{u}} {f : EtaleLogHom X S}
    {G : Type v} [Group G] {a : G →* Aut X.scheme}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {x : Spec (.of Ω) ⟶ X.scheme}
    {Λ Q : Type u} [CommRing Λ] [CommMonoid Q] {t r s : ℕ}
    {γ : Q →* ToricMonoid t r} (c : LocalChart f a x Λ Q t r s γ) :
    c.V.left ⟶ pullback
      (chartSchemeMap c.coefficient ((S.logStructure.alpha.app (op c.W)).hom.comp c.baseChart))
      (modelBase t r (Fin s) γ) :=
  pullback.lift c.toBase c.toModel c.square

/-- The explicit chart cover of the Rees blowup. The exceptional and strict ideals are
specified separately, hence also specify their union. Polynomial variables outside the
boundary monoid are exactly the indices in the displayed model rings.
Source: ILO X 1.7(a)--(b), pp.144--146
(blueprint: lem-per-gabber-fixed-locus-log-chart). -/
structure BlowupCharts (Λ : Type u) [CommRing Λ] (t r s m n : ℕ) where
  zChart : ∀ _i : {i : Fin r // i.val < m},
    Spec (.of (ModelRing Λ t r (Fin s))) ⟶ (center Λ t r s m n).blowup
  yChart : ∀ i : {i : Fin s // i.val < n},
    Spec (.of (ModelRing Λ t (r + 1) {j : Fin s // j ≠ i.val})) ⟶
      (center Λ t r s m n).blowup
  z_open : ∀ i, IsOpenImmersion (zChart i)
  y_open : ∀ i, IsOpenImmersion (yChart i)
  z_map : ∀ i, zChart i ≫ (center Λ t r s m n).blowupMap =
    Spec.map (CommRingCat.ofHom (zSubstitution Λ t r s m n i.val))
  y_map : ∀ i, yChart i ≫ (center Λ t r s m n).blowupMap =
    Spec.map (CommRingCat.ofHom (ySubstitution Λ t r s m n i.val))
  covers : ∀ b : (center Λ t r s m n).blowup,
    (∃ i, ∃ z, zChart i z = b) ∨ (∃ i, ∃ z, yChart i z = b)
  z_exceptional : ∀ i,
    ((center Λ t r s m n).comap (center Λ t r s m n).blowupMap).comap (zChart i) =
      affineIdeal (Ideal.span {boundaryCoordinate Λ t r (Fin s) i.val})
  z_strict : ∀ i,
    (strictIdeal (boundary Λ t r (Fin s)) (center Λ t r s m n)).comap (zChart i) =
      affineIdeal (Ideal.span {∏ j ∈ Finset.univ.erase i.val,
        boundaryCoordinate Λ t r (Fin s) j})
  y_exceptional : ∀ i,
    ((center Λ t r s m n).comap (center Λ t r s m n).blowupMap).comap (yChart i) =
      affineIdeal (Ideal.span {boundaryCoordinate Λ t (r + 1)
        {j : Fin s // j ≠ i.val} (Fin.last r)})
  y_strict : ∀ i,
    (strictIdeal (boundary Λ t r (Fin s)) (center Λ t r s m n)).comap (yChart i) =
      affineIdeal (Ideal.span {∏ j : Fin r,
        boundaryCoordinate Λ t (r + 1) {j : Fin s // j ≠ i.val} j.castSucc})


/-- The two explicit base monoid maps on the blowup charts. They are equations of
scheme morphisms, retaining the original map `gamma` and the canonical blowup projection.
Source: ILO X 1.7(a)--(b), pp.145--146
(blueprint: lem-per-gabber-fixed-locus-log-chart). -/
def BlowupCharts.BaseMaps {Λ Q : Type u} [CommRing Λ] [CommMonoid Q]
    {t r s m n : ℕ} (c : BlowupCharts Λ t r s m n) (γ : Q →* ToricMonoid t r) : Prop :=
  (∀ i, c.zChart i ≫ (center Λ t r s m n).blowupMap ≫ modelBase t r (Fin s) γ =
    modelBase t r (Fin s) ((beta t r m i.val).comp γ)) ∧
  (∀ i, c.yChart i ≫ (center Λ t r s m n).blowupMap ≫ modelBase t r (Fin s) γ =
    modelBase t (r + 1) {j : Fin s // j ≠ i.val} ((delta t r m).comp γ))

/-- Gabber's fixed-locus local model and its blowup charts.
Source: ILO X Proposition 1.2, 1.3, Lemmas 1.5--1.6 and 1.7, pp.136--146
(blueprint: lem-per-gabber-fixed-locus-log-chart).

Proof:
1. Tameness makes the inertia order invertible. Since the base action is trivial,
choose its sharp equivariant chart by lem-per-very-tame-equivariant-sharp-chart.
Group-strictness fixes every boundary branch through the geometric point.
The regular-boundary criterion lem-trf-free-characteristic-regular-boundary identifies
its characteristic monoid with N^r.
2. Apply lem-per-equivariant-log-smooth-chart. Localize its fs monoid along the unit face,
using lem-trf-fs-face-sharpening. Saturation and torsion-free units make its group
completion torsion free; lem-trf-fine-monoid-unit-splitting then gives Z^t + N^r.
Inertia fixes every unit monomial: its value at the fixed geometric point is nonzero,
and distinct invertible-order roots of unity have distinct residues.
3. Apply lem-per-tame-smooth-representation-chart to the remaining smooth comparison.
Localize the coefficient ring to make the finite projective representation free.
For H, average by its invertible order. The image and kernel of the averaging
idempotent split the representation; lem-trf-projective-over-local-free supplies bases
on a coefficient neighborhood. The kernel is generated by differences (h-1)v.
Thus the fixed ideal is precisely the first n y-coordinates and the z-coordinates
with nontrivial H-character, which can be numbered first. This is the equalizer
ideal, not the invariant subring.
4. The fixed-locus comparison becomes cartesian after shrinking: equalizers of
lifts along an etale map are open and contain the chosen point. Intersect the
finitely many translates. The fixed locus also commutes with the base pullback,
since the action on the base is trivial. Strictness identifies both boundary ideals.
5. Lem-per-log-regular-chart-monomial-tor gives Tor independence for the fixed ideal,
every boundary intersection, and their intersections. These are regular coordinate
immersions. Lem-per-tor-independent-blowup-transform therefore gives the two
base-change isomorphisms, without assuming the model projection flat. Pulling
back along the etale comparison gives the same assertions on its source.
6. Omit the operation when m+n=0. Otherwise apply
lem-trf-blowup-chart-regular-sequence-presentation and
lemma-nagata-rees-generators-cover-proj. Eliminating the old coordinates gives the
Ui and Vi model rings and exactly zSubstitution and ySubstitution.
7. On Ui the exceptional equation is z_i, and saturation by z_i leaves the product
of all other boundary coordinates. Including the exceptional component gives N^r;
the monomial substitution is beta composed with gamma.
8. On Vi the exceptional equation is y_i, and saturation by y_i leaves the product
of all r strict boundary coordinates. Including the exceptional component gives
N^(r+1); the monomial substitution is delta composed with gamma. Polynomial
expansion proves these saturation statements, including all empty products.
-/
theorem exists_fixed_locus_log_chart
    (X S : FineSaturatedLogScheme.{u}) [IsNoetherian X.scheme] [IsNoetherian S.scheme]
    (_hregular : IsRegularScheme X.scheme)
    (Z : X.scheme.IdealSheafData) (D : S.scheme.IdealSheafData)
    (_hX : X.IsLogRegular) (_hS : S.IsLogRegular)
    (_hXZ : IsDivisorial X Z) (_hSD : IsDivisorial S D)
    (_hZ : IsStrictNormalCrossingsBoundary Z) (_hZn : Z.IsNormalCrossingsDivisor)
    (f : EtaleLogHom X S) (_hf : f.IsLogSmooth)
    (G : Type v) [Group G] [Finite G] (a : G →* Aut X.scheme)
    (_hover : ∀ g : G, (a g).hom ≫ f.base = f.base)
    (_hpreserve : ∀ g : G, Z.comap (a g).hom = Z)
    (_hstrict : IsGroupStrict a Z)
    (_htame : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (b : Spec (.of K) ⟶ X.scheme),
      IsUnit (Nat.card {g : G // b ≫ (a g).hom = b} :
        X.scheme.presheaf.stalk (b default)))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X.scheme)
    (_hinertia : ∀ g : G, x ≫ (a g).hom = x) (H : Subgroup G) :
    ∃ (N : ℕ) (_hN : 0 < N) (Λ : Type u) (_ : CommRing Λ)
      (_ : Algebra (CyclotomicRing N ℤ ℚ) Λ) (M : Submonoid (CyclotomicRing N ℤ ℚ)),
      IsLocalization M Λ ∧ (N : CyclotomicRing N ℤ ℚ) ∈ M ∧
      (∀ g : G, g ^ N = 1) ∧
      ∃ (Q : Type u) (_ : CommMonoid Q), IsFineSaturatedMonoid Q ∧
      (∀ q : Q, IsUnit q → q = 1) ∧
      ∃ (t r s m n : ℕ) (γ : Q →* ToricMonoid t r),
        m ≤ r ∧ n ≤ s ∧ Function.Injective (groupMap γ) ∧
        Finite (CommGroup.torsion
          (Algebra.GrothendieckGroup (ToricMonoid t r) ⧸ (groupMap γ).range)) ∧
        IsUnit (Nat.card (CommGroup.torsion
          (Algebra.GrothendieckGroup (ToricMonoid t r) ⧸ (groupMap γ).range)) : Λ) ∧
        ∃ c : LocalChart f a x Λ Q t r s γ,
          Etale c.comparison ∧
          Z.comap c.V.hom = (boundary Λ t r (Fin s)).comap c.toModel ∧
          IsFixedSubscheme c.modelAction H (center Λ t r s m n).subschemeι ∧
          IsFixedSubscheme c.sourceAction H
            ((center Λ t r s m n).comap c.toModel).subschemeι ∧
          (0 < m + n →
            BlowupComparison
              (pullback.snd
                (chartSchemeMap c.coefficient
                  ((S.logStructure.alpha.app (op c.W)).hom.comp c.baseChart))
                (modelBase t r (Fin s) γ))
              (center Λ t r s m n) (boundary Λ t r (Fin s)) ∧
            BlowupComparison c.toModel (center Λ t r s m n) (boundary Λ t r (Fin s)) ∧
            ∃ b : BlowupCharts Λ t r s m n, b.BaseMaps γ) := by
  sorry

end AlgebraicGeometry.GabberFixedLocus
