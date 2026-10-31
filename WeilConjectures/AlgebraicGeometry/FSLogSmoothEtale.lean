/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FineSaturatedLogBlowup
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.GroupTheory.Torsion

/-!
# Log smooth and log étale morphisms of fs log schemes

Source: ILO, Exposé X Proposition 1.2, pp.136--138; Exposé XVI 3.6.1--3.6.3,
p.252; Kato, Logarithmic structures of Fontaine--Illusie, Theorem 3.5
(blueprint: def-per-fs-log-smooth-etale).

We use the multiplicative notation of the existing fs log interface: `1`, products,
and powers represent the node's `0`, sums, and integer multiples. Monoid rings are
Mathlib's finite-support `MonoidAlgebra ℤ P`. Chart maps to spectra are constructed
by the global-sections adjunction, and the comparison is the canonical pullback lift.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The scheme map of a monoid chart, sending each monomial to its structural image.
Source: ILO X 1.2; the global-sections--spectrum adjunction
(blueprint: def-per-fs-log-smooth-etale). -/
noncomputable def EtaleLogStructure.chartToSpec {X : Scheme.{u}} (M : EtaleLogStructure X)
    (W : X.Etale) {P : Type u} [CommMonoid P]
    (β : P →* M.monoidSheaf.obj.obj (op W)) :
    W.left ⟶ Spec (.of (MonoidAlgebra ℤ P)) :=
  (ΓSpec.adjunction.homEquiv W.left (op (.of (MonoidAlgebra ℤ P))))
    (CommRingCat.ofHom (MonoidAlgebra.lift ℤ Γ(W.left, ⊤) P
      ((M.alpha.app (op W)).hom.comp β)).toRingHom).op

/-- One compatible fs chart square over a log morphism. The last equation is the
commutativity of the canonical chart scheme maps; it expresses the square from the
node, with no chosen unrelated maps to spectra. Source: ILO X 1.2 and XVI 3.6.3
(blueprint: def-per-fs-log-smooth-etale). -/
structure FSLogChart {X Y : FineSaturatedLogScheme.{u}} (f : EtaleLogHom X Y) where
  W : Y.scheme.Etale
  V : X.scheme.Etale
  P : Type u
  Q : Type u
  instP : CommMonoid P
  instQ : CommMonoid Q
  fineP : @IsFineSaturatedMonoid P instP
  fineQ : @IsFineSaturatedMonoid Q instQ
  chartY : P →* Y.logStructure.monoidSheaf.obj.obj (op W)
  chartX : Q →* X.logStructure.monoidSheaf.obj.obj (op V)
  g : P →* Q
  chartY_isChart : Y.logStructure.IsChart W chartY
  chartX_isChart : X.logStructure.IsChart V chartX
  map : V.left ⟶ W.left
  map_over : map ≫ W.hom = V.hom ≫ f.base
  chart_compatibility : ∀ p : P,
    f.sectionMap W V map map_over (chartY p) = chartX (g p)
  square : map ≫ Y.logStructure.chartToSpec W chartY =
    X.logStructure.chartToSpec V chartX ≫
      Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapDomainRingHom ℤ g))

attribute [instance] FSLogChart.instP FSLogChart.instQ

/-- The canonical comparison `(fᵢ,aᵢ)` to the scheme fibre product.
Source: ILO X 1.2 and XVI 3.6.3 (blueprint: def-per-fs-log-smooth-etale). -/
noncomputable def FSLogChart.comparison {X Y : FineSaturatedLogScheme.{u}}
    {f : EtaleLogHom X Y} (c : FSLogChart f) :
    c.V.left ⟶ pullback (Y.logStructure.chartToSpec c.W c.chartY)
      (Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapDomainRingHom ℤ c.g))) :=
  pullback.lift c.map (X.logStructure.chartToSpec c.V c.chartX) c.square

/-- The induced homomorphism on the canonical group completions.
Source: Kato Theorem 3.5, recalled in ILO X 1.2
(blueprint: def-per-fs-log-smooth-etale). -/
noncomputable def FSLogChart.groupMap {X Y : FineSaturatedLogScheme.{u}}
    {f : EtaleLogHom X Y} (c : FSLogChart f) :
    Algebra.GrothendieckGroup c.P →* Algebra.GrothendieckGroup c.Q :=
  Algebra.GrothendieckGroup.lift ((Algebra.GrothendieckGroup.of (M := c.Q)).comp c.g)

/-- The whole group cokernel, without discarding its free part.
Source: Kato Theorem 3.5, recalled in ILO X 1.2
(blueprint: def-per-fs-log-smooth-etale). -/
noncomputable abbrev FSLogChart.cokernel {X Y : FineSaturatedLogScheme.{u}}
    {f : EtaleLogHom X Y} (c : FSLogChart f) :=
  Algebra.GrothendieckGroup c.Q ⧸ c.groupMap.range

/-- A log-smooth chart has finite kernel and torsion cokernel of locally invertible
orders, and smooth canonical comparison. The unit tests are in every ordinary local
ring of the chart source. Source: Kato Theorem 3.5 and ILO X 1.2
(blueprint: def-per-fs-log-smooth-etale). -/
noncomputable def FSLogChart.IsSmoothChart {X Y : FineSaturatedLogScheme.{u}}
    {f : EtaleLogHom X Y} (c : FSLogChart f) : Prop :=
  Finite c.groupMap.ker ∧ Finite (CommGroup.torsion c.cokernel) ∧
    (∀ x : c.V.left,
      IsUnit ((Nat.card c.groupMap.ker : ℕ) : c.V.left.presheaf.stalk x) ∧
      IsUnit ((Nat.card (CommGroup.torsion c.cokernel) : ℕ) : c.V.left.presheaf.stalk x)) ∧
    Smooth c.comparison

/-- A log-étale chart requires the whole cokernel to be finite of locally invertible
order and the canonical comparison to be étale. Source: Kato Theorem 3.5
(blueprint: def-per-fs-log-smooth-etale). -/
noncomputable def FSLogChart.IsEtaleChart {X Y : FineSaturatedLogScheme.{u}}
    {f : EtaleLogHom X Y} (c : FSLogChart f) : Prop :=
  Finite c.groupMap.ker ∧ Finite c.cokernel ∧
    (∀ x : c.V.left,
      IsUnit ((Nat.card c.groupMap.ker : ℕ) : c.V.left.presheaf.stalk x) ∧
      IsUnit ((Nat.card c.cokernel : ℕ) : c.V.left.presheaf.stalk x)) ∧
    Etale c.comparison

/-- Log smoothness: compatible smooth fs charts cover the source. Pointwise existence
is equivalent to existence of a covering family of these charts. Source: ILO X 1.2,
XVI 3.6.1--3.6.3; Kato Theorem 3.5 (blueprint: def-per-fs-log-smooth-etale). -/
noncomputable def EtaleLogHom.IsLogSmooth {X Y : FineSaturatedLogScheme.{u}}
    (f : EtaleLogHom X Y) : Prop :=
  ∀ x : X.scheme, ∃ c : FSLogChart f, x ∈ Set.range c.V.hom ∧ c.IsSmoothChart

/-- Log étaleness: compatible étale fs charts with finite whole cokernels cover the
source. Empty sources are allowed. Source: Kato Theorem 3.5; ILO XVI 3.6.1--3.6.3
(blueprint: def-per-fs-log-smooth-etale). -/
noncomputable def EtaleLogHom.IsLogEtale {X Y : FineSaturatedLogScheme.{u}}
    (f : EtaleLogHom X Y) : Prop :=
  ∀ x : X.scheme, ∃ c : FSLogChart f, x ∈ Set.range c.V.hom ∧ c.IsEtaleChart

end AlgebraicGeometry
