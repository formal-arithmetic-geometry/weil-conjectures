module

public import Sheaf.AlgebraicGeometry.LogMorphismOperations
public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.FSLogSmoothEtale
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Finite Kummer étale G-covers

Source: ILO VI 2.1--2.3, printed pp.71--73
(blueprint: def-per-kummer-etale-g-cover).

The torsor diagonal is a pullback cone whose vertex is the categorical disjoint union
of copies of the source, with the prescribed identity and deck-action projections.
The full fs category and its compatible chart family are included here so arbitrary
fs base changes may be non-Noetherian. The original locally Noetherian dependency
interfaces and their node records remain intact. Chart structural maps reuse
`EtaleLogStructure.chartToSpec`, and identity/composition reuse `EtaleLogMap`.

`EtaleLogHom.IsKummer` from def-per-kummer-log-morphism requires locally Noetherian
bundles. Here the injective positive-power chart criterion of ILO VI 2.1--2.2
expresses Kummer etaleness for unrestricted fs bases, as arbitrary fs base change
requires. It does not define another characteristic-stalk Kummer predicate.
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- An fs log scheme without a Noetherianity restriction. Source: ILO VI 2.1--2.2
(blueprint: def-per-kummer-etale-g-cover). -/
structure FSLogScheme where
  scheme : Scheme.{u}
  logStructure : EtaleLogStructure scheme
  fineSaturated : logStructure.IsFineSaturated

/-- The category uses the already constructed log-map identity and composition.
Source: ILO VI 1.1, 2.2 (blueprint: def-per-kummer-etale-g-cover). -/
noncomputable instance fsLogSchemeCategory : Category FSLogScheme.{u} where
  Hom X Y := EtaleLogMap X.logStructure Y.logStructure
  id X := EtaleLogMap.id X.logStructure
  comp f g := f.comp g
  id_comp := EtaleLogMap.id_comp
  comp_id := EtaleLogMap.comp_id
  assoc := EtaleLogMap.comp_assoc

/-- Forget only the log structure. Source: ILO VI 1.1
(blueprint: def-per-kummer-etale-g-cover). -/
noncomputable def FSLogScheme.forget : FSLogScheme.{u} ⥤ Scheme.{u} where
  obj X := X.scheme
  map f := f.base
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The original locally Noetherian bundle as an object of the full fs category.
Source: ILO VI 1.1 (blueprint: def-per-kummer-etale-g-cover). -/
def FineSaturatedLogScheme.toFSLogScheme (X : FineSaturatedLogScheme.{u}) : FSLogScheme.{u} :=
  ⟨X.scheme, X.logStructure, X.fineSaturated⟩

/-- Add a supplied local Noetherianity proof without changing any log data.
Source: ILO VI 1.1 (blueprint: def-per-kummer-etale-g-cover). -/
def FSLogScheme.locallyNoetherian (X : FSLogScheme.{u})
    (h : IsLocallyNoetherian X.scheme) : FineSaturatedLogScheme.{u} :=
  ⟨X.scheme, h, X.logStructure, X.fineSaturated⟩

/-- One compatible fs chart square over a log morphism. The last equation is the
commutativity of the canonical chart scheme maps; it expresses the square from the
node, with no chosen unrelated maps to spectra. Source: ILO X 1.2 and XVI 3.6.3
(blueprint: def-per-kummer-etale-g-cover). -/
structure FSLogScheme.Chart {X Y : FSLogScheme.{u}} (f : X ⟶ Y) where
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

attribute [instance] FSLogScheme.Chart.instP FSLogScheme.Chart.instQ

/-- The canonical comparison `(fᵢ,aᵢ)` to the scheme fibre product.
Source: ILO X 1.2 and XVI 3.6.3 (blueprint: def-per-kummer-etale-g-cover). -/
noncomputable def FSLogScheme.Chart.comparison {X Y : FSLogScheme.{u}}
    {f : X ⟶ Y} (c : FSLogScheme.Chart f) :
    c.V.left ⟶ pullback (Y.logStructure.chartToSpec c.W c.chartY)
      (Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapDomainRingHom ℤ c.g))) :=
  pullback.lift c.map (X.logStructure.chartToSpec c.V c.chartX) c.square

/-- The induced homomorphism on the canonical group completions.
Source: Kato Theorem 3.5, recalled in ILO X 1.2
(blueprint: def-per-kummer-etale-g-cover). -/
noncomputable def FSLogScheme.Chart.groupMap {X Y : FSLogScheme.{u}}
    {f : X ⟶ Y} (c : FSLogScheme.Chart f) :
    Algebra.GrothendieckGroup c.P →* Algebra.GrothendieckGroup c.Q :=
  Algebra.GrothendieckGroup.lift ((Algebra.GrothendieckGroup.of (M := c.Q)).comp c.g)

/-- The whole group cokernel, without discarding its free part.
Source: Kato Theorem 3.5, recalled in ILO X 1.2
(blueprint: def-per-kummer-etale-g-cover). -/
noncomputable abbrev FSLogScheme.Chart.cokernel {X Y : FSLogScheme.{u}}
    {f : X ⟶ Y} (c : FSLogScheme.Chart f) :=
  Algebra.GrothendieckGroup c.Q ⧸ c.groupMap.range

/-- A log-smooth chart has finite kernel and torsion cokernel of locally invertible
orders, and smooth canonical comparison. The unit tests are in every ordinary local
ring of the chart source. Source: Kato Theorem 3.5 and ILO X 1.2
(blueprint: def-per-kummer-etale-g-cover). -/
noncomputable def FSLogScheme.Chart.IsSmoothChart {X Y : FSLogScheme.{u}}
    {f : X ⟶ Y} (c : FSLogScheme.Chart f) : Prop :=
  Finite c.groupMap.ker ∧ Finite (CommGroup.torsion c.cokernel) ∧
    (∀ x : c.V.left,
      IsUnit ((Nat.card c.groupMap.ker : ℕ) : c.V.left.presheaf.stalk x) ∧
      IsUnit ((Nat.card (CommGroup.torsion c.cokernel) : ℕ) : c.V.left.presheaf.stalk x)) ∧
    Smooth c.comparison

/-- A log-étale chart requires the whole cokernel to be finite of locally invertible
order and the canonical comparison to be étale. Source: Kato Theorem 3.5
(blueprint: def-per-kummer-etale-g-cover). -/
noncomputable def FSLogScheme.Chart.IsEtaleChart {X Y : FSLogScheme.{u}}
    {f : X ⟶ Y} (c : FSLogScheme.Chart f) : Prop :=
  Finite c.groupMap.ker ∧ Finite c.cokernel ∧
    (∀ x : c.V.left,
      IsUnit ((Nat.card c.groupMap.ker : ℕ) : c.V.left.presheaf.stalk x) ∧
      IsUnit ((Nat.card c.cokernel : ℕ) : c.V.left.presheaf.stalk x)) ∧
    Etale c.comparison

/-- Log smoothness: compatible smooth fs charts cover the source. Pointwise existence
is equivalent to existence of a covering family of these charts. Source: ILO X 1.2,
XVI 3.6.1--3.6.3; Kato Theorem 3.5 (blueprint: def-per-kummer-etale-g-cover). -/
noncomputable def FSLogScheme.IsLogSmooth {X Y : FSLogScheme.{u}}
    (f : X ⟶ Y) : Prop :=
  ∀ x : X.scheme, ∃ c : FSLogScheme.Chart f, x ∈ Set.range c.V.hom ∧ c.IsSmoothChart

/-- Log étaleness: compatible étale fs charts with finite whole cokernels cover the
source. Empty sources are allowed. Source: Kato Theorem 3.5; ILO XVI 3.6.1--3.6.3
(blueprint: def-per-kummer-etale-g-cover). -/
noncomputable def FSLogScheme.IsLogEtale {X Y : FSLogScheme.{u}}
    (f : X ⟶ Y) : Prop :=
  ∀ x : X.scheme, ∃ c : FSLogScheme.Chart f, x ∈ Set.range c.V.hom ∧ c.IsEtaleChart

/-- Kummer étaleness means covering compatible injective Kummer fs charts, with finite
invertible group cokernel and étale canonical comparison. Source: ILO VI 2.1--2.2
(blueprint: def-per-kummer-etale-g-cover). -/
noncomputable def FSLogScheme.IsKummerEtale {X Y : FSLogScheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ x : X.scheme, ∃ c : FSLogScheme.Chart f,
    x ∈ Set.range c.V.hom ∧ c.IsEtaleChart ∧ Function.Injective c.g ∧
      ∀ q : c.Q, ∃ (n : ℕ) (p : c.P), 0 < n ∧ q ^ n = c.g p

/-- A finite surjective Kummer étale G-cover, retaining the original action.
The canonical diagonal from the disjoint union is an fs pullback, and its two
projections on the g-th summand are the identity and g. This is precisely the
isomorphism `coprod_G X ≅ X ×_Y^fs X`, without choosing either object in advance.
Source: ILO VI 2.1--2.3 (blueprint: def-per-kummer-etale-g-cover). -/
noncomputable def FSLogScheme.IsKummerEtaleGCover {G : Type v} [Group G] [Finite G]
    {X Y : FSLogScheme.{u}} (f : X ⟶ Y) (a : G → (X ⟶ X)) : Prop :=
  FSLogScheme.IsKummerEtale f ∧ IsFinite f.base ∧ Surjective f.base ∧
    (a 1 = 𝟙 X) ∧ (∀ g h : G, a h ≫ a g = a (g * h)) ∧
    (∀ g : G, a g ≫ f = f) ∧
    ∃ (C : FSLogScheme.{u}) (i : G → (X ⟶ C)) (p₁ p₂ : C ⟶ X),
      Nonempty (IsColimit (Cofan.mk C i)) ∧ IsPullback p₁ p₂ f f ∧
        ∀ g : G, i g ≫ p₁ = 𝟙 X ∧ i g ≫ p₂ = a g

end AlgebraicGeometry
