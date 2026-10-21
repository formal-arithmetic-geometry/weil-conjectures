/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.SixFunctors.SchemeFrobenius
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.Paper.CoefTowerCoaugmentation
public import Sheaf.Paper.PointProEtaleSectionsExact
public import Sheaf.Paper.PointSystemTransportDescent
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.CategoryTheory.StrictRoosComparison
public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.Paper.ExactProductFunctorStrictLimit
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition
import Sheaf.AlgebraicGeometry.PointSheafInsertionCalculus
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.Paper.ExactProductFunctorRoosChainMaps

/-! # Power coherence of point transport and the entire Roos comparison

Source: blueprint main-20261015, trace-transport proof, Step 1, Global powers;
`prop-trf-rational-frobenius-integral-model`, proof (3); Stacks Tags 03CB, 0H7J, 0941
(blueprint: lem-trf-point-system-power-roos-coherence).

All system categories, inverse images, scalar restrictions and transports are the
recorded constructions. The auxiliary data below specify the canonical maps on
sections and on both signed Roos coordinates. No arbitrary derived comparison is
used, and no boundedness, constructibility or normalization of the input is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PointSystemTransport
namespace PowerRoos

variable (D : FiniteFieldDatum.{t}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The recorded completed-coefficient module inverse image, with its actual scalar map.
Source: Stacks 03D6, 03CO (blueprint: lem-trf-point-system-power-roos-coherence). -/
abbrev F (r : ℕ) := inverseImageIntegralModules l E (pointPower D r).hom

/-- Termwise inverse image on unbounded complexes.
Source: Stacks 015F (blueprint: lem-trf-point-system-power-roos-coherence). -/
abbrev Fc (r : ℕ) := (F D l E r).mapHomologicalComplex (.up ℤ)

/-- Inverse image on entire completed-module towers.
Source: Stacks 0941 (blueprint: lem-trf-point-system-power-roos-coherence). -/
abbrev Ft (r : ℕ) := (Functor.whiskeringRight ℕᵒᵖ _ _).obj (F D l E r)

/-- The recorded levelwise scalar restriction on system complexes.
Source: Stacks 0941 (blueprint: lem-trf-point-system-power-roos-coherence). -/
abbrev Uc := (coefficientSequenceRestriction l E (Spec (.of D.k))).mapHomologicalComplex (.up ℤ)

/-- The recorded strict system inverse image on complexes.
Source: Stacks 015F (blueprint: lem-trf-point-system-power-roos-coherence). -/
abbrev Gc (r : ℕ) := (pull D l E r).mapHomologicalComplex (.up ℤ)

/-- The signed coordinates (x,y)=(u,-v) on the actual shifted cone, in that order.
Source: Stacks 0941 and exact-product strict-limit normalization
(blueprint: lem-trf-point-system-power-roos-coherence). -/
def coordinates (X : CochainComplex
    (ℕᵒᵖ ⥤ scalarReductionSource l E (Spec (.of D.k))) ℤ) (p : ℤ) :
    (roosF.obj X).X (p + 1) ⟶ (roosP X).X (p + 1) ⊞ (roosP X).X p :=
  (roosχ X p).hom ≫ (biprod.braiding _ _).hom ≫ biprod.map (𝟙 _) (-𝟙 _)

/-- The normalized site and whole-system compositors, including finite tensor units.
The section equations uniquely prescribe their underlying maps; HEq transports only
between the canonically equal direct and twice-postcomposed site objects.
Source: Stacks 03CB, 0H7J, 03D3 and blueprint Global powers
(blueprint: lem-trf-point-system-power-roos-coherence). -/
structure Compositors where
  /-- Canonical completed-module compositor. -/
  d : ∀ m : ℕ, F D l E m ⋙ F D l E 1 ≅ F D l E (m + 1)
  /-- Canonical whole-system compositor. -/
  t : ∀ m : ℕ, pull D l E m ⋙ pull D l E 1 ≅ pull D l E (m + 1)
  /-- Scalar restriction comparison. -/
  b : ∀ r : ℕ,
    coefficientSequenceRestriction l E (Spec (.of D.k)) ⋙ Ft D l E r ≅
      pull D l E r ⋙ coefficientSequenceRestriction l E (Spec (.of D.k))
  /-- Canonical finite tensor compositor. -/
  tensor : ∀ m n : ℕ,
    tensorPull D l E m n ⋙ tensorPull D l E 1 n ≅ tensorPull D l E (m + 1) n

/-- Completed compositor on every section.
Source: Stacks 03CB, 03D3, 0941
(blueprint: lem-trf-point-system-power-roos-coherence). -/
def HasSiteSections (P : Compositors D l E) : Prop :=
  ∀ (m : ℕ) (M : scalarReductionSource l E (Spec (.of D.k)))
    (V : (Spec (.of D.k)).ProEt)
    (x : (((F D l E m ⋙ F D l E 1).obj M).val.obj (op V))),
    HEq (((P.d m).hom.app M).val.app (op V) x) x

/-- System compositor on every original level section.
Source: Stacks 03CB, 03D3, 0941
(blueprint: lem-trf-point-system-power-roos-coherence). -/
def HasSystemSections (P : Compositors D l E) : Prop :=
  ∀ (m : ℕ) (M : coefficientSequenceModules l E (Spec (.of D.k)))
    (n : ℕ) (V : (Spec (.of D.k)).ProEt)
    (x : (((pull D l E m ⋙ pull D l E 1).obj M).val.obj (op (n, V)))),
    HEq (((P.t m).hom.app M).val.app (op (n, V)) x) x

/-- Restriction compatibility on every original section.
Source: Stacks 03CB, 03D3, 0941
(blueprint: lem-trf-point-system-power-roos-coherence). -/
def HasRestrictionSections (P : Compositors D l E) : Prop :=
  ∀ (r : ℕ) (M : coefficientSequenceModules l E (Spec (.of D.k)))
    (n : ℕ) (V : (Spec (.of D.k)).ProEt)
    (x : ((((coefficientSequenceRestriction l E (Spec (.of D.k)) ⋙
      Ft D l E r).obj M).obj (op n)).val.obj (op V))),
    HEq ((((P.b r).hom.app M).app (op n)).val.app (op V) x) x

/-- Multiplication of the two inserted finite tensor units.
Source: Stacks 03CB, 03D3, 0941
(blueprint: lem-trf-point-system-power-roos-coherence). -/
def HasTensorUnits (P : Compositors D l E) : Prop :=
  ∀ (m n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ)
    (i : ℤ) (V : (Spec (.of D.k)).ProEt)
    (x : (K.X i).val.obj
      (op ((proEtaleIsoPostcompose (pointPower D m).hom).obj
        ((proEtaleIsoPostcompose (pointPower D 1).hom).obj V))))
    (x' : (K.X i).val.obj (op ((proEtaleIsoPostcompose (pointPower D (m + 1)).hom).obj V))),
    HEq x x' →
      (((P.tensor m n).hom.app (K.X i)).val.app (op V)
        (((inverseImageFiniteComparisonComplex l E (pointPower D 1).hom n
          (((tensorPull D l E m n).mapHomologicalComplex (.up ℤ)).obj K)).f i).val.app
            (op V)
            (((inverseImageFiniteComparisonComplex l E (pointPower D m).hom n K).f i).val.app
              (op ((proEtaleIsoPostcompose (pointPower D 1).hom).obj V)) x))) =
        ((inverseImageFiniteComparisonComplex l E (pointPower D (m + 1)).hom n K).f i).val.app
          (op V) x'

/-- The ordinary-limit comparison and the normalized total-limit/Roos identification.
This is the same normalization as strictRoosComparison: the ordinary inclusion is
sent to the right-derived unit. The unit is pinned on every K-injective tower.
Source: Stacks 0941 (blueprint: lem-trf-point-system-power-roos-coherence). -/
structure RoosNormalization where
  /-- Termwise limits and limits of complexes have their canonical projection comparison. -/
  ordinary : (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E (Spec (.of D.k))) ⥤
    scalarReductionSource l E (Spec (.of D.k))).mapHomologicalComplex (.up ℤ) ≅
      roosLimitFunctor
  /-- The comparison is fixed by every original limit projection. -/
  ordinary_projection : ∀ (X : CochainComplex
    (ℕᵒᵖ ⥤ scalarReductionSource l E (Spec (.of D.k))) ℤ) (n : ℕ) (i : ℤ),
    (ordinary.hom.app X ≫ limit.π X.asFunctor (op n)).f i = limit.π (X.X i) (op n)
  /-- The canonical cochain presentation of the right-derived unit. -/
  unit : roosLimitFunctor ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E (Spec (.of D.k))
  /-- Its K-injective normalization uses the actual right-derived comparison. -/
  unit_normalization : ∀ (I : CochainComplex
    (ℕᵒᵖ ⥤ scalarReductionSource l E (Spec (.of D.k))) ℤ) [I.IsKInjective],
    unit.app I ≫ ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E (Spec (.of D.k))) ⥤
      scalarReductionSource l E (Spec (.of D.k))).rightDerivedFunctorObjQIso I).hom =
        DerivedCategory.Q.map (ordinary.inv.app I)
  /-- The same Roos identification on the entire unbounded tower category. -/
  theta : DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E (Spec (.of D.k)) ≅
    roosF ⋙ DerivedCategory.Q
  /-- It carries the specified unit to the actual strict cone inclusion. -/
  theta_normalization : ∀ X : CochainComplex
    (ℕᵒᵖ ⥤ scalarReductionSource l E (Spec (.of D.k))) ℤ,
    unit.app X ≫ theta.hom.app X = DerivedCategory.Q.map (roosι X)

/-- Transport from the recorded system limit to the normalized cone of its strict tower.
Source: Stacks 0941 (blueprint: lem-trf-point-system-power-roos-coherence). -/
def toRoos (N : RoosNormalization D l E)
    (M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ) :
    (coefficientSequenceLimit l E (Spec (.of D.k))).obj (DerivedCategory.Q.obj M) ⟶
      DerivedCategory.Q.obj (roosF.obj ((Uc D l E).obj M)) :=
  (coefficientConstantTowerLimit l E (Spec (.of D.k))).map
      ((coefficientSequenceRestriction l E (Spec (.of D.k))).mapDerivedCategoryFactors.hom.app M) ≫
    N.theta.hom.app ((Uc D l E).obj M)

/-- The specified canonical product and whole-cone comparisons, with their derived descent.
All coordinate equations use the same b, theta, kappa and a.
Source: Stacks 0941, normalized exact-product comparison
(blueprint: lem-trf-point-system-power-roos-coherence). -/
structure Comparisons where
  /-- Canonical product comparison. -/
  psi : ∀ (r : ℕ) (M : CochainComplex
    (coefficientSequenceModules l E (Spec (.of D.k))) ℤ),
    (Fc D l E r).obj (roosP ((Uc D l E).obj M)) ≅
      roosP ((Uc D l E).obj ((Gc D l E r).obj M))
  /-- Canonical whole-cone comparison. -/
  kappa : ∀ r : ℕ, Uc D l E ⋙ roosF ⋙ Fc D l E r ≅ Gc D l E r ⋙ Uc D l E ⋙ roosF
  /-- The specified natural derived comparison. -/
  a : ∀ r : ℕ,
    coefficientSequenceLimit l E (Spec (.of D.k)) ⋙ (F D l E r).mapDerivedCategory ≅
      (pull D l E r).mapDerivedCategory ⋙ coefficientSequenceLimit l E (Spec (.of D.k))

/-- The original product projection equations.
Source: Stacks 0941, normalized exact-product comparison
(blueprint: lem-trf-point-system-power-roos-coherence). -/
def HasProducts (P : Compositors D l E) (A : Comparisons D l E) : Prop :=
  ∀ (r : ℕ) (M : CochainComplex
    (coefficientSequenceModules l E (Spec (.of D.k))) ℤ) (n : ℕ),
    (A.psi r M).hom ≫ Pi.π
        (fun k : ℕ ↦ ((Uc D l E).obj ((Gc D l E r).obj M)).asFunctor.obj (op k)) n =
      (Fc D l E r).map
        (Pi.π (fun k : ℕ ↦ ((Uc D l E).obj M).asFunctor.obj (op k)) n) ≫
          (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            ((Functor.mapHomologicalComplexCompIso (P.b r) (.up ℤ)).hom.app M)).app (op n)

/-- The unshifted diagonal product component.
Source: Stacks 0941, normalized exact-product comparison
(blueprint: lem-trf-point-system-power-roos-coherence). -/
def HasFirstCoordinate (A : Comparisons D l E) : Prop :=
  ∀ (r : ℕ) (M : CochainComplex
    (coefficientSequenceModules l E (Spec (.of D.k))) ℤ) (p : ℤ),
    ((A.kappa r).hom.app M).f (p + 1) ≫
        coordinates D l E ((Uc D l E).obj ((Gc D l E r).obj M)) p ≫ biprod.fst =
      (F D l E r).map (coordinates D l E ((Uc D l E).obj M) p ≫ biprod.fst) ≫
        (A.psi r M).hom.f (p + 1)

/-- The shifted diagonal product component.
Source: Stacks 0941, normalized exact-product comparison
(blueprint: lem-trf-point-system-power-roos-coherence). -/
def HasSecondCoordinate (A : Comparisons D l E) : Prop :=
  ∀ (r : ℕ) (M : CochainComplex
    (coefficientSequenceModules l E (Spec (.of D.k))) ℤ) (p : ℤ),
    ((A.kappa r).hom.app M).f (p + 1) ≫
        coordinates D l E ((Uc D l E).obj ((Gc D l E r).obj M)) p ≫ biprod.snd =
      (F D l E r).map (coordinates D l E ((Uc D l E).obj M) p ≫ biprod.snd) ≫
        (A.psi r M).hom.f p

/-- The prescribed whole-cone representative formula for the derived comparison.
Source: Stacks 0941, normalized exact-product comparison
(blueprint: lem-trf-point-system-power-roos-coherence). -/
def HasDerivedModel (N : RoosNormalization D l E) (A : Comparisons D l E) : Prop :=
  ∀ (r : ℕ) (M : CochainComplex
    (coefficientSequenceModules l E (Spec (.of D.k))) ℤ),
    (A.a r).hom.app (DerivedCategory.Q.obj M) ≫
        (coefficientSequenceLimit l E (Spec (.of D.k))).map
          ((pull D l E r).mapDerivedCategoryFactors.hom.app M) ≫
        toRoos D l E N ((Gc D l E r).obj M) =
      (F D l E r).mapDerivedCategory.map (toRoos D l E N M) ≫
        (F D l E r).mapDerivedCategoryFactors.hom.app (roosF.obj ((Uc D l E).obj M)) ≫
        DerivedCategory.Q.map ((A.kappa r).hom.app M)

-- These functor values already have their canonical public interfaces above.
attribute [local irreducible] CategoryTheory.roosF
set_option backward.isDefEq.respectTransparency.types true

/-- The strict compositor applied termwise; this retains all quotient-linear transitions.
Source: Stacks 015F, 03CB (blueprint: lem-trf-point-system-power-roos-coherence). -/
abbrev tc (P : Compositors D l E) (m : ℕ) :=
  Functor.mapHomologicalComplexCompIso (P.t m) (.up ℤ)

/-- The same compositor localized on whole systems, using the canonical factorization.
Source: Stacks 015F, 03CB (blueprint: lem-trf-point-system-power-roos-coherence). -/
abbrev td (P : Compositors D l E) (m : ℕ) :=
  Functor.mapDerivedCategoryCompNatIso (P.t m)

/-- The canonical termwise completed-module compositor.
Source: Stacks 015F, 03CB (blueprint: lem-trf-point-system-power-roos-coherence). -/
abbrev dc (P : Compositors D l E) (m : ℕ) :=
  Functor.mapHomologicalComplexCompIso (P.d m) (.up ℤ)

/-- The same completed-module compositor in the ordinary unbounded derived category.
Source: Stacks 015F, 03CB (blueprint: lem-trf-point-system-power-roos-coherence). -/
abbrev dd (P : Compositors D l E) (m : ℕ) :=
  Functor.mapDerivedCategoryCompNatIso (P.d m)

/-- The recorded chain insertion with its canonically factored target.
Source: Stacks 015F, blueprint Global powers
(blueprint: lem-trf-point-system-power-roos-coherence). -/
def u (hl : l ≠ D.p) (r : ℕ) (hr : 1 ≤ r) :
    complexSections D l E ⟶ Gc D l E r ⋙ complexSections D l E :=
  chainTransport D l E hl r hr ≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (pull D l E r ⋙ sections D l E))
      (.up ℤ)).inv

/-- The recorded descended insertion with its canonically factored target.
Source: Stacks 015F, blueprint Global powers
(blueprint: lem-trf-point-system-power-roos-coherence). -/
def I (hl : l ≠ D.p) (r : ℕ) (hr : 1 ≤ r) :
    derivedSections D l E ⟶ (pull D l E r).mapDerivedCategory ⋙ derivedSections D l E :=
  derivedTransport D l E hl r hr ≫
    (Functor.mapDerivedCategoryCompIso (pull D l E r) (sections D l E)).hom

/-- StrictTransportCoherence: the corresponding entire-system equality.
Source: blueprint Global powers; Stacks 03CB, 0941
(blueprint: lem-trf-point-system-power-roos-coherence). -/
def StrictTransportCoherence (hl : l ≠ D.p) (P : Compositors D l E) (m : ℕ) (hm : 1 ≤ m) : Prop :=
  ∀ M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ,
    (u D l E hl (m + 1) (Nat.le_trans hm (Nat.le_succ m))).app M =
      (u D l E hl m hm).app M ≫
        (u D l E hl 1 (Nat.le_refl 1)).app ((Gc D l E m).obj M) ≫
        (complexSections D l E).map ((tc D l E P m).hom.app M)

/-- DerivedTransportCoherence: the corresponding entire-system equality.
Source: blueprint Global powers; Stacks 03CB, 0941
(blueprint: lem-trf-point-system-power-roos-coherence). -/
def DerivedTransportCoherence (hl : l ≠ D.p) (P : Compositors D l E) (m : ℕ) (hm : 1 ≤ m) : Prop :=
  ∀ C : coefficientSequenceDerived l E (Spec (.of D.k)),
    (I D l E hl (m + 1) (Nat.le_trans hm (Nat.le_succ m))).app C =
      (I D l E hl m hm).app C ≫
        (I D l E hl 1 (Nat.le_refl 1)).app ((pull D l E m).mapDerivedCategory.obj C) ≫
        (derivedSections D l E).map ((td D l E P m).hom.app C)

/-- ProductCoherence: the corresponding entire-system equality.
Source: blueprint Global powers; Stacks 03CB, 0941
(blueprint: lem-trf-point-system-power-roos-coherence). -/
def ProductCoherence (P : Compositors D l E) (A : Comparisons D l E) (m : ℕ) : Prop :=
  ∀ M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ,
    (dc D l E P m).hom.app (roosP ((Uc D l E).obj M)) ≫ (A.psi (m + 1) M).hom =
      (Fc D l E 1).map (A.psi m M).hom ≫ (A.psi 1 ((Gc D l E m).obj M)).hom ≫
        roosPmap ((Uc D l E).map ((tc D l E P m).hom.app M))

/-- ConeCoherence: the corresponding entire-system equality.
Source: blueprint Global powers; Stacks 03CB, 0941
(blueprint: lem-trf-point-system-power-roos-coherence). -/
def ConeCoherence (P : Compositors D l E) (A : Comparisons D l E) (m : ℕ) : Prop :=
  ∀ M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ,
    (dc D l E P m).hom.app (roosF.obj ((Uc D l E).obj M)) ≫
        (A.kappa (m + 1)).hom.app M =
      (Fc D l E 1).map ((A.kappa m).hom.app M) ≫
        (A.kappa 1).hom.app ((Gc D l E m).obj M) ≫
        roosF.map ((Uc D l E).map ((tc D l E P m).hom.app M))

/-- DerivedComparisonCoherence: the corresponding entire-system equality.
Source: blueprint Global powers; Stacks 03CB, 0941
(blueprint: lem-trf-point-system-power-roos-coherence). -/
def DerivedComparisonCoherence (P : Compositors D l E) (A : Comparisons D l E) (m : ℕ) : Prop :=
  ∀ C : coefficientSequenceDerived l E (Spec (.of D.k)),
    (dd D l E P m).hom.app ((coefficientSequenceLimit l E (Spec (.of D.k))).obj C) ≫
        (A.a (m + 1)).hom.app C =
      (F D l E 1).mapDerivedCategory.map ((A.a m).hom.app C) ≫
        (A.a 1).hom.app ((pull D l E m).mapDerivedCategory.obj C) ≫
        (coefficientSequenceLimit l E (Spec (.of D.k))).map ((td D l E P m).hom.app C)

/-- Point insertion composes on strict system complexes and their ordinary derived
category. The normalized inverse-image/product comparison has the same compositor
on the product, on both signed cone coordinates, and on the entire derived object.

Source: blueprint main-20261015, trace-transport proof, Step 1, Global powers;
`prop-trf-rational-frobenius-integral-model`, proof (3); Stacks 03CB, 0H7J, 0941
(blueprint: lem-trf-point-system-power-roos-coherence).

Proof, following the seven steps of the node:
1. Apply lem-trf-constant-coefficient-composition to the two point powers and A_n.
The finite coefficient comparisons commute with reduction by the isomorphism inverse-image
lemma. Project the completed coefficient equation to every finite level; the limit
universal property proves it. Thus d, t and b respect the actual scalar actions.
2. Apply lem-trf-point-sheaf-insertion-calculus to every finite module in every degree.
Two restrictions compose by presheaf functoriality. The inverse of the canonical
pullback-composition map multiplies the two inserted tensor units. This gives HasTensorUnits
and the equality of section maps, read through the recorded finite j comparisons.
3. The transition squares and differential squares are those of point-system transport
descent. Naturality of the compositor and equality of all strict components give the
first displayed chain-map equality. Localize this equality, using the representative
normalization of derivedTransport and functoriality of localization, to get the second.
4. Exact countable products, exact inverse image and its product preservation allow
lem-cbc-exact-product-functor-strict-limit on the full completed-module category.
Its normalized comparison, together with lem-weil-strict-roos-comparison, supplies N,
psi, kappa and a with the displayed representative normalization, without constructibility.
5. Compose the two candidate product maps with the nth product projection. The defining
projection equations and naturality of d give the same twice-reindexed projection.
Product uniqueness proves the third equality, before any derived localization.
6. Naturality of t with the original transitions makes its product map commute with
shift and hence with 1-shift. In the signed coordinates the differential is
D(x,y)=(dx,(1-shift)x-dy). Apply step 5 to each coordinate: the diagonal entries agree
and both off-diagonal entries vanish. This proves the fourth, whole-cone equality.
7. Substitute HasDerivedModel into the two sides of the last equality. Naturality of theta
moves it through t and d; the two middle inverse theta factors cancel. Step 6 makes
what remains identical. The natural transformations descend through localization,
so the result holds naturally for every derived system object and morphism. No
faithfulness of derived evaluation or constructibility of the realized object is used. -/
theorem point_system_power_roos_coherence (hl : l ≠ D.p) :
    ∃ (P : Compositors D l E) (N : RoosNormalization D l E) (A : Comparisons D l E),
      HasSiteSections D l E P ∧ HasSystemSections D l E P ∧
      HasRestrictionSections D l E P ∧ HasTensorUnits D l E P ∧
      HasProducts D l E P A ∧ HasFirstCoordinate D l E A ∧
      HasSecondCoordinate D l E A ∧ HasDerivedModel D l E N A ∧
      ∀ (m : ℕ) (hm : 1 ≤ m),
      StrictTransportCoherence D l E hl P m hm ∧
      DerivedTransportCoherence D l E hl P m hm ∧
      ProductCoherence D l E P A m ∧ ConeCoherence D l E P A m ∧
      DerivedComparisonCoherence D l E P A m := by
  sorry

end PowerRoos
end WeilConjectures.PointSystemTransport
