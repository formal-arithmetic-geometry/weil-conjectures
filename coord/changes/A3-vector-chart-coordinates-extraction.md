# AlgebraicGeometry.ProEtale.VectorIntegrationChart.ChartComparison

## Reason

Extract the existing chart coordinate interface into a prerequisite module so separately
stated intermediate lemmas can refer to the actual maps without importing the theorem
that must use them. This avoids an import cycle and preserves every mathematical object.

## Old

The following complete prefix of `Sheaf.Paper.VectorIntegrationChartComparison` contained
all sixteen public helper declarations, followed by `vectorIntegration_chart_comparison`:

```lean
module

public import Sheaf.Paper.ProjectionPurityAgreement
public import Sheaf.Paper.VectorIntegrationSiteComparison
public import Sheaf.Paper.VectorBundlePurity
public import Sheaf.Paper.AffineSpacePurityComparison
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import WeilConjectures.ConstructibleSheaf.SpecializationCriterion

/-! # Vector integration in a linear chart

Source: main-20261015, sec-smooth-purity/sk-prop-an,
thm-amb-vector-bundle-purity.proof.md, second paragraph.
(blueprint: lem-pur-vector-integration-chart-comparison).

The source comparisons below contain only Tate pullback, tensor comparison and units.
The target comparisons contain only exceptional exchange and comparison-adjunction units.

## Main declarations

* `restrictedRaw` and `restrictedMap`: the actual restricted integration transpose.
* `orderedMap`: the recorded ordered affine comparison in the same endpoints.
* `ChartComparison` and `vectorIntegration_chart_comparison`: their equality and
  independence of every positive annihilating exponent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationChart
open AffineLinePurity AffineSpacePurity VectorIntegrationSite

/-- The coefficient unit is bounded below and constructible of Tor interval [0,0].
Source: the coefficient-unit input of the chart comparison, proof Step 1
(blueprint: lem-pur-vector-integration-chart-comparison).
Proof: A is the constant rank-one free module sheaf. Its single complex has only
cohomology in degree zero. Tensor with this complex is the identity, so it has
Tor interval [0,0], including the empty scheme. -/
theorem unit_properties (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    DerivedCategory.TStructure.t.plus (Etale.ordinaryFiniteUnit (Ring P) T) ∧
    etaleFiniteTor (Ring P) T (Etale.ordinaryFiniteUnit (Ring P) T) := by
  have : Scheme.IsConstructibleSheaf (Etale.ordinaryFiniteConstant (Ring P) T) :=
    Scheme.isConstructibleSheaf_constantSheaf _
  refine ⟨⟨0, inferInstance⟩, ?_⟩
  exact ⟨Etale.DerivedCategory.boundedConstructible_singleFunctor_obj _ 0,
    0, 0, DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
      (CategoryTheory.ObjectProperty.flat_of_isDualizable
        (A := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Ring P)))
        isDualizable_unit)⟩

/-- The coefficient unit with its canonical bounded-below witness.
Source: the coefficient-unit input (blueprint: lem-pur-vector-integration-chart-comparison). -/
def unitPlus (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    Plus (Ring P) T :=
  (siteComparisonDerivedPullbackPlus T (Ring P)).obj
    ⟨Etale.ordinaryFiniteUnit (Ring P) T, (unit_properties P T).1⟩

/-- Exact comparison of an ordered tensor of shifted lines, factor by factor.
Source: canonical Tate identifications in the chart equation
(blueprint: lem-pur-vector-integration-chart-comparison). -/
def comparedBaseAction (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (T : Scheme.{u}) :
    (d : ℕ) →
    (comparison A T).obj (Etale.affineLinearBaseCoefficient A N hA T d) ≅
    (action ((tensor A T).flip.obj
      ((comparison A T).obj ((Etale.ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧))) d).obj
        (unit A T)
  | 0 => Iso.refl _
  | d + 1 => tensorComparison A T _ _ ≪≫
      ((tensor A T).flip.obj
        ((comparison A T).obj ((Etale.ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧))).mapIso
          (comparedBaseAction A N hA T d)

/-- The preceding canonical comparison at the fixed finite purity coefficient.
Source: canonical Tate identifications (blueprint: lem-pur-vector-integration-chart-comparison).
-/
def baseAction (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  comparedBaseAction (Ring P) (P.coefficients.l ^ (P.level + 1)) (annihilates P) T

/-- Pullback of the constant coefficient, using the canonical site square.
Source: canonical Tate pullback (blueprint: lem-pur-vector-integration-chart-comparison). -/
def unitPullback (P : WeilConjectures.PurityFiniteSetting.{u}) {X T : Scheme.{u}}
    (f : X ⟶ T) :
    (inverseImage (Ring P) f).obj (unit (Ring P) T) ≅ unit (Ring P) X :=
  pullbackUnit (Ring P) f

/-- Canonical tensor/unit source composite with its computed endpoints retained.
Source: Tate pullback in the chart equation
(blueprint: lem-pur-vector-integration-chart-comparison). -/
def orderedSourceRaw (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    (d : ℕ) → Σ M N : D P (iteratedAffineLine T d), M ≅ N
  | 0 => ⟨_, _, Iso.refl (unit (Ring P) T)⟩
  | d + 1 => ⟨_, _, baseAction P (iteratedAffineLine T (d + 1)) (d + 1) ≪≫
      (action ((tensor (Ring P) (iteratedAffineLine T (d + 1))).flip.obj
        ((comparison (Ring P) (iteratedAffineLine T (d + 1))).obj
          ((Etale.ordinaryFiniteLine (Ring P) (P.coefficients.l ^ (P.level + 1))
            (annihilates P) (iteratedAffineLine T (d + 1)))⟦(2 : ℤ)⟧))) (d + 1)).mapIso
        (unitPullback P (iteratedAffineLineProj T (d + 1))).symm⟩

/-- The raw source composite has exactly the ordered comparison endpoints.
Source: canonical Tate pullback (blueprint: lem-pur-vector-integration-chart-comparison).
Proof: at zero both endpoints are the coefficient unit. At a successor, unfold
orderedSource and twistAction. The raw composite first compares every shifted Tate
factor and then replaces the unit by its canonical inverse-image identification.
These are the displayed endpoints; transporting the raw isomorphism gives existence.
HEq fixes its hom, hence fixes the isomorphism uniquely. -/
theorem orderedSourceIso_existsUnique (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) (d : ℕ) :
    ∃! e : (comparison (Ring P) (iteratedAffineLine T d)).obj
      (Etale.affineLinearBaseCoefficient (Ring P) (P.coefficients.l ^ (P.level + 1))
        (annihilates P) (iteratedAffineLine T d) d) ≅
      (orderedSource P T d).obj (unit (Ring P) T),
      HEq e.hom (orderedSourceRaw P T d).2.2.hom := by
  cases d with
  | zero =>
    unfold orderedSource orderedSourceRaw
    refine ⟨Iso.refl _, HEq.rfl, ?_⟩
    intro e he
    apply Iso.ext
    exact eq_of_heq he
  | succ d =>
    unfold orderedSource twistAction
    refine ⟨(orderedSourceRaw P T (d + 1)).2.2, HEq.rfl, ?_⟩
    intro e he
    apply Iso.ext
    exact eq_of_heq he

/-- The source identification fixed by the actual tensor/unit composite.
Source: canonical Tate pullback (blueprint: lem-pur-vector-integration-chart-comparison). -/
def orderedSourceIso (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    (d : ℕ) :=
  (orderedSourceIso_existsUnique P T d).exists.choose

/-- Ordinary exceptional target with its canonical compactification evidence.
Source: target of the chart equation
(blueprint: lem-pur-vector-integration-chart-comparison). -/
def ordinaryTarget (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u}) (d : ℕ) :=
  letI := (projection_geometry T d).2
  (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} (Ring P))
    (iteratedAffineLineProj T d)).obj (Etale.ordinaryFiniteUnit (Ring P) T)

/-- Exceptional target coordinates: comparison-unit rho in positive dimension,
and the canonical exceptional identity in dimension zero.
Source: exceptional and identity conventions of the chart equation
(blueprint: lem-pur-vector-integration-chart-comparison). -/
def orderedTargetIso (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    (d : ℕ) →
    (exceptional P T d).obj (unit (Ring P) T) ≅
    (comparison (Ring P) (iteratedAffineLine T d)).obj
      (ordinaryTarget P T d)
  | 0 => by
    unfold exceptional
    exact (comparison (Ring P) T).mapIso
      (((Etale.rightDerivedUpperShriekIsoOfIso (ModuleCat.{u + 1} (Ring P))
        (Iso.refl T)) ≪≫ Etale.leftDerivedUpperStarId
          (ModuleCat.{u + 1} (Ring P)) T).app _).symm
  | d + 1 => by
    letI := (projection_geometry T (d + 1)).2
    letI := isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} (Ring P)) T
      (Etale.ordinaryFiniteUnit (Ring P) T) (unit_properties P T).1
    unfold exceptional
    exact (comparison (Ring P) _).mapIso
      ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} (Ring P))
        (iteratedAffineLineProj T (d + 1))).mapIso
        (asIso ((derivedComparisonAdjunction (ModuleCat.{u + 1} (Ring P)) T).unit.app
          (Etale.ordinaryFiniteUnit (Ring P) T)))).symm

/-- Geometry of every open chart, derived from the given finite-type base.
Source: chart comparison, proof Step 1
(blueprint: lem-pur-vector-integration-chart-comparison).
Proof: a Noetherian open is quasi-compact. Its open immersion is finite type;
compose with the given structure map. Separatedness is preserved by composition. -/
theorem open_geometry (P : WeilConjectures.PurityFiniteSetting.{u})
    (Z : Scheme.{u}) [IsNoetherian Z] (aZ : Z ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aZ] [QuasiCompact aZ] [IsSeparated aZ] (U : Z.Opens) :
    LocallyOfFiniteType (U.ι ≫ aZ) ∧ QuasiCompact (U.ι ≫ aZ) ∧
      IsSeparated (U.ι ≫ aZ) := by
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The ordered affine comparison at the coefficient unit, with its source and target
expressed as compared ordinary objects. No integration or purity map is used in
these coordinate identifications.
Source: the ordered Gamma in the chart equation
(blueprint: lem-pur-vector-integration-chart-comparison). -/
def orderedMap (P : WeilConjectures.PurityFiniteSetting.{u})
    (Z : Scheme.{u}) [IsNoetherian Z] (aZ : Z ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aZ] [QuasiCompact aZ] [IsSeparated aZ] (U : Z.Opens) (d : ℕ) :=
  letI := (open_geometry P Z aZ U).1
  letI := (open_geometry P Z aZ U).2.1
  letI := (open_geometry P Z aZ U).2.2
  (orderedSourceIso P U.toScheme d).hom ≫
    affineSpacePurityComparison P U.toScheme (U.ι ≫ aZ) (unitPlus P U.toScheme)
      (Etale.ordinaryFiniteUnit (Ring P) U.toScheme) (unit_properties P U.toScheme).2
      (Iso.refl _) d ≫ (orderedTargetIso P U.toScheme d).hom

/-- The actual inverse unit-object purity, restricted through the inverse linear chart.
The ordinary adjunction transposes the specified global integration. The subsequent
exceptional exchange is precisely the mate of inverse compact-support exchange.
The source identification is only ordinary pullback composition and Tate pullback.
Finally exact site comparison realizes the entire map on the small pro-etale site.
Source: vector-bundle integration chart comparison, proof Steps 2--3
(blueprint: lem-pur-vector-integration-chart-comparison). -/
def restrictedRaw (P : WeilConjectures.PurityFiniteSetting.{u})
    (Z : Scheme.{u}) [IsNoetherian Z] (aZ : Z ⟶ Spec (.of P.field.k))
    (d : ℕ) (F : Z.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (U : Z.Opens) (e : VectorBundleZeroSection.Trivialization Z d F U)
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0) :=
  letI := (Etale.vectorIntegration_geometry Z d F).1
  letI := (Etale.vectorIntegration_geometry Z d F).2.1
  letI := (projection_geometry U.toScheme d).2
  let hZ := primeUnit P Z aZ
  let hN : IsUnit ((P.coefficients.l ^ (r + 1) : ℕ) : Γ(Z, ⊤)) :=
    by simpa only [Nat.cast_pow] using hZ.pow (r + 1)
  let t := Etale.projectiveLineTraceTransport (P.coefficients.l ^ (r + 1))
    (pow_pos P.coefficients.prime.out.pos _) (Ring P) hA
  let a := Etale.vectorIntegrationChart Z d F U e
  let f := VectorBundleZeroSection.π Z d F
  let p := affineTraceProjection U.toScheme d
  let c := (Etale.vectorBundlePurityAdjunction (Ring P) Z d F).homEquiv
    (Etale.vectorIntegrationCoefficient (Ring P) (P.coefficients.l ^ (r + 1)) hA Z d F)
    (Etale.ordinaryFiniteUnit (Ring P) Z)
    (Etale.vectorBundleIntegration (P.coefficients.l ^ (r + 1))
      (pow_pos P.coefficients.prime.out.pos _) (Ring P) hA Z hN d F)
  (comparison (Ring P) (affineTraceTower U.toScheme d)).map
    ((Etale.vectorIntegrationBaseCoefficientPullback (Ring P)
        (P.coefficients.l ^ (r + 1)) hA t (a ≫ f) hN d).inv ≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} (Ring P)) a f).hom.app _ ≫
      (Etale.ordinaryFinitePullback (Ring P) a).map c ≫
      (Etale.rightDerivedUpperShriekBaseChangeMap (Ring P)
        (Etale.vectorIntegrationChart_isPullback Z d F U e)).app
          (Etale.ordinaryFiniteUnit (Ring P) Z) ≫
      (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} (Ring P)) p).map
        (Etale.ordinaryFiniteUnitPullback (Ring P) U.ι).hom)

/-- The recursive polynomial towers give the same chart map endpoints.
Source: change of affine coordinates in the chart equation
(blueprint: lem-pur-vector-integration-chart-comparison).
Proof: induct on d to identify affineTraceTower and iteratedAffineLine, whose zero
objects are T and whose successor objects adjoin one affine coordinate. The same
induction identifies their projections. Transport restrictedRaw along these
identities. Its source is the compared affineLinearBaseCoefficient by the
base-coefficient pullback and its target is ordinaryTarget by the unit pullback.
HEq fixes the actual morphism, so the transported morphism is unique. -/
theorem restrictedMap_existsUnique (P : WeilConjectures.PurityFiniteSetting.{u})
    (Z : Scheme.{u}) [IsNoetherian Z] (aZ : Z ⟶ Spec (.of P.field.k))
    (d : ℕ) (F : Z.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (U : Z.Opens) (e : VectorBundleZeroSection.Trivialization Z d F U)
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0) :
    ∃! c : (comparison (Ring P) (iteratedAffineLine U.toScheme d)).obj
      (Etale.affineLinearBaseCoefficient (Ring P) (P.coefficients.l ^ (r + 1)) hA
        (iteratedAffineLine U.toScheme d) d) ⟶
      (comparison (Ring P) (iteratedAffineLine U.toScheme d)).obj
        (ordinaryTarget P U.toScheme d),
      HEq c (restrictedRaw P Z aZ d F U e r hA) := by
  have ht (T : Scheme.{u}) (n : ℕ) :
      (⟨affineTraceTower T n, affineTraceProjection T n⟩ : Σ X : Scheme.{u}, X ⟶ T) =
        ⟨iteratedAffineLine T n, iteratedAffineLineProj T n⟩ := by
    induction n with
    | zero => rfl
    | succ n ih =>
      exact congrArg (fun q : Σ X : Scheme.{u}, X ⟶ T ↦
        (⟨AffineSpace PUnit.{u + 1} q.1,
          (AffineSpace PUnit.{u + 1} q.1 ↘ q.1) ≫ q.2⟩ : Σ X : Scheme.{u}, X ⟶ T)) ih
  have transport (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (ha : (N : A) = 0)
      (T X Y : Scheme.{u}) (f : X ⟶ T) (g : Y ⟶ T)
      [HasCompactification f] [HasCompactification g]
      (h : (⟨X, f⟩ : Σ X : Scheme.{u}, X ⟶ T) = ⟨Y, g⟩)
      (c : (comparison A X).obj (Etale.affineLinearBaseCoefficient A N ha X d) ⟶
        (comparison A X).obj
          ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj
            (Etale.ordinaryFiniteUnit A T))) :
      ∃ c' : (comparison A Y).obj (Etale.affineLinearBaseCoefficient A N ha Y d) ⟶
        (comparison A Y).obj
          ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) g).obj
            (Etale.ordinaryFiniteUnit A T)), HEq c' c := by
    cases h
    exact ⟨c, HEq.rfl⟩
  let := (projection_geometry U.toScheme d).2
  obtain ⟨c, hc⟩ := transport (Ring P) (P.coefficients.l ^ (r + 1)) hA
    U.toScheme _ _ (affineTraceProjection U.toScheme d)
    (iteratedAffineLineProj U.toScheme d) (ht U.toScheme d)
    (restrictedRaw P Z aZ d F U e r hA)
  exact ⟨c, hc, fun c' hc' ↦ eq_of_heq (hc'.trans hc.symm)⟩

/-- The restricted integration transpose in the ordered polynomial coordinates,
uniquely fixed by the actual exceptional-exchange composite.
Source: chart equation (blueprint: lem-pur-vector-integration-chart-comparison). -/
def restrictedMap (P : WeilConjectures.PurityFiniteSetting.{u})
    (Z : Scheme.{u}) [IsNoetherian Z] (aZ : Z ⟶ Spec (.of P.field.k))
    (d : ℕ) (F : Z.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (U : Z.Opens) (e : VectorBundleZeroSection.Trivialization Z d F U)
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0) :=
  (restrictedMap_existsUnique P Z aZ d F U e r hA).exists.choose

/-- The chart equation and invariance under every positive annihilating exponent.
Noetherianity is deduced from finite type over the field, rather than assumed.
Source: displayed chart equation and final sentence of the node
(blueprint: lem-pur-vector-integration-chart-comparison). -/
def ChartComparison (P : WeilConjectures.PurityFiniteSetting.{u})
    (Z : Scheme.{u}) (aZ : Z ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aZ] [QuasiCompact aZ] [IsSeparated aZ]
    (d : ℕ) (F : Z.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (U : Z.Opens) (e : VectorBundleZeroSection.Trivialization Z d F U) : Prop :=
  letI : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType aZ
  restrictedMap P Z aZ d F U e P.level (annihilates P) = orderedMap P Z aZ U d ∧
    ∀ (r r' : ℕ) (h : r ≤ r')
      (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
      (hA' : ((P.coefficients.l ^ (r' + 1) : ℕ) : Ring P) = 0),
      (comparison (Ring P) (iteratedAffineLine U.toScheme d)).map
          (baseExponentComparison P.coefficients.l P.extension (P.level - 1)
            (iteratedAffineLine U.toScheme d)
            (primeUnit P _ (towerBase (U.ι ≫ aZ) d)) r r' h hA hA' d).hom ≫
        restrictedMap P Z aZ d F U e r hA = restrictedMap P Z aZ d F U e r' hA'

```

## New

That exact prefix is now `Sheaf.Paper.VectorIntegrationChartCoordinates`, with only its
blueprint tags updated to `def-pur-vector-chart-comparison-coordinates`, followed by the
same namespace end. Every helper name, universe, instance binder, type, body and visibility
is unchanged. The original theorem module publicly imports the coordinate module:

```lean
public import Sheaf.Paper.VectorIntegrationChartCoordinates
```

It privately imports the three new intermediate-statement modules and keeps the original
`vectorIntegration_chart_comparison` signature and docstring verbatim. Its proof combines
chart restriction, unit-coordinate transport, the existing ordered transpose theorem and
affine exponent naturality. All four original public imports remain publicly reexported
through the coordinate module. There is no change to a definition used by a target.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.VectorIntegrationChartComparison | A3 | Same public interface by reexport; assembly proof uses three new intermediate statements. |
| Sheaf.Paper.VectorIntegrationChartCoordinates | new, A3 | Contains the identical extracted helper declarations. |
| Sheaf.Paper.VectorIntegrationUnitTranspose | new, A3 | Uses the shared interface to formulate the affine adjunct and unit-coordinate equation. |
| Sheaf.Paper.VectorIntegrationChartTranspose | new, A3 | States the inverse-frame restriction equation using shared actual maps. |
| Sheaf.Paper.AffineIntegrationExponentTransition | new, A3 | States affine adjunct naturality under root transition. |

`tools/downstream.py Sheaf.Paper.VectorIntegrationChartComparison --uses
AlgebraicGeometry.ProEtale.VectorIntegrationChart.restrictedRaw` reported zero downstream
modules and only the item itself as a user. A namespace-qualified scan finds no other consumer of these sixteen names;
unqualified-name matches elsewhere refer to unrelated namespaces. No held module is adapted.

## Status

landed 20261025T122442-L-1772857 2026-10-25 (merge of deliver/A3/Sheaf.Paper.VectorIntegrationChartComparison)
