module

public import Sheaf.AlgebraicGeometry.GraphConeGluing
public import Sheaf.AlgebraicGeometry.NodalLocalTangentData
public import Sheaf.AlgebraicGeometry.ProjectiveNodalTower
public import Mathlib.RingTheory.TensorProduct.Maps
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.NodalLocalTangentNormalization
import Sheaf.AlgebraicGeometry.UnramifiedFieldFibreDecomposition
import Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular
import WeilConjectures.AlgebraicGeometry.ConstantLocalDimensionComponents
import WeilConjectures.RingTheory.BijectiveQuotientMapPowOfFlat
import Sheaf.AlgebraicGeometry.ConormalGradedAlgebra
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality

/-! # The nodal graph cone and normalization fibres

Source: Stacks Project, Curves, Tags 0CBT, 0CBU, 0CBW; Morphisms, Tag 02G7
(blueprint: lem-sfb-nodal-graph-cone-fibre).

## Main definitions

* `LocalComparison`: the actual localized graph stalk and its map on graded classes.
* `PointComparison`: the residue graded algebra and intrinsic normalization branches.
* `Comparison`: the global isomorphism over the singular centre, with its local equations.

## Main statements

* `exists_nodalGraphCone_comparison`: existence and naturality for nodal curves over fields.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.GraphCone.Nodal

/-- The actual tensor product of the pointed stalk with its residue field.
Source: Curves, Tag 0CBT; Varieties, Tag 0C54
(blueprint: lem-sfb-nodal-graph-cone-fibre). -/
def tensorRing {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) (x : C) : CommRingCat.{u} :=
  letI : Algebra k (C.presheaf.stalk x) := (NodalLocal.stalkScalarMap f x).toAlgebra
  letI : Algebra k (C.residueField x) := ((IsLocalRing.residue (C.presheaf.stalk x)).comp
    (NodalLocal.stalkScalarMap f x)).toAlgebra
  .of ((C.presheaf.stalk x) ⊗[k] (C.residueField x))

/-- Multiplication after reducing the stalk factor: a tensor lambda maps to a-bar lambda.
Source: Varieties, Tag 0C54 (blueprint: lem-sfb-nodal-graph-cone-fibre). -/
def tensorAugmentation {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) (x : C) : tensorRing f x →+* C.residueField x :=
  letI : Algebra k (C.presheaf.stalk x) := (NodalLocal.stalkScalarMap f x).toAlgebra
  letI : Algebra k (C.residueField x) := ((IsLocalRing.residue (C.presheaf.stalk x)).comp
    (NodalLocal.stalkScalarMap f x)).toAlgebra
  (Algebra.TensorProduct.lift
    { toRingHom := IsLocalRing.residue (C.presheaf.stalk x), commutes' := fun _ ↦ rfl }
    (AlgHom.id k (C.residueField x)) (fun _ _ ↦ Commute.all _ _)).toRingHom

/-- The left tensor-factor map, a maps to a tensor one.
Source: Varieties, Tag 0C54 (blueprint: lem-sfb-nodal-graph-cone-fibre). -/
def tensorLeft {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) (x : C) : C.presheaf.stalk x →+* tensorRing f x :=
  letI : Algebra k (C.presheaf.stalk x) := (NodalLocal.stalkScalarMap f x).toAlgebra
  letI : Algebra k (C.residueField x) := ((IsLocalRing.residue (C.presheaf.stalk x)).comp
    (NodalLocal.stalkScalarMap f x)).toAlgebra
  Algebra.TensorProduct.includeLeftRingHom (R := k)

/-- The right tensor-factor map.
Source: Varieties, Tag 0C54 (blueprint: lem-sfb-nodal-graph-cone-fibre). -/
def tensorRight {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) (x : C) : C.residueField x →+* tensorRing f x :=
  letI : Algebra k (C.presheaf.stalk x) := (NodalLocal.stalkScalarMap f x).toAlgebra
  letI : Algebra k (C.residueField x) := ((IsLocalRing.residue (C.presheaf.stalk x)).comp
    (NodalLocal.stalkScalarMap f x)).toAlgebra
  (Algebra.TensorProduct.includeRight (R := k) (A := C.presheaf.stalk x)
    (B := C.residueField x)).toRingHom

/-- The graph prime is the kernel of the residue augmentation.
Source: Varieties, Tag 0C54 (blueprint: lem-sfb-nodal-graph-cone-fibre). -/
def graphPrime {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) (x : C) : PrimeSpectrum (tensorRing f x) :=
  ⟨RingHom.ker (tensorAugmentation f x), RingHom.ker_isPrime _⟩

/-- The graph-local ring, constructed by localization rather than chosen abstractly.
Source: Varieties, Tag 0C54 (blueprint: lem-sfb-nodal-graph-cone-fibre). -/
def graphRing {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) (x : C) : CommRingCat.{u} :=
  .of (Localization.AtPrime (graphPrime f x).asIdeal)

/-- The localization algebra structure on the bundled graph-local ring.
Source: Varieties, Tag 0C54 (blueprint: lem-sfb-nodal-graph-cone-fibre). -/
instance graphRingAlgebra {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) (x : C) : Algebra (tensorRing f x) (graphRing f x) :=
  inferInstanceAs (Algebra (tensorRing f x) (Localization.AtPrime (graphPrime f x).asIdeal))

/-- The canonical map from the original pointed stalk to the graph-local ring.
Source: Varieties, Tag 0C54 (blueprint: lem-sfb-nodal-graph-cone-fibre). -/
def toGraphRing {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) (x : C) : C.presheaf.stalk x →+* graphRing f x :=
  (algebraMap (tensorRing f x) (graphRing f x)).comp (tensorLeft f x)

/-- Residue-field scalars in the graph-local ring come from the second tensor factor.
Source: Varieties, Tag 0C54 (blueprint: lem-sfb-nodal-graph-cone-fibre). -/
def graphScalars {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) (x : C) : C.residueField x →+* graphRing f x :=
  (algebraMap (tensorRing f x) (graphRing f x)).comp (tensorRight f x)

/-- The field-valued graph ambient with its specified structural point map.
Source: Curves, Tag 0CBT (blueprint: lem-sfb-nodal-graph-cone-fibre). -/
def pointAmbient {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) (x : C) : Scheme.{u} :=
  pullback f (C.fromSpecResidueField x ≫ f)

/-- The graph of the canonical residue point.
Source: Curves, Tag 0CBT (blueprint: lem-sfb-nodal-graph-cone-fibre). -/
def pointGraph {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) (x : C) : Spec (C.residueField x) ⟶ pointAmbient f x :=
  pullback.lift (C.fromSpecResidueField x) (𝟙 _) (by simp)

/-- The graph point at which the ambient local ring is taken.
Source: Curves, Tag 0CBT (blueprint: lem-sfb-nodal-graph-cone-fibre). -/
def graphPoint {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) (x : C) : pointAmbient f x :=
  pointGraph f x (IsLocalRing.closedPoint (C.residueField x))

/-- The graph ideal is the extended graph prime in its localization.
Source: Varieties, Tag 0C54 (blueprint: lem-sfb-nodal-graph-cone-fibre). -/
def graphIdeal {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) (x : C) : Ideal (graphRing f x) :=
  (graphPrime f x).asIdeal.map (algebraMap (tensorRing f x) (graphRing f x))

/-- Scalar extension of an algebra along a specified residue map.
Source: Divisors, Tags 0631--0633 (blueprint: lem-sfb-nodal-graph-cone-fibre). -/
def fibreRing {R K A : Type u} [CommRing R] [CommRing K] [CommRing A]
    [Algebra R A] (s : R →+* K) : CommRingCat.{u} :=
  letI := s.toAlgebra
  .of (K ⊗[R] A)

/-- The canonical inclusion of an algebra into its residue scalar extension.
Source: Divisors, Tags 0631--0633 (blueprint: lem-sfb-nodal-graph-cone-fibre). -/
def fibreInclude {R K A : Type u} [CommRing R] [CommRing K] [CommRing A]
    [Algebra R A] (s : R →+* K) : A →+* fibreRing (A := A) s :=
  letI := s.toAlgebra
  (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := A)).toRingHom

/-- The residue scalars on the same actual tensor product.
Source: Divisors, Tags 0631--0633 (blueprint: lem-sfb-nodal-graph-cone-fibre). -/
def fibreScalar {R K A : Type u} [CommRing R] [CommRing K] [CommRing A]
    [Algebra R A] (s : R →+* K) : K →+* fibreRing (A := A) s :=
  letI := s.toAlgebra
  Algebra.TensorProduct.includeLeftRingHom (R := R)

/-- The residue point of the centre, expressed using the inverse residue-field map.
Source: Curves, Tag 0CBT (blueprint: lem-sfb-nodal-graph-cone-fibre). -/
@[irreducible]
def centrePoint {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : (singularDiagram f).Z)
    (r : (singularDiagram f).Z.residueField x ≃+*
      C.residueField ((singularDiagram f).i x)) :
    Spec (C.residueField ((singularDiagram f).i x)) ⟶ (singularDiagram f).Z :=
  Spec.map (CommRingCat.ofHom r.toRingHom) ≫ (singularDiagram f).Z.fromSpecResidueField x

/-- The canonical inclusion of a pointwise normalization fibre in the fibre over D.
Source: Curves, Tag 0CBT (blueprint: lem-sfb-nodal-graph-cone-fibre). -/
def normalizationFibreMap {C D : Scheme.{u}} (i : D ⟶ C) (x : C)
    (p : Spec (C.residueField x) ⟶ D) (hp : p ≫ i = C.fromSpecResidueField x) :
    pullback C.fromReducedNormalization (C.fromSpecResidueField x) ⟶
      pullback C.fromReducedNormalization i :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ p)
    (by rw [Category.assoc, hp]; exact pullback.condition)

/-- The degree-zero action of the residue field on the maximal-ideal graded ring.
Source: Curves, Tag 0CBT (3) (blueprint: lem-sfb-nodal-graph-cone-fibre). -/
def tangentScalars (C : Scheme.{u}) (x : C) : C.residueField x →+*
    Ideal.associatedGraded (IsLocalRing.maximalIdeal (C.presheaf.stalk x)) :=
  Ideal.Quotient.lift _ (Ideal.associatedGradedRingHom _)
    (Ideal.associatedGradedRingHom_ker _)

/-- The canonical graph-local comparison, including the actual ambient stalk,
residue quotient, ideal contraction and graded map on representatives.
Source: Varieties, Tag 0C54; Curves, Tag 0CBT
(blueprint: lem-sfb-nodal-graph-cone-fibre). -/
structure LocalComparison {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) (x : C) where
  localStalk : graphRing f x ≃+*
    (pointAmbient f x).presheaf.stalk
      (graphPoint f x)
  localStalk_fst :
    Spec.map (CommRingCat.ofHom localStalk.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (toGraphRing f x)) ≫
      C.fromSpecStalk x =
    (pointAmbient f x).fromSpecStalk
      (graphPoint f x) ≫ pullback.fst _ _
  localStalk_snd :
    Spec.map (CommRingCat.ofHom localStalk.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (graphScalars f x)) =
    (pointAmbient f x).fromSpecStalk
      (graphPoint f x) ≫ pullback.snd _ _
  quotient : graphRing f x ⧸ graphIdeal f x ≃+*
    C.residueField x
  quotient_scalars : ∀ a : C.residueField x,
    quotient (Ideal.Quotient.mk (graphIdeal f x)
      (graphScalars f x a)) = a
  quotient_original : ∀ a : C.presheaf.stalk x,
    quotient (Ideal.Quotient.mk (graphIdeal f x)
      (toGraphRing f x a)) =
        IsLocalRing.residue (C.presheaf.stalk x) a
  ideal_comap : (graphIdeal f x).comap
    (toGraphRing f x) =
      IsLocalRing.maximalIdeal (C.presheaf.stalk x)
  power : ∀ (n : ℕ)
    (a : ↥((IsLocalRing.maximalIdeal (C.presheaf.stalk x)) ^ n)),
    toGraphRing f x a ∈ (graphIdeal f x) ^ n
  graphGraded :
    Ideal.associatedGraded (IsLocalRing.maximalIdeal (C.presheaf.stalk x))
      ≃+* Ideal.associatedGraded (graphIdeal f x)
  graphGraded_apply : ∀ (n : ℕ)
    (a : ↥((IsLocalRing.maximalIdeal (C.presheaf.stalk x)) ^ n)),
    graphGraded (NodalLocal.initialForm (C.presheaf.stalk x) n a) =
      DirectSum.of (Ideal.associatedGradedPiece (graphIdeal f x)) n
        (Submodule.Quotient.mk ⟨toGraphRing f x a, power n a⟩)

/-- The intrinsic pointwise comparison. The open singleton presents the restriction of
G as its residue fibre. The tensor-product equivalence is specified on the canonical
inclusion; the associated-graded map is specified on every ideal-power representative.
The chart equations fix the restriction map from G to the local graph cone, using both
actual ambient projections. The tangent-to-normalization map is the previously defined,
normalized comparison, with its geometric completed-branch correspondence.
Source: Curves, Tags 0CBT, 0CBU, 0CBW; Varieties, Tag 0C54; Divisors, Tag 0633
(blueprint: lem-sfb-nodal-graph-cone-fibre). -/
structure PointBase {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (x : (singularDiagram f).Z) where
  openPoint : (singularDiagram f).Z.affineOpens
  singleton : (openPoint.1 : Set (singularDiagram f).Z) = {x}
  mem : x ∈ openPoint.1
  residueIso : (singularDiagram f).Z.residueField x ≃+*
    C.residueField ((singularDiagram f).i x)
  residueIso_inverse : ∀ a : (singularDiagram f).Z.residueField x,
    ((singularDiagram f).i.residueFieldMap x) (residueIso a) = a
  point_over : centrePoint f x residueIso ≫ (singularDiagram f).i =
    C.fromSpecResidueField ((singularDiagram f).i x)
  scalarIso : Γ((singularDiagram f).Z, openPoint.1) ≃+*
    C.residueField ((singularDiagram f).i x)
  scalarIso_apply : ∀ a : Γ((singularDiagram f).Z, openPoint.1),
    scalarIso a = residueIso ((singularDiagram f).Z.evaluation openPoint.1 x mem a)
  finite : (f.residueFieldAlgebraMap ((singularDiagram f).i x)).Finite
  separable : @Algebra.IsSeparable k (C.residueField ((singularDiagram f).i x)) _ _
    (f.residueFieldAlgebraMap ((singularDiagram f).i x)).toAlgebra

/-- The graded residue fibre and its normalized projectivization at an open point.
Source: Curves, Tags 0CBT, 0CBU, 0CBW; Divisors, Tag 0633
(blueprint: lem-sfb-nodal-graph-cone-fibre). -/
structure PointGraded {k : Type u} [Field k] {C : Scheme.{u}}
    (F : Construction.{u}) (f : C ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (x : (singularDiagram f).Z)
    [GradedRing (NodalLocal.tangentGrading (C.presheaf.stalk ((singularDiagram f).i x)))]
    (base : PointBase f x) where
  toTangent : (F.obj (singularDiagram f)).algebra.grading base.openPoint →+*ᵍ
    NodalLocal.tangentGrading (C.presheaf.stalk ((singularDiagram f).i x))
  bijective : Function.Bijective toTangent
  homogeneous : ∀ (n : ℕ) (a : (F.obj (singularDiagram f)).algebra.obj base.openPoint),
    a ∈ (F.obj (singularDiagram f)).algebra.grading base.openPoint n ↔
      toTangent a ∈ NodalLocal.tangentGrading (C.presheaf.stalk ((singularDiagram f).i x)) n
  scalar : ∀ a : Γ((singularDiagram f).Z, base.openPoint.1),
    toTangent (algebraMap _ _ a) = tangentScalars C ((singularDiagram f).i x) (base.scalarIso a)
  fibreIso : fibreRing (A := (F.obj (singularDiagram f)).algebra.obj base.openPoint)
      base.scalarIso.toRingHom ≃+*
    Ideal.associatedGraded (IsLocalRing.maximalIdeal (C.presheaf.stalk ((singularDiagram f).i x)))
  fibreIso_include : ∀ a : (F.obj (singularDiagram f)).algebra.obj base.openPoint,
    fibreIso (fibreInclude base.scalarIso.toRingHom a) = toTangent a
  fibreIso_scalar : ∀ a : C.residueField ((singularDiagram f).i x),
    fibreIso (fibreScalar base.scalarIso.toRingHom a) = tangentScalars C ((singularDiagram f).i x) a

/-- The affine chart formula specifying the graded comparison on graph ideal classes.
Source: Divisors, Tag 0633 (blueprint: lem-sfb-nodal-graph-cone-fibre). -/
structure PointChart {k : Type u} [Field k] {C : Scheme.{u}}
    (F : Construction.{u}) (f : C ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (x : (singularDiagram f).Z)
    [GradedRing (NodalLocal.tangentGrading (C.presheaf.stalk ((singularDiagram f).i x)))]
    (base : PointBase f x) (graphLocal : LocalComparison f ((singularDiagram f).i x))
    (graded : PointGraded F f x base) where
  chart : Chart (singularDiagram f)
  centreLe : base.openPoint ≤ chart.centre
  chartAffine : IsAffine chart.ambient
  chartMap : Γ(chart.ambient, ⊤) →+* graphRing f ((singularDiagram f).i x)
  chartMap_fst : Spec.map (CommRingCat.ofHom chartMap) ≫
      (@Scheme.isoSpec chart.ambient chartAffine).inv ≫
        pullback.fst chart.family (chart.inclusion ≫ chart.family) ≫ chart.U.1.ι =
    Spec.map (CommRingCat.ofHom (toGraphRing f ((singularDiagram f).i x))) ≫
      C.fromSpecStalk ((singularDiagram f).i x)
  chartMap_snd : Spec.map (CommRingCat.ofHom chartMap) ≫
      (@Scheme.isoSpec chart.ambient chartAffine).inv ≫
        pullback.snd chart.family (chart.inclusion ≫ chart.family) ≫ chart.centre.1.ι =
    Spec.map (CommRingCat.ofHom (graphScalars f ((singularDiagram f).i x))) ≫
      centrePoint f x base.residueIso
  chartPower : ∀ (n : ℕ) (a : ↥(chart.ideal ^ n)),
    chartMap a ∈ (graphIdeal f ((singularDiagram f).i x)) ^ n
  chart_class : ∀ (n : ℕ) (a : ↥(chart.ideal ^ n)),
    graphLocal.graphGraded (graded.toTangent ((F.obj (singularDiagram f)).algebra.res centreLe
      (((F.obj (singularDiagram f)).chart chart).symm
        (DirectSum.of (Ideal.associatedGradedPiece chart.ideal) n (Submodule.Quotient.mk a))))) =
      DirectSum.of (Ideal.associatedGradedPiece (graphIdeal f ((singularDiagram f).i x))) n
        (Submodule.Quotient.mk ⟨chartMap a, chartPower n a⟩)

/-- The intrinsic normalized tangent comparison and its two geometric branches.
Source: Curves, Tags 0CBT, 0CBU, 0CBW (blueprint: lem-sfb-nodal-graph-cone-fibre). -/
structure PointBranches {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : (singularDiagram f).Z)
    [GradedRing (NodalLocal.tangentGrading (C.presheaf.stalk ((singularDiagram f).i x)))] where
  normalization : NodalLocal.Comparison C ((singularDiagram f).i x)
  normalization_natural : normalization.IsNatural
  branches : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ Spec (.of k))
    (y : pullback (C := Scheme.{u}) f g)
    (hy : pullback.fst f g y = (singularDiagram f).i x),
    normalization.GeometricBranches (pullback.fst f g) (pullback.snd f g) y hy
  geometricSplit : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (ρ : C.residueField ((singularDiagram f).i x) →+* Ω),
    ∃ e : fibreRing (A := NodalLocal.ResidueAlgebra
        (C.presheaf.stalk ((singularDiagram f).i x))) ρ ≃+* (Ω × Ω),
      ∀ a : Ω, e (fibreScalar ρ a) = (a, a)

/-- The pointwise comparison assembled from its explicit local, graded and branch data.
Source: Curves, Tag 0CBT; Divisors, Tag 0633 (blueprint: lem-sfb-nodal-graph-cone-fibre). -/
structure PointComparison {k : Type u} [Field k] {C : Scheme.{u}}
    (F : Construction.{u}) (f : C ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (x : (singularDiagram f).Z) where
  base : PointBase f x
  graphLocal : LocalComparison f ((singularDiagram f).i x)
  [tangentGraded : GradedRing (NodalLocal.tangentGrading
    (C.presheaf.stalk ((singularDiagram f).i x)))]
  graded : PointGraded F f x base
  chart : PointChart F f x base graphLocal graded
  branch : PointBranches f x

/-- The local normalization spectrum maps into graph Proj by the normalized tangent
comparison and the map induced by the graded restriction isomorphism.
Source: Curves, Tag 0CBT; Divisors, Tag 0633
(blueprint: lem-sfb-nodal-graph-cone-fibre). -/
@[irreducible]
def PointComparison.intoGraph {k : Type u} [Field k] {C : Scheme.{u}}
    {F : Construction.{u}} {f : C ⟶ Spec (.of k)} [LocallyOfFiniteType f]
    {x : (singularDiagram f).Z} (P : PointComparison F f x) :
    Spec (.of (NodalLocal.ResidueAlgebra (C.presheaf.stalk ((singularDiagram f).i x)))) ⟶
      (F.obj (singularDiagram f)).algebra.relProj :=
  letI := P.tangentGraded
  P.branch.normalization.iso.inv ≫ Proj.map P.graded.toTangent
    (GradedRingHom.irrelevant_le_map_of_surjective P.graded.bijective.surjective) ≫
      (F.obj (singularDiagram f)).algebra.relProjι P.base.openPoint

/-- The same spectrum maps into the actual normalization fibre by its canonical
local-fibre identification and both fibre-product projections.
Source: Curves, Tag 0CBT (blueprint: lem-sfb-nodal-graph-cone-fibre). -/
@[irreducible]
def PointComparison.intoNormalization {k : Type u} [Field k] {C : Scheme.{u}}
    {F : Construction.{u}} {f : C ⟶ Spec (.of k)} [LocallyOfFiniteType f]
    {x : (singularDiagram f).Z} (P : PointComparison F f x) :
    Spec (.of (NodalLocal.ResidueAlgebra (C.presheaf.stalk ((singularDiagram f).i x)))) ⟶
      pullback C.fromReducedNormalization (singularDiagram f).i :=
  letI := P.tangentGraded
  P.branch.normalization.fiberIso.hom ≫
    normalizationFibreMap (singularDiagram f).i ((singularDiagram f).i x)
      (centrePoint f x P.base.residueIso) P.base.point_over

/-- The global comparison over the singular centre, normalized on every open point.
No finiteness is imposed on the set of points. Its local equation is precisely the
projectivization of the graded comparison followed by the normalized tangent isomorphism.
Source: Curves, Tags 0CBT, 0CBU, 0CBW; gluing on the open summands of Morphisms, Tag 02G7
(blueprint: lem-sfb-nodal-graph-cone-fibre). -/
structure Comparison {k : Type u} [Field k] {C : Scheme.{u}}
    (F : Construction.{u}) (f : C ⟶ Spec (.of k)) [LocallyOfFiniteType f] where
  iso : (F.obj (singularDiagram f)).algebra.relProj ≅
    pullback C.fromReducedNormalization (singularDiagram f).i
  over_centre : iso.hom ≫ pullback.snd _ _ = (F.obj (singularDiagram f)).algebra.relProjHom
  point : ∀ x : (singularDiagram f).Z, PointComparison F f x
  pointwise : ∀ x : (singularDiagram f).Z,
    (point x).intoGraph ≫ iso.hom = (point x).intoNormalization

/-- Existence of the canonical graph-cone/normalization comparison for every nodal
curve over a field, and its naturality under curve isomorphisms. Naturality uses the
canonical normalization lift: its equation over the curve specifies that lift, and the
resulting pullback map fixes both projections. The pointwise maps themselves are fixed
by their ideal-class and normalized homogeneous-localization formulas.

Source: Curves, Tags 0CBT, 0CBU, 0CBW; Morphisms, Tag 02G7
(blueprint: lem-sfb-nodal-graph-cone-fibre).

Proof (the nine steps of the node):
1. A field is Noetherian. On affine pairs, finite type implies finite presentation
   (lem-weil-pbc-lft-affine-pairs, lem-weil-pbc-finite-type-noetherian-finite-presentation).
   Every scheme over a field is flat (lem-pc-flat-field), and finite type over a field
   is locally Noetherian (pqf-lem-locnoeth-lft); no quasi-compactness is needed.
2. The nodal-family Fitting theorem identifies D with the nonsmooth locus and makes
   it unramified. The unramified-field decomposition gives its open point summands
   with finite separable residue fields. Each image point is closed in C: its affine
   residue domain embeds in a finite-dimensional field extension, hence is a field.
3. Geometric pure fibre point dimension and the constant-local-dimension component
   criterion give pure dimension one for C. Thus the local tangent theorem applies.
4. On an affine chart Spec S, let q be the kernel of S tensor kappa -> kappa.
   The graph stalk is (S tensor kappa)_q. Inverting S minus p first identifies it
   with the displayed localization of A tensor kappa. The graph quotient is kappa
   and its ideal contracts to the maximal ideal of A (the affine fibre-product,
   open fibre-product, and affine-open stalk-localization lemmas).
5. The separable-point flat-completion-map lemma with K = F = kappa gives the flat
   local map, mH = J and the identity residue map. Flat quotient-power comparison
   makes every A/m^n -> H/J^n bijective. Power-quotient graded comparison then gives
   graphGraded, sending every initial form [a] to [a tensor 1].
6. Graph-cone gluing and the conormal graded algebra's stalk formula identify the
   restriction of G on each open singleton with gr_J H. Compose with the inverse
   of graphGraded. Since O_D at this point is kappa, scalar extension is exactly
   this restriction; fibreIso records its pure-factor inclusion and scalar maps.
7. Nodal local tangent normalization identifies tangent Proj with the normalization
   residue spectrum and its scheme normalization fibre. Projectivize the graded
   comparison by the relative-Proj graded-isomorphism construction. Its normalized
   charts fix the map. The separable quadratic residue algebra splits over every
   algebraically closed extension as Omega times Omega, with the two completed
   normalization branches recorded by the geometric branch square.
8. The open singletons cover D and are disjoint, so the pointwise morphisms and
   inverses glue uniquely over D. Arbitrary coproducts work equally for infinite
   D and for empty D (relative Proj affine restriction and open gluing).
9. Curve isomorphisms preserve the residue augmentation, quotient-power maps and
   homogeneous representative classes. Graph-cone gluing and the intrinsic local
   tangent comparison are natural. Their pointwise squares therefore commute;
   uniqueness of open gluing gives the global naturality equation. No ordering of
   the two branches is chosen. -/
theorem exists_nodalGraphCone_comparison (F : Construction.{u}) :
    (∀ (k : Type u) [Field k] (C : Scheme.{u}) (f : C ⟶ Spec (.of k))
      [LocallyOfFiniteType f],
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ Spec (.of k)),
        Nonempty (pullback (C := Scheme.{u}) f g) →
          (pullback (C := Scheme.{u}) f g).IsPureDimension 1 ∧
            ∀ y : pullback (C := Scheme.{u}) f g,
              y ∉ (pullback.snd f g).smoothLocus →
                IsGeometricOrdinaryDoublePoint Ω (pullback f g) y) →
      Nonempty (Comparison F f)) ∧
    (∀ (k : Type u) [Field k] (C C' : Scheme.{u})
      (f : C ⟶ Spec (.of k)) (f' : C' ⟶ Spec (.of k))
      [LocallyOfFiniteType f] [LocallyOfFiniteType f']
      (a : Comparison F f) (b : Comparison F f')
      (e : C ≅ C') (_he : e.hom ≫ f' = f),
      ∃ (h : DiagramIso (singularDiagram f) (singularDiagram f'))
        (ν : C.reducedNormalization ≅ C'.reducedNormalization)
        (hν : C.fromReducedNormalization ≫ h.x.hom = ν.hom ≫ C'.fromReducedNormalization),
        h.x = e ∧ h.t = Iso.refl (Spec (.of k)) ∧
          F.projMap h ≫ b.iso.hom = a.iso.hom ≫
            pullback.map C.fromReducedNormalization (singularDiagram f).i
              C'.fromReducedNormalization (singularDiagram f').i ν.hom h.z.hom h.x.hom
              hν h.wi) := by
  sorry

end AlgebraicGeometry.GraphCone.Nodal

