module

public import Sheaf.AlgebraicGeometry.SmoothAnalyticData
public import Sheaf.Geometry.Manifold.KahlerCoordinateData
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Topology.Constructions

/-! # Dolbeault forms on the components of a complex projective manifold

Source: Popa, Kodaira dimension, proof of Theorem 1.6.6, pp.26--27; Kong, Notes on
Complex Geometry, §§5.1 and 6.1--6.2 (blueprint: def-sfb-projective-dolbeault-data).

The analytic point space and its holomorphic atlas are the existing `SmoothAnalytic.Data`.
Components have their own dimensions. Local homogeneous lifts identify the projective
embedding on actual scheme-valued points and fix its induced Fubini--Study metric.
The cohomology space is a concrete quotient of closed smooth forms by smooth boundaries.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped Manifold ContDiff

namespace ComplexManifold

/-- Fubini--Study Hermitian pairing on homogeneous lifts and their tangent vectors,
conjugate linear in the first tangent vector. Scaling a lift leaves its pullback unchanged.
Source: Kong §5.1, Fubini--Study formula
(blueprint: def-sfb-projective-dolbeault-data). -/
def fubiniStudyPair {N : ℕ} (z v w : Fin (N + 1) → ℂ) : ℂ :=
  ((∑ j, star (v j) * w j) * (∑ j, star (z j) * z j) -
    (∑ j, star (v j) * z j) * (∑ j, star (z j) * w j)) /
    ((Real.pi : ℂ) * (∑ j, star (z j) * z j) ^ 2)

/-- A homogeneous vector interpreted as global sections on the lifted complex point.
Source: Serre, GAGA no.5; Kong §5.1
(blueprint: def-sfb-projective-dolbeault-data). -/
def homogeneousPointSections {N : ℕ} (z : Fin (N + 1) → ℂ) :
    ULift.{u} (Fin (N + 1)) → Γ(Spec (.of (ULift.{u} ℂ)), ⊤) :=
  fun j ↦ (Scheme.ΓSpecIso (.of (ULift.{u} ℂ))).inv (ULift.up (z j.down))

/-- The equipped projective analytic manifold, presented componentwise. Its topology,
complex structure, projective point map and metric are all normalized. The number of
components may be zero; dimensions may differ. No cohomological conclusion is assumed.
Source: Popa, Theorem 1.6.6 proof, pp.26--27; Kong §§3.1, 5.1, 6.1
(blueprint: def-sfb-projective-dolbeault-data). -/
structure ProjectiveDolbeaultData {X : Scheme.{u}}
    {f : X ⟶ Spec (.of (ULift.{u} ℂ))} (A : SmoothAnalytic.Data f) where
  count : ℕ
  component : Fin count → Type u
  dimension : Fin count → ℕ
  [topology : ∀ i, TopologicalSpace (component i)]
  [charts : ∀ i, ChartedSpace (Model (dimension i)) (component i)]
  [manifold : ∀ i, IsManifold (𝓘(ℂ, Model (dimension i))) ∞ (component i)]
  [hausdorff : ∀ i, T2Space (component i)]
  [compact : ∀ i, CompactSpace (component i)]
  [connected : ∀ i, ConnectedSpace (component i)]
  [measurable : ∀ i, MeasurableSpace (component i)]
  [borel : ∀ i, BorelSpace (component i)]
  glue : (Σ i, component i) ≃ₜ A.space
  compatible : ∀ (i : Fin count) (m : ℕ)
    (e : OpenPartialHomeomorph (component i) (Model (dimension i)))
    (c : OpenPartialHomeomorph A.space (Fin m → ℂ)),
    e ∈ atlas (Model (dimension i)) (component i) → c ∈ A.atlas.charts m →
    ∀ x ∈ e.source, glue ⟨i, x⟩ ∈ c.source →
      m = dimension i ∧
      AnalyticAt ℂ (fun y ↦ c (glue ⟨i, e.symm y⟩)) (e x) ∧
      Function.Injective (fderiv ℂ (fun y ↦ c (glue ⟨i, e.symm y⟩)) (e x))
  metric : ∀ i, HermitianMetric (dimension i) (component i)
  kahler : ∀ i, IsKahlerMetric (metric i)
  volume : ∀ i, MetricVolume (metric i)
  operators : ∀ i, DolbeaultOperators (metric i) (volume i)
  ambientDimension : ℕ
  embedding : X ⟶ ℙ(ULift.{u} (Fin (ambientDimension + 1)); Spec (.of (ULift.{u} ℂ)))
  closed : IsClosedImmersion embedding
  over : embedding ≫
    ℙ(ULift.{u} (Fin (ambientDimension + 1)); Spec (.of (ULift.{u} ℂ))) ↘ _ = f
  induced : ∀ (i : Fin count) (x : component i),
    ∃ (e : OpenPartialHomeomorph (component i) (Model (dimension i)))
      (z : Model (dimension i) → Fin (ambientDimension + 1) → ℂ)
      (hz : ∀ y ∈ e.target,
        Ideal.span (Set.range (homogeneousPointSections.{u} (z y))) = ⊤),
      e ∈ atlas (Model (dimension i)) (component i) ∧ x ∈ e.source ∧
      (∀ y ∈ e.target, AnalyticAt ℂ z y) ∧
      (∀ (y : Model (dimension i)) (hy : y ∈ e.target),
        (A.points (glue ⟨i, e.symm y⟩)).left ≫ embedding =
          ProjectiveSpace.homOfSections (𝟙 (Spec (.of (ULift.{u} ℂ))))
            (homogeneousPointSections (z y)) (hz y hy)) ∧
      (∀ y ∈ e.target, ∀ v w : Model (dimension i),
        metricPair (metric i).matrix (e.symm y)
          (chartTangent e y v) (chartTangent e y w) =
            fubiniStudyPair (z y) (fderiv ℂ z y v) (fderiv ℂ z y w))

attribute [instance] ProjectiveDolbeaultData.topology ProjectiveDolbeaultData.charts
  ProjectiveDolbeaultData.manifold ProjectiveDolbeaultData.hausdorff
  ProjectiveDolbeaultData.compact ProjectiveDolbeaultData.connected
  ProjectiveDolbeaultData.measurable ProjectiveDolbeaultData.borel

variable {X : Scheme.{u}} {f : X ⟶ Spec (.of (ULift.{u} ℂ))}
  {A : SmoothAnalytic.Data f} (P : ProjectiveDolbeaultData A)

/-- Smooth forms on a finite disjoint union are families of smooth forms on its components.
Source: Popa, Theorem 1.6.6 proof, componentwise extension
(blueprint: def-sfb-projective-dolbeault-data). -/
abbrev ProjectiveDolbeaultData.Forms :=
  ∀ i : Fin P.count, smoothForms (n := P.dimension i) (M := P.component i)

/-- Closed forms of bidegree `(p,q)`, componentwise and with invalid degrees zero.
Source: Kong §6.2; Popa, Theorem 1.6.6 proof
(blueprint: def-sfb-projective-dolbeault-data). -/
def ProjectiveDolbeaultData.cycles (p q : ℤ) : Submodule ℂ P.Forms :=
  Submodule.pi Set.univ (fun i ↦ typeForms p q ⊓ (P.operators i).dbar.ker)

/-- Boundaries inside the closed forms. The comap only places the actual smooth image
in the subtype of cycles; square-zero ensures that no boundary is discarded.
Source: Kong §6.2 (blueprint: def-sfb-projective-dolbeault-data). -/
def ProjectiveDolbeaultData.boundaries (p q : ℤ) : Submodule ℂ (P.cycles p q) :=
  (Submodule.pi Set.univ (fun i ↦ (P.operators i).exact p q)).comap (P.cycles p q).subtype

/-- Dolbeault cohomology is the kernel modulo the actual image, without closure.
Source: Kong §6.2; Popa, Theorem 1.6.6 proof
(blueprint: def-sfb-projective-dolbeault-data). -/
abbrev ProjectiveDolbeaultData.Cohomology (p q : ℤ) :=
  (P.cycles p q) ⧸ P.boundaries p q

/-- The canonical cohomology class of a closed smooth form.
Source: Kong §6.2 (blueprint: def-sfb-projective-dolbeault-data). -/
def ProjectiveDolbeaultData.classOf (p q : ℤ) (α : P.cycles p q) : P.Cohomology p q :=
  Submodule.Quotient.mk α

end ComplexManifold
