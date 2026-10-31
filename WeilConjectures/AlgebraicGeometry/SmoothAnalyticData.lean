/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Homology.KFlatPullback
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-! # Smooth analytic data, with dimensions varying between components

Source: Serre, GAGA, nos. 4--6 and 9; the coordinate description of covectors in
lem-sfb-smooth-analytification-cotangent (blueprint: def-sfb-smooth-analytic-data).

The structures below specify the usual analytic objects by their sections, including
restriction and scalar action. They do not choose an unspecified sheaf or an unspecified
comparison map. In particular, holomorphic covectors obey the Jacobian transition law.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace Topology
open scoped ChangeOfRings

namespace AlgebraicGeometry
namespace SmoothAnalytic

/-- Complex points over the specified base; the lift allows schemes in any universe.
Source: Serre, GAGA, no. 5 (blueprint: def-sfb-smooth-analytic-data). -/
abbrev Points {X : Scheme.{u}} (f : X ⟶ Spec (.of (ULift.{u} ℂ))) :=
  (Over.mk (𝟙 (Spec (.of (ULift.{u} ℂ)))) ⟶ Over.mk f)

/-- The inverse image of a usual complex open under a local regular function.
Source: Serre, GAGA, no. 5, remark, p. 9
(blueprint: def-sfb-smooth-analytic-data). -/
def regularValueSet {X : Scheme.{u}} (f : X ⟶ Spec (.of (ULift.{u} ℂ)))
    (U : X.Opens) (a : Γ(X, U)) (V : Set ℂ) : Set (Points f) :=
  {p | ∃ h : ⊤ ≤ p.left ⁻¹ᵁ U,
    ((Scheme.ΓSpecIso (.of (ULift.{u} ℂ))).hom (p.left.appLE U ⊤ h a)).down ∈ V}

/-- The analytic topology is the least topology making local regular functions continuous.
Source: Serre, GAGA, no. 5, remark, p. 9
(blueprint: def-sfb-smooth-analytic-data). -/
@[instance_reducible] def pointTopology {X : Scheme.{u}} (f : X ⟶ Spec (.of (ULift.{u} ℂ))) :
    TopologicalSpace (Points f) :=
  TopologicalSpace.generateFrom
    {S | ∃ (U : X.Opens) (a : Γ(X, U)) (V : Set ℂ),
      IsOpen V ∧ S = regularValueSet f U a V}

/-- An analytic atlas with finite, possibly varying, complex dimensions.
Source: Serre, GAGA, no. 4, simple points
(blueprint: def-sfb-smooth-analytic-data). -/
structure Atlas (M : Type u) [TopologicalSpace M] where
  /-- The selected coordinate charts. -/
  charts : ∀ n : ℕ, Set (OpenPartialHomeomorph M (Fin n → ℂ))
  /-- Every point has a chart, including the zero-dimensional case. -/
  cover : ∀ x : M, ∃ n c, c ∈ charts n ∧ x ∈ c.source
  /-- All coordinate changes are complex analytic. -/
  transition : ∀ (n m : ℕ) (c : OpenPartialHomeomorph M (Fin n → ℂ))
    (d : OpenPartialHomeomorph M (Fin m → ℂ)), c ∈ charts n → d ∈ charts m →
    ∀ x : M, x ∈ c.source → x ∈ d.source → AnalyticAt ℂ (d ∘ c.symm) (c x)

open Classical in
/-- Express a scalar function on an open in coordinates; values outside the open are
irrelevant to germs at its points. Source: Serre, GAGA, nos. 1 and 4
(blueprint: def-sfb-smooth-analytic-data). -/
noncomputable def inCoordinates {M : Type u} [TopologicalSpace M] {n : ℕ}
    (c : OpenPartialHomeomorph M (Fin n → ℂ)) (U : Opens M) (g : U → ℂ) :
    (Fin n → ℂ) → ℂ :=
  fun z => if h : c.symm z ∈ U then g ⟨c.symm z, h⟩ else 0

/-- A function is holomorphic precisely when it is analytic in every chart.
Source: Serre, GAGA, nos. 1 and 4 (blueprint: def-sfb-smooth-analytic-data). -/
def IsHolomorphic {M : Type u} [TopologicalSpace M] (A : Atlas M)
    (U : Opens M) (g : U → ℂ) : Prop :=
  ∀ (n : ℕ) (c : OpenPartialHomeomorph M (Fin n → ℂ)), c ∈ A.charts n →
    ∀ x : U, x.val ∈ c.source → AnalyticAt ℂ (inCoordinates c U g) (c x.val)

/-- Coordinate covectors over an open, with no extraneous values outside chart domains.
Source: coordinate construction in lem-sfb-smooth-analytification-cotangent, step 6
(blueprint: def-sfb-smooth-analytic-data). -/
abbrev Covectors {M : Type u} [TopologicalSpace M] (A : Atlas M) (U : Opens M) :=
  ∀ (n : ℕ) (c : OpenPartialHomeomorph M (Fin n → ℂ)), c ∈ A.charts n →
    ∀ x : U, x.val ∈ c.source → ((Fin n → ℂ) →L[ℂ] ℂ)

open Classical in
/-- Coordinate expression of a covector family, extended by zero off its domain.
Source: coordinate construction in lem-sfb-smooth-analytification-cotangent, step 6
(blueprint: def-sfb-smooth-analytic-data). -/
noncomputable def covectorCoordinates {M : Type u} [TopologicalSpace M]
    {A : Atlas M} {U : Opens M} (w : Covectors A U) (n : ℕ)
    (c : OpenPartialHomeomorph M (Fin n → ℂ)) (hc : c ∈ A.charts n) :
    (Fin n → ℂ) → ((Fin n → ℂ) →L[ℂ] ℂ) :=
  fun z => if h : c.symm z ∈ U ∧ c.symm z ∈ c.source then
    w n c hc ⟨c.symm z, h.1⟩ h.2 else 0

/-- Holomorphic one-forms are analytic covector families with the cotangent transition law.
Source: coordinate construction in lem-sfb-smooth-analytification-cotangent, step 6
(blueprint: def-sfb-smooth-analytic-data). -/
def IsOneForm {M : Type u} [TopologicalSpace M] {A : Atlas M} {U : Opens M}
    (w : Covectors A U) : Prop :=
  (∀ (n : ℕ) (c : OpenPartialHomeomorph M (Fin n → ℂ)) (hc : c ∈ A.charts n)
    (x : U), x.val ∈ c.source →
      AnalyticAt ℂ (covectorCoordinates w n c hc) (c x.val)) ∧
  (∀ (n m : ℕ) (c : OpenPartialHomeomorph M (Fin n → ℂ))
    (d : OpenPartialHomeomorph M (Fin m → ℂ)) (hc : c ∈ A.charts n)
    (hd : d ∈ A.charts m) (x : U) (hx : x.val ∈ c.source) (hy : x.val ∈ d.source),
      w n c hc x hx = (w m d hd x hy).comp (fderiv ℂ (d ∘ c.symm) (c x.val)))

/-- A ringed space whose sections are exactly the holomorphic functions of the atlas.
The sectionwise evaluations preserve restrictions, so identify sheaves, not just rings.
Source: Serre, GAGA, nos. 1, 4 and 5 (blueprint: def-sfb-smooth-analytic-data). -/
structure FunctionSheaf (R : RingedSpace.{u}) (A : Atlas R) where
  /-- A section is evaluated as a complex-valued function. -/
  eval : ∀ U : Opens R, R.presheaf.obj (op U) →+* (U → ULift.{u} ℂ)
  /-- Sections are determined by their functions. -/
  injective : ∀ U : Opens R, Function.Injective (eval U)
  /-- Precisely the holomorphic functions occur. -/
  range : ∀ (U : Opens R) (g : U → ULift.{u} ℂ),
    (∃ a, eval U a = g) ↔ IsHolomorphic A U (fun x => (g x).down)
  /-- Restriction is restriction of functions. -/
  restrict : ∀ (U V : Opens R) (h : V ≤ U) (a : R.presheaf.obj (op U)) (x : V),
    eval V (R.presheaf.map (homOfLE h).op a) x = eval U a ⟨x.val, h x.property⟩

/-- The holomorphic cotangent sheaf, specified by all its local coordinate covectors.
Source: coordinate construction in lem-sfb-smooth-analytification-cotangent, step 6
(blueprint: def-sfb-smooth-analytic-data). -/
structure Cotangent (R : RingedSpace.{u}) (A : Atlas R) (H : FunctionSheaf R A) where
  /-- The sheaf of holomorphic one-forms. -/
  omega : SheafOfModules.{u} (moduleRings R)
  /-- Its coordinate covectors, additively. -/
  repr : ∀ U : Opens R, omega.val.obj (op U) → Covectors A U
  /-- The coordinate representation preserves addition. -/
  add : ∀ (U : Opens R) (s t : omega.val.obj (op U)) (n : ℕ)
    (c : OpenPartialHomeomorph R (Fin n → ℂ)) (hc : c ∈ A.charts n)
    (x : U) (hx : x.val ∈ c.source),
    repr U (s + t) n c hc x hx = repr U s n c hc x hx + repr U t n c hc x hx
  /-- Covectors determine a section. -/
  injective : ∀ U : Opens R, Function.Injective (repr U)
  /-- Exactly the analytic covectors satisfying the transition law are represented. -/
  range : ∀ (U : Opens R) (w : Covectors A U),
    (∃ a, repr U a = w) ↔ IsOneForm w
  /-- The action of holomorphic functions is pointwise multiplication. -/
  smul : ∀ (U : Opens R) (a : R.presheaf.obj (op U)) (s : omega.val.obj (op U))
    (n : ℕ) (c : OpenPartialHomeomorph R (Fin n → ℂ)) (hc : c ∈ A.charts n)
    (x : U) (hx : x.val ∈ c.source),
    repr U (a • s) n c hc x hx = (H.eval U a x).down • repr U s n c hc x hx
  /-- Restriction is restriction of coordinate covectors. -/
  restrict : ∀ (U V : Opens R) (h : V ≤ U) (s : omega.val.obj (op U))
    (n : ℕ) (c : OpenPartialHomeomorph R (Fin n → ℂ)) (hc : c ∈ A.charts n)
    (x : V) (hx : x.val ∈ c.source),
    repr V (omega.val.map (homOfLE h).op s) n c hc x hx =
      repr U s n c hc ⟨x.val, h x.property⟩ hx
  /-- Holomorphic exterior differentiation in degree zero. -/
  d : ∀ U : Opens R, R.presheaf.obj (op U) → omega.val.obj (op U)
  /-- Its defining formula is the derivative of the coordinate function. -/
  d_repr : ∀ (U : Opens R) (a : R.presheaf.obj (op U)) (n : ℕ)
    (c : OpenPartialHomeomorph R (Fin n → ℂ)) (hc : c ∈ A.charts n)
    (x : U) (hx : x.val ∈ c.source),
    repr U (d U a) n c hc x hx =
      fderiv ℂ (inCoordinates c U (fun y => (H.eval U a y).down)) (c x.val)

/-- Analytic data over a complex scheme: actual complex points, the usual analytic topology,
regular-coordinate charts, and the evaluation morphism of ringed spaces.
Source: Serre, GAGA, nos. 4--6 (blueprint: def-sfb-smooth-analytic-data). -/
structure Data {X : Scheme.{u}} (f : X ⟶ Spec (.of (ULift.{u} ℂ))) where
  /-- The analytification as a ringed space. -/
  space : RingedSpace.{u}
  /-- Its underlying set consists of complex points. -/
  points : space ≃ Points f
  /-- The topology is the analytic topology, not an unspecified manifold topology. -/
  topology : inferInstanceAs (TopologicalSpace space) =
    TopologicalSpace.induced points (pointTopology f)
  /-- Holomorphic charts with varying finite dimensions. -/
  atlas : Atlas space
  /-- The holomorphic structure sheaf, with its evaluations. -/
  functions : FunctionSheaf space atlas
  /-- The canonical map to the scheme. -/
  pi : space ⟶ X.toRingedSpace
  /-- Its underlying map takes a complex point to its scheme point. -/
  support : ∀ (x : space) (z : Spec (.of (ULift.{u} ℂ))),
    pi.hom.base x = (points x).left.base z
  /-- Regular functions are sent to exactly their evaluation functions. -/
  regular : ∀ (U : X.Opens) (a : Γ(X, U))
    (x : (Opens.map pi.hom.base).obj U) (h : ⊤ ≤ (points x.val).left ⁻¹ᵁ U),
    functions.eval _ (pi.hom.c.app (op U) a) x =
      (Scheme.ΓSpecIso (.of (ULift.{u} ℂ))).hom ((points x.val).left.appLE U ⊤ h a)
  /-- The atlas consists of restrictions of regular coordinate functions on affine opens. -/
  regularCharts : ∀ (n : ℕ) (c : OpenPartialHomeomorph space (Fin n → ℂ)),
    c ∈ atlas.charts n → ∃ (U : X.Opens) (_ : IsAffineOpen U) (a : Fin n → Γ(X, U))
      (h : c.source ⊆ ((Opens.map pi.hom.base).obj U : Set space)),
      ∀ (x : space) (hx : x ∈ c.source) (j : Fin n),
        c x j = (functions.eval _ (pi.hom.c.app (op U) (a j)) ⟨x, h hx⟩).down
  /-- Holomorphic one-forms and exterior differentiation. -/
  cotangent : Cotangent space atlas functions

/-- Scalar extension of the inverse-image sheaf, exactly Serre's module analytification.
Source: Serre, GAGA, no. 9, Definition 2
(blueprint: def-sfb-smooth-analytic-data). -/
noncomputable def analytify {X : Scheme.{u}} {f : X ⟶ Spec (.of (ULift.{u} ℂ))}
    (D : Data f) (F : X.Modules) : SheafOfModules.{u} (moduleRings D.space) :=
  SheafOfModules.changeOfRings.{u, u, u}
    (CochainComplex.tensorPullbackRingMap D.pi.hom.base D.space.sheaf X.sheaf ⟨D.pi.hom.c⟩)
    (TopCat.Sheaf.inverseImageModule D.pi.hom.base X.sheaf F)

/-- The local tensor `h ⊗ s` in the analytified module, using the sheafification map.
Source: Serre, GAGA, no. 9, Definition 2
(blueprint: def-sfb-smooth-analytic-data). -/
noncomputable def tensorSection {X : Scheme.{u}} {f : X ⟶ Spec (.of (ULift.{u} ℂ))}
    (D : Data f) (F : X.Modules) (U : X.Opens)
    (h : D.space.presheaf.obj (op ((Opens.map D.pi.hom.base).obj U)))
    (s : F.val.obj (op U)) :
    (analytify D F).val.obj (op ((Opens.map D.pi.hom.base).obj U)) :=
  (CategoryTheory.toSheafify (Opens.grothendieckTopology D.space)
    (SheafOfModules.changeOfRingsPresheaf.{u, u, u}
      (CochainComplex.tensorPullbackRingMap D.pi.hom.base D.space.sheaf X.sheaf
        ⟨D.pi.hom.c⟩)
      (TopCat.Sheaf.inverseImageModule D.pi.hom.base X.sheaf F)).presheaf).app
        (op ((Opens.map D.pi.hom.base).obj U))
    (h ⊗ₜ[(TopCat.Sheaf.inverseImageRing D.pi.hom.base X.sheaf).obj.obj
      (op ((Opens.map D.pi.hom.base).obj U)),
      ((CochainComplex.tensorPullbackRingMap D.pi.hom.base D.space.sheaf X.sheaf
        ⟨D.pi.hom.c⟩).hom.app (op ((Opens.map D.pi.hom.base).obj U))).hom]
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map D.pi.hom.base) AddCommGrpCat.{u} (Opens.grothendieckTopology X)
        (Opens.grothendieckTopology D.space)).unit.app
          ((SheafOfModules.toSheaf _).obj F)).hom.app (op U) s))

/-- A closed holomorphic embedding: a closed topological embedding, analytic in coordinates,
with injective coordinate derivative. This is equivalent to a closed complex submanifold
embedding by the holomorphic inverse theorem.
Source: Serre, GAGA, no. 5, and the graph argument in
lem-sfb-smooth-analytification-cotangent (blueprint: def-sfb-smooth-analytic-data). -/
def IsClosedHolomorphicEmbedding {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (A : Atlas M) (B : Atlas N) (i : M → N) : Prop :=
  IsClosedEmbedding i ∧
    ∀ (n m : ℕ) (c : OpenPartialHomeomorph M (Fin n → ℂ))
      (d : OpenPartialHomeomorph N (Fin m → ℂ)), c ∈ A.charts n → d ∈ B.charts m →
      ∀ x : M, x ∈ c.source → i x ∈ d.source →
        AnalyticAt ℂ (d ∘ i ∘ c.symm) (c x) ∧
          Function.Injective (fderiv ℂ (d ∘ i ∘ c.symm) (c x))

/-- The map of analytic point sets induced by an algebraic morphism over the complex base.
Source: Serre, GAGA, no. 5 (blueprint: def-sfb-smooth-analytic-data). -/
noncomputable def mapPoints {X Y : Scheme.{u}} {f : X ⟶ Spec (.of (ULift.{u} ℂ))}
    {g : Y ⟶ Spec (.of (ULift.{u} ℂ))} (D : Data f) (E : Data g)
    (i : Over.mk f ⟶ Over.mk g) : D.space → E.space :=
  fun x => E.points.symm (D.points x ≫ i)

end SmoothAnalytic
end AlgebraicGeometry
