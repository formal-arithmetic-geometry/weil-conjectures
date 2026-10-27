module

public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.Topology.LocallyConstantMapsPresheaf
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Topology.Maps.Basic

/-! # The holomorphic module on analytic complex projective space

Source: Serre, GAGA, nos. 1--2 and 13, Lemma 4, printed pp.3--5 and 20--21
(blueprint: def-sfb-projective-holomorphic-module).

This is a presentation by sections: the coefficient rings are exactly locally constant
complex functions, and the module sections are exactly functions analytic in every standard
projective chart. Both identifications respect restriction and scalar multiplication.
No unspecified choice of a sheaf or a map is used to define an object.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace Topology

namespace ComplexGeometry

/-- The normalized homogeneous vector in a standard affine chart is nonzero.
Source: Serre, GAGA, no. 13, Lemma 4
(blueprint: def-sfb-projective-holomorphic-module).

Proof: its coordinate at `j` is `1` by `Fin.insertNth_apply_same`, so it cannot
be the zero vector. -/
theorem projectiveChartVector_ne_zero (n : ℕ) (j : Fin (n + 1)) (w : Fin n → ℂ) :
    (Fin.insertNth j (1 : ℂ) w : Fin (n + 1) → ℂ) ≠ 0 := by
  sorry

/-- The inverse of the standard chart with nonzero homogeneous coordinate `j`:
insert `1` in position `j`. Source: Serre, GAGA, no. 13, Lemma 4
(blueprint: def-sfb-projective-holomorphic-module). -/
noncomputable def projectiveChartPoint (n : ℕ) (j : Fin (n + 1)) (w : Fin n → ℂ) :
    Projectivization ℂ (Fin (n + 1) → ℂ) :=
  Projectivization.mk ℂ (Fin.insertNth j 1 w) (projectiveChartVector_ne_zero n j w)

open Classical in
/-- A section expressed in the standard chart, with zero outside its open domain.
Only its germs at points of that domain are tested for analyticity.
Source: Serre, GAGA, nos. 1--2 and 13, Lemma 4
(blueprint: def-sfb-projective-holomorphic-module). -/
noncomputable def projectiveSectionCoordinates (n : ℕ)
    {X : Type u} [TopologicalSpace X]
    (e : X ≃ Projectivization ℂ (Fin (n + 1) → ℂ))
    (U : Opens X) (f : U → ℂ) (j : Fin (n + 1)) (w : Fin n → ℂ) : ℂ :=
  if h : e.symm (projectiveChartPoint n j w) ∈ U then
    f ⟨e.symm (projectiveChartPoint n j w), h⟩ else 0

/-- A fully specified presentation of the holomorphic structure sheaf as a module over
constant complex coefficients on analytic projective `n`-space. The quotient topology,
standard chart formulas, all section ranges, restriction maps and scalar actions are fixed.
Source: Serre, GAGA, nos. 1--2 and 13, Lemma 4
(blueprint: def-sfb-projective-holomorphic-module). -/
structure ProjectiveHolomorphicModule (n : ℕ) where
  /-- The ringed space with the constant complex coefficient sheaf. -/
  coefficients : AlgebraicGeometry.RingedSpace.{u}
  /-- Its points are lines in complex `(n+1)`-space. -/
  points : coefficients ≃ Projectivization ℂ (Fin (n + 1) → ℂ)
  /-- Its topology is exactly the quotient topology on nonzero homogeneous vectors. -/
  quotientMap : IsQuotientMap
    (fun z : {z : Fin (n + 1) → ℂ // z ≠ 0} => points.symm (Projectivization.mk' ℂ z))
  /-- The coefficient sections are exactly locally constant complex functions. -/
  coefficientEval : ∀ U : Opens coefficients,
    coefficients.presheaf.obj (op U) ≃+* LocallyConstant U ℂ
  /-- The coefficient identification is an identification of sheaves. -/
  coefficientRestrict : ∀ (U V : Opens coefficients) (h : V ≤ U)
    (a : coefficients.presheaf.obj (op U)) (x : V),
    coefficientEval V (coefficients.presheaf.map (homOfLE h).op a) x =
      coefficientEval U a ⟨x.val, h x.property⟩
  /-- The holomorphic structure sheaf, regarded as a module over the constant sheaf. -/
  holomorphic : SheafOfModules.{u} (AlgebraicGeometry.moduleRings coefficients)
  /-- Section evaluation preserves the pointwise additive operations. -/
  eval : ∀ U : Opens coefficients, holomorphic.val.obj (op U) →+ (U → ℂ)
  /-- Sections are determined by their functions. -/
  eval_injective : ∀ U : Opens coefficients, Function.Injective (eval U)
  /-- Precisely the functions analytic in every standard projective chart occur. -/
  eval_range : ∀ (U : Opens coefficients) (f : U → ℂ),
    (∃ a, eval U a = f) ↔
      ∀ (j : Fin (n + 1)) (w : Fin n → ℂ),
        points.symm (projectiveChartPoint n j w) ∈ U →
          AnalyticAt ℂ (projectiveSectionCoordinates n points U f j) w
  /-- The action of constant-sheaf sections is pointwise complex multiplication. -/
  eval_smul : ∀ (U : Opens coefficients) (a : coefficients.presheaf.obj (op U))
    (s : holomorphic.val.obj (op U)) (x : U),
    eval U (a • s) x = coefficientEval U a x * eval U s x
  /-- Module restriction is restriction of functions. -/
  eval_restrict : ∀ (U V : Opens coefficients) (h : V ≤ U)
    (s : holomorphic.val.obj (op U)) (x : V),
    eval V (holomorphic.val.map (homOfLE h).op s) x = eval U s ⟨x.val, h x.property⟩

end ComplexGeometry
