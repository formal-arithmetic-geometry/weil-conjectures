/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Sheaf.CategoryTheory.CommAlgebraSheafModule
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # Algebraic graded presentation of the tensor ideal sequences

Source: Stacks Project, Tag 09MS, coherent-equation-ses and its direct sum over degrees.
(blueprint: lem-sc-square-zero-tensor-graded-presentation).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
attribute [local irreducible] RingedSpace.moduleCohomology
  boundaryCoefficientCohomologyIso canonicalTensorBoundaryComparisons
noncomputable section

/-- The underlying module map, with its source and target stated explicitly.
Source: Stacks Project, Tag 09MS, the quotient in the graded ideal sequence.
(blueprint: lem-sc-square-zero-tensor-graded-presentation). -/
def tensorGradedAlgebraMap {X : Scheme.{u}} {B C : X.CommAlgebraSheaf} (p : B ⟶ C) :
    commAlgebraSheafModule X.sheaf B ⟶ commAlgebraSheafModule X.sheaf C :=
  (commAlgebraSheafModuleFunctor X.sheaf).map p

/-- Read a section of the underlying module as a section of the algebra sheaf.
Source: Stacks Project, Tag 09MS, the graded ideal sequence.
(blueprint: lem-sc-square-zero-tensor-graded-presentation). -/
def tensorGradedAlgebraSection {X : Scheme.{u}} (B : X.CommAlgebraSheaf) (U : X.Opens)
    (z : Γ(commAlgebraSheafModule X.sheaf B, U)) : B.right.obj.obj (op U) := z

attribute [local irreducible] tensorGradedAlgebraMap commAlgebraSheafModule

/-- The chosen tensor-pullback unit, with a compact explicit module-map type.
Source: Stacks Project, Tag 0096, the tensor-pullback adjunction.
(blueprint: lem-sc-square-zero-tensor-graded-presentation). -/
def tensorGradedUnit {X Z : Scheme.{u}} (j : Z ⟶ X) (M : X.Modules) :
    M ⟶ (pushforward j).obj ((tensorPullback j).obj M) :=
  (Classical.choose (exists_tensorPullbackAdjunction j)).unit.app M

attribute [local irreducible] tensorGradedUnit tensorPullback

/-- A graded algebra presentation, before taking cohomology. All its data are supplied
explicitly; this structure does not select an object from an existence theorem.
The kernel cofan expresses its graded direct sum, and the degree maps are projections.
Source: Stacks Project, Tag 09MS, the direct-sum ideal sequence.
(blueprint: lem-sc-square-zero-tensor-graded-presentation). -/
structure TensorGradedPresentation {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) where
  B : X.CommAlgebraSheaf
  C : X.CommAlgebraSheaf
  p : B ⟶ C
  I : SheafOfModules.{u} (moduleRings X.toRingedSpace)
  i : I ⟶ commAlgebraSheafModule X.sheaf B
  hw : i ≫ tensorGradedAlgebraMap p = 0
  shortExact : (ShortComplex.mk i (tensorGradedAlgebraMap p)
    hw).ShortExact
  squareZero : ∀ (U : X.Opens) (a b : B.right.obj.obj (op U)),
    p.right.hom.app (op U) a = 0 → p.right.hom.app (op U) b = 0 → a * b = 0
  b : ∀ d : ℕ, L.tensorPow d ⟶ commAlgebraSheafModule X.sheaf B
  c : ∀ d : ℕ,
    (pushforward j).obj ((tensorPullback j).obj (L.tensorPow d)) ⟶
      commAlgebraSheafModule X.sheaf C
  k : ∀ d : ℕ,
    kernel (tensorGradedUnit j (L.tensorPow d)) ⟶ I
  degree : ∀ d : ℕ,
    ShortComplex.mk i (tensorGradedAlgebraMap p) hw ⟶
      ShortComplex.kernelSequence
        (tensorGradedUnit j (L.tensorPow d))
  q : ∀ d : ℕ, commAlgebraSheafModule X.sheaf C ⟶
    (pushforward j).obj ((tensorPullback j).obj (L.tensorPow d))
  degree_quotient : ∀ d : ℕ, (degree d).τ₃ = q d
  k_colimit : IsColimit (Cofan.mk I k)
  b_quotient : ∀ d : ℕ, b d ≫ tensorGradedAlgebraMap p =
    tensorGradedUnit j (L.tensorPow d) ≫ c d
  k_inclusion : ∀ d : ℕ, k d ≫ i = kernel.ι _ ≫ b d
  c_projection : ∀ d : ℕ, c d ≫ q d = 𝟙 _
  k_projection : ∀ d : ℕ, k d ≫ (degree d).τ₁ = 𝟙 _
  k_orthogonal : ∀ a d : ℕ, a ≠ d → k a ≫ (degree d).τ₁ = 0
  b_multiply : ∀ (U : X.Opens) (a d : ℕ) (s : Γ(L.tensorPow a, U))
    (t : Γ(L.tensorPow d, U)),
    tensorGradedAlgebraSection B U ((b a).app U s) *
      tensorGradedAlgebraSection B U ((b d).app U t) =
      tensorGradedAlgebraSection B U
        ((b (a + d)).app U ((L.tensorPowAddIso a d).inv.app U (tmulSection s t)))

/-- The direct sum of the unit kernel sequences has a commutative algebra presentation.
This assertion is purely algebraic: it includes neither a cohomology boundary nor an action
on cohomology.

Source: Stacks Project, Tag 09MS, coherent-equation-ses and the following direct sum;
Tag 0B8S, the square-zero ideal in the first paragraph of the proof.
(blueprint: lem-sc-square-zero-tensor-graded-presentation).
Proof: On an open set with a frame of L, form O_X[T], the quotient
(O_X/J)[T], and its ideal J[T]. Frame changes multiply the degree-d coefficient by
the d-th power of the transition unit, and preserve both the unit and multiplication.
Glue these polynomial algebras, the quotient map, and the ideal inclusions. Their
underlying modules are the sheaf direct sums of L^d, j_*j^*L^d, and ker(eta_d).
The unit-quotient and ideal-kernel comparisons identify the degreewise sequences with
the canonical kernel sequences. Exactness of sheaf direct sums follows on stalks (AB4),
so their sum is short exact. Inclusions of the kernel summands give its colimit cofan.
Projection gives the degree morphisms; their diagonal composites with the kernel and quotient
inclusions are identities, and their off-diagonal kernel composites vanish. Multiplication
of homogeneous sections is the inverse tensor-power
addition isomorphism. Locally two ideal sections have all coefficients in J, so their
product is zero by J squared equals zero; sheaf separation extends this to every open.
For degree zero the same construction gives the structure-sheaf summand and its unitors.
No choice of frame enters the resulting maps, and no finite-type assumption is used. -/
theorem tensorGradedPresentation_exists {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥) :
    Nonempty (TensorGradedPresentation j L) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
