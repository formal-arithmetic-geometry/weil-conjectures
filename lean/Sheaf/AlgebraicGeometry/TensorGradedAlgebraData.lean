/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Sheaf.CategoryTheory.CommAlgebraSheafModule
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Graded algebra and quotient of tensor powers

Source: Stacks Project, Tag 09MS, the direct-sum algebra sequence.
(blueprint: lem-sc-tensor-graded-algebra-data).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
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

/-- The two graded algebra sheaves, with their underlying module coproducts.
No exactness, kernel, or degree projection data are included.
Source: Stacks Project, Tag 09MS, the direct-sum algebra sequence.
(blueprint: lem-sc-tensor-graded-algebra-data). -/
structure TensorGradedAlgebraData {X Z : Scheme.{u}} (j : Z ⟶ X)
    (L : X.Modules) where
  B : X.CommAlgebraSheaf
  C : X.CommAlgebraSheaf
  p : B ⟶ C
  b : ∀ d : ℕ, L.tensorPow d ⟶ commAlgebraSheafModule X.sheaf B
  c : ∀ d : ℕ,
    (pushforward j).obj ((tensorPullback j).obj (L.tensorPow d)) ⟶
      commAlgebraSheafModule X.sheaf C
  b_colimit : IsColimit (Cofan.mk (commAlgebraSheafModule X.sheaf B) b)
  c_colimit : IsColimit (Cofan.mk (commAlgebraSheafModule X.sheaf C) c)
  b_quotient : ∀ d : ℕ, b d ≫ tensorGradedAlgebraMap p =
    tensorGradedUnit j (L.tensorPow d) ≫ c d
  b_multiply : ∀ (U : X.Opens) (a d : ℕ) (s : Γ(L.tensorPow a, U))
    (t : Γ(L.tensorPow d, U)),
    tensorGradedAlgebraSection B U ((b a).app U s) *
      tensorGradedAlgebraSection B U ((b d).app U t) =
      tensorGradedAlgebraSection B U
        ((b (a + d)).app U ((L.tensorPowAddIso a d).inv.app U (tmulSection s t)))

/-- The tensor powers and their restrictions form a graded algebra quotient.
Source: Stacks Project, Tag 09MS, the direct-sum sequence after coherent-equation-ses.
Proof: on a frame open for L, form the polynomial algebra O_X[T], and on its inverse
image form O_Z[T]. A change of frame by a unit u acts on degree d by u^d. These
algebra automorphisms satisfy the cocycle identities, so the polynomial algebra
sheaves and their coefficient quotient maps glue to B, C, and p. Their underlying
modules are the sheafifications of the direct sums of the tensor powers and of
j_*j^*L^d. The canonical homogeneous inclusions give b and c; the coproduct
universal properties hold locally on frames and therefore globally. Compare the
chosen tensor-pullback adjunction with the usual adjunction by uniqueness of left
adjoints. Its units differ by an invertible natural transformation on j_*j^*.
Precompose each target inclusion c_d by the inverse of this transformation. This
preserves the coproduct universal property and gives the quotient square for the
chosen tensorGradedUnit, without requiring c to preserve multiplication. On a frame,
the multiplication equation is (s T^a)(t T^d) = st T^(a+d); the transition maps preserve
it, and separation of the sheaf gives the equation on every open. This construction
uses neither square-zero of the ideal nor any kernel or projection data.
(blueprint: lem-sc-tensor-graded-algebra-data). -/
theorem tensorGradedAlgebraData_exists {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] :
    Nonempty (TensorGradedAlgebraData j L) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
