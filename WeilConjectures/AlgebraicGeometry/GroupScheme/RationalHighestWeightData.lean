/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StandardGroupSchemes
public import WeilConjectures.AlgebraicGeometry.HopfCoactionLinearization
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Coaction subspaces, highest lines and canonical contragredients

Source: Milne, Algebraic Groups (2017), Sections 4a--4b, Theorem 22.18, and
"The highest weight of the contragredient representation", p.471.
(blueprint: def-sfb-rational-highest-weight-data)

Rationality uses the existing HopfAction.Coassociative and HopfAction.Counital
predicates on an unbundled linear map. This module adds the subspace and character
notions needed to state the highest-weight theorem. Coordinate rings, group objects,
the Hopf structure and the multiplicative group are the existing canonical objects.
The dual predicate determines its coaction by every contraction, so its existential
use in the highest-weight theorem cannot choose an unrelated dual representation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct MonObj
namespace AlgebraicGeometry.RationalHighestWeight
variable {F : Type u} [Field F]
variable (G : Grp (Over (Spec (.of F)))) [IsAffine G.X.left]
/-- The actual ring of global functions, not a separately chosen coordinate algebra.
Source: Milne, Sections 3a and 4a (blueprint: def-sfb-rational-highest-weight-data). -/
abbrev coordinateAlgebra : Type u := Γ(G.X.left, ⊤)
/-- Expose the given bundled group law on its scheme with the given structure map.
Source: Milne, Section 3a (blueprint: def-sfb-rational-highest-weight-data). -/
instance coordinateOverGroup : GrpObj (G.X.left.asOver (Spec (.of F))) := G.grp
/-- Reuse the canonical affine coordinate Hopf structure, with the field unbundled.
Source: Milne, Sections 3a and 4a; Mathlib Group/Affine
(blueprint: def-sfb-rational-highest-weight-data). -/
instance coordinateHopf : HopfAlgebra F (coordinateAlgebra G) :=
  HopfAction.coordinateHopfAlgebra F G.X.left
/-- The recorded multiplicative group is the affine spectrum of Laurent polynomials.
Source: Milne, Section 2a (blueprint: def-sfb-rational-highest-weight-data). -/
instance multiplicativeAffine :
    IsAffine (StandardGroupSchemes.multiplicative F).left :=
  inferInstanceAs (IsAffine (Spec (.of (LaurentPolynomial F))))
variable {H : Grp (Over (Spec (.of F)))} [IsAffine H.X.left]
/-- Pullback of regular functions along a morphism over F preserves the F-scalars.
This verifies the proof field of coordinateMap; its ring-map data is appTop.
Source: Milne, Sections 3a and 4a (blueprint: def-sfb-rational-highest-weight-data).

Proof: the affine global-section algebra map is the pullback of scalars along the
structure map, expressed through the canonical Spec/global-sections isomorphism.
The over-category square gives i followed by G's structure map equal to H's
structure map. Apply the contravariant global-sections functor, evaluate at the
scalar a, and use its composition law. The two sides are exactly the displayed
algebra maps, including the canonical affine identifications used by the Hopf API. -/
theorem coordinateMap_commutes {G : Grp (Over (Spec (.of F)))} [IsAffine G.X.left]
    (i : H ⟶ G) (a : F) :
    i.hom.hom.left.appTop.hom (algebraMap F (coordinateAlgebra G) a) =
      algebraMap F (coordinateAlgebra H) a := by
  sorry

/-- Canonical pullback of functions along the given group-scheme morphism.
Source: Milne, Sections 3a and 4a (blueprint: def-sfb-rational-highest-weight-data). -/
def coordinateMap {G : Grp (Over (Spec (.of F)))} [IsAffine G.X.left]
    (i : H ⟶ G) : coordinateAlgebra G →ₐ[F] coordinateAlgebra H :=
  { i.hom.hom.left.appTop.hom with commutes' := coordinateMap_commutes i }

variable {V : Type v} [AddCommGroup V] [Module F V]
variable {G}

/-- A rational subspace: c(N) lies in the image of N tensor F[G]. Over a field
that tensor inclusion is injective, so this is precisely the subspace condition.
Source: Milne, Section 4a (blueprint: def-sfb-rational-highest-weight-data). -/
def IsStable (c : V →ₗ[F] V ⊗[F] coordinateAlgebra G) (N : Submodule F V) : Prop :=
  ∀ v ∈ N, c v ∈ LinearMap.range (N.subtype.rTensor (coordinateAlgebra G))
/-- A nonzero rational module whose only rational subspaces are zero and itself.
Source: Milne, Section 4b and Theorem 22.18
(blueprint: def-sfb-rational-highest-weight-data). -/
def IsSimple (c : V →ₗ[F] V ⊗[F] coordinateAlgebra G) : Prop :=
  Nontrivial V ∧ ∀ N : Submodule F V, IsStable c N → N = ⊥ ∨ N = ⊤
/-- Subgroup invariants as the equalizer of the restricted and trivial coactions.
This retains invariance over all scalar extensions, including nonreduced algebras.
Source: Milne, Section 4a and Theorem 22.18
(blueprint: def-sfb-rational-highest-weight-data). -/
def invariants (c : V →ₗ[F] V ⊗[F] coordinateAlgebra G) {H : Grp (Over (Spec (.of F)))}
    [IsAffine H.X.left]
    (i : H ⟶ G) : Submodule F V :=
  LinearMap.eqLocus ((coordinateMap i).toLinearMap.lTensor V ∘ₗ c)
    ((TensorProduct.mk F V (coordinateAlgebra H)).flip 1)
/-- The group-like regular function associated to the actual character T to G_m:
pull back the Laurent coordinate t along that character.
Source: Milne, Section 12b (blueprint: def-sfb-rational-highest-weight-data). -/
def characterElement {T : Grp (Over (Spec (.of F)))}
    [IsAffine T.X.left]
    (χ : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)) : coordinateAlgebra T :=
  (coordinateMap χ) ((Scheme.ΓSpecIso (.of (LaurentPolynomial F))).inv
    (LaurentPolynomial.T 1))
/-- The U-invariants form a line on which T acts by the specified character.
The second clause is the character coaction identity on that entire line.
Source: Milne, Theorem 22.18 (blueprint: def-sfb-rational-highest-weight-data). -/
def HasHighestWeight (c : V →ₗ[F] V ⊗[F] coordinateAlgebra G)
    {T U : Grp (Over (Spec (.of F)))} [IsAffine T.X.left] [IsAffine U.X.left]
    (iT : T ⟶ G) (iU : U ⟶ G)
    (χ : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)) : Prop :=
  Module.finrank F (invariants c iU) = 1 ∧
    ∀ v ∈ invariants c iU,
      (coordinateMap iT).toLinearMap.lTensor V (c v) = v ⊗ₜ[F] characterElement χ
/-- The canonical contragredient coaction, characterized by contraction:
for all f and v, evaluating d(f) at v equals applying the antipode to the
contraction of c(v) with f. In coordinates this is the inverse-transpose matrix;
evaluation at every algebra-valued point gives (g f)(v) = f(g inverse v).
All contractions determine a tensor in V dual tensor F[G] when V is finite-dimensional.
Source: Milne, contragredient paragraph following 22.31, p.471
(blueprint: def-sfb-rational-highest-weight-data). -/
def IsContragredient (c : V →ₗ[F] V ⊗[F] coordinateAlgebra G)
    (d : Module.Dual F V →ₗ[F] Module.Dual F V ⊗[F] coordinateAlgebra G) : Prop :=
  ∀ (f : Module.Dual F V) (v : V),
    (TensorProduct.lid F (coordinateAlgebra G))
        (((LinearMap.applyₗ v).rTensor (coordinateAlgebra G)) (d f)) =
      HopfAlgebra.antipode F
        ((TensorProduct.lid F (coordinateAlgebra G))
          ((f.rTensor (coordinateAlgebra G)) (c v)))

end AlgebraicGeometry.RationalHighestWeight
