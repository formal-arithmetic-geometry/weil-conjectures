/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Topology.Sober
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometryCore

/-! # Generic descent of the square difference over a normal integral base

Source: Guo, Divisors on coherent schemes and homogeneous spaces, Section 5.1 and
Proposition 5.2(i), March 31, 2026 version, printed pages 11--12; Stacks Project,
Tag 0BD7 (blueprint: lem-sfb-normal-product-square-descent).

The coordinate maps and square difference below are actual product maps and tensor
constructions. Products in `Over S` are fibre products, as witnessed by
`Over.prodLeftIsoPullback`. The two inverse factors use the internal Hom into the
structure sheaf.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- The parameter scheme `P = (X₁ ×[S] X₁) ×[S] (X₂ ×[S] X₂)` over `S`.
Source: Guo, Section 5.1, reordered coordinates of `W ×[S] W`
(blueprint: lem-sfb-normal-product-square-descent). -/
noncomputable abbrev squareParameter {S : Scheme.{u}} (X₁ X₂ : Over S) : Over S :=
  (X₁ ⨯ X₁) ⨯ (X₂ ⨯ X₂)

/-- The map `(x₀,x₁,y₀,y₁,z) ↦ (xₐ,y_b,z)`, where `false` denotes index zero
and `true` denotes index one. Both coordinates are selected by product projections.
Source: Guo, Section 5.1 (blueprint: lem-sfb-normal-product-square-descent). -/
noncomputable def squareCoordinate {S : Scheme.{u}} (X₁ X₂ X₃ : Over S) (a b : Bool) :
    squareParameter X₁ X₂ ⨯ X₃ ⟶ (X₁ ⨯ X₂) ⨯ X₃ :=
  prod.map
    (prod.lift
      (prod.fst ≫ (if a then prod.snd else prod.fst))
      (prod.snd ≫ (if b then prod.snd else prod.fst)))
    (𝟙 X₃)

/-- The square difference `r₀₀* A ⊗ r₁₁* A ⊗ (r₀₁* A)ᵛ ⊗ (r₁₀* A)ᵛ`.
Each pullback is the recorded tensor pullback, and each dual is the internal Hom
into the tensor unit, the structure sheaf of `P ×[S] X₃`.
Source: Guo, Section 5.1 (blueprint: lem-sfb-normal-product-square-descent). -/
noncomputable def squareDifference {S : Scheme.{u}} (X₁ X₂ X₃ : Over S)
    (A : ((X₁ ⨯ X₂) ⨯ X₃).left.Modules) :
    (squareParameter X₁ X₂ ⨯ X₃).left.Modules :=
  (tensorPullback (squareCoordinate X₁ X₂ X₃ false false).left).obj A ⊗
    (tensorPullback (squareCoordinate X₁ X₂ X₃ true true).left).obj A ⊗
    SheafOfModules.homObj (R := (squareParameter X₁ X₂ ⨯ X₃).left.sheaf)
      ((tensorPullback (squareCoordinate X₁ X₂ X₃ false true).left).obj A) (𝟙_ _) ⊗
    SheafOfModules.homObj (R := (squareParameter X₁ X₂ ⨯ X₃).left.sheaf)
      ((tensorPullback (squareCoordinate X₁ X₂ X₃ true false).left).obj A) (𝟙_ _)

/-- The parameter projection `π : P ×[S] X₃ → P`.
Source: Guo, Section 5.1 (blueprint: lem-sfb-normal-product-square-descent). -/
noncomputable abbrev squareProjection {S : Scheme.{u}} (X₁ X₂ X₃ : Over S) :
    squareParameter X₁ X₂ ⨯ X₃ ⟶ squareParameter X₁ X₂ :=
  prod.fst

/-- The square difference descends from `P` if it descends after restriction to
`Spec k(S)`. Local finite presentation and quasi-compactness, together with
separatedness (hence quasi-separatedness), express finite presentation.
Normality is stated on all local rings, and geometric integrality includes the
nonemptiness of every residue-field fibre.

Source: Guo, Proposition 5.2(i), March 31, 2026 version, printed pages 11--12;
Stacks Project, Tag 0BD7 (blueprint: lem-sfb-normal-product-square-descent).

Proof plan:
1. Form the successive products S, X₁, X₁ ×[S] X₁, its product with X₂, and
   its second product with X₂, namely P. The projections are smooth by
   lem-pc-proper-base-change, with nonempty geometrically integral fibres by
   base change. Apply lem-sbc-smooth-connected-generic-geometry-core at each
   stage to obtain normal integral products. Smooth maps are locally of finite
   presentation by lem-pc-smooth-flat, hence locally of finite type. The lemma
   pqf-lem-locnoeth-lft gives local Noetherianity at each stage. Nonempty fibres
   also make P → S surjective.
2. For Y = P ×[S] X₃, the projection π is smooth, hence flat and locally of
   finite presentation (lem-pc-proper-base-change and lem-pc-smooth-flat).
   The lemma pqf-lem-locnoeth-lft makes Y locally Noetherian. Every fibre over
   p in P is the field extension of the given fibre of X₃, hence integral and
   nonempty.
3. The generic point ξ of P maps to the generic point of S: surjectivity and
   specialization show that its image is generic. Thus Spec k(P) → P factors
   through Pη. Pull back the assumed isomorphism along Yξ → Yη, using
   def-pc-module-pullback. The pullback of Nη to Spec k(P) is a one-dimensional
   vector space and hence trivial. Therefore D(A) is trivial over Yξ. Tensoring
   pulled-back local frames and dual frames proves D(A) invertible
   (def-sc-invertible-module).
4. Apply lem-sfb-normal-noetherian-generic-line-pullback to π and D(A), with
   the locally-of-finite-type alternative. It gives an invertible N on P and
   π* N ≅ D(A). Invert this isomorphism for the displayed conclusion.
-/
theorem normal_product_square_descent
    {S : Scheme.{u}} [IsIntegral S] [IsLocallyNoetherian S]
    (hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    (X₁ X₂ X₃ : Over S)
    [Smooth X₁.hom] [IsSeparated X₁.hom] [LocallyOfFinitePresentation X₁.hom]
    [QuasiCompact X₁.hom] [GeometricallyIntegral X₁.hom]
    [Smooth X₂.hom] [IsSeparated X₂.hom] [LocallyOfFinitePresentation X₂.hom]
    [QuasiCompact X₂.hom] [GeometricallyIntegral X₂.hom]
    [Smooth X₃.hom] [IsSeparated X₃.hom] [LocallyOfFinitePresentation X₃.hom]
    [QuasiCompact X₃.hom] [GeometricallyIntegral X₃.hom]
    (A : ((X₁ ⨯ X₂) ⨯ X₃).left.Modules) [IsInvertible A]
    (hη : ∃ Nη : (Limits.pullback (squareParameter X₁ X₂).hom
        (S.fromSpecStalk (genericPoint S))).Modules,
      IsInvertible Nη ∧
        Nonempty
          ((tensorPullback (pullback.fst (squareParameter X₁ X₂ ⨯ X₃).hom
              (S.fromSpecStalk (genericPoint S)))).obj (squareDifference X₁ X₂ X₃ A) ≅
            (tensorPullback
              (((Over.pullback (S.fromSpecStalk (genericPoint S))).map
                (squareProjection X₁ X₂ X₃)).left)).obj Nη)) :
    ∃ N : (squareParameter X₁ X₂).left.Modules,
      IsInvertible N ∧
        Nonempty (squareDifference X₁ X₂ X₃ A ≅
          (tensorPullback (squareProjection X₁ X₂ X₃).left).obj N) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
