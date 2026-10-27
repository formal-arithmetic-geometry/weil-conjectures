/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.AlgebraicGeometry.RelativeProjectiveSpace
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.AlgebraicGeometry.AmpleImmersionAffineBase
import WeilConjectures.AlgebraicGeometry.AmpleTwistGlobalGeneration
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Product
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.SegreTwist
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Sheaf.AlgebraicGeometry.ClosedImmersionProducts
import Sheaf.AlgebraicGeometry.SectionsMorphismToProjPolynomialRing
import Sheaf.AlgebraicGeometry.CoherentFiniteType

/-! # Eventual projective immersions from an ample module

Source: Stacks Project, Morphisms, Lemma 01VS, first and final paragraphs
(blueprint: lem-trf-affine-eventual-power-immersion).

The target is the recorded symmetric-algebra relative Proj. Over the affine base its
restriction to the whole base identifies it with the recorded local Proj. The inner
tensor pullback in the conclusion transports the existing `Proj.twist` through this
specified chart; it is the degree-one twist of the relative projective space.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- Every sufficiently large tensor power of an ample invertible module on a scheme
locally of finite type over an affine base is induced by an immersion into projective
space over that base.

Source: Stacks Project, Morphisms, Lemma 01VS, first and final paragraphs; Properties,
Proposition 01Q3; Constructions, Lemma 01WD
(blueprint: lem-trf-affine-eventual-power-immersion).

Proof, following the node's five steps:
1. By `lem-weil-pbc-ample-very-ample-immersion-affine-base`, fix a positive exponent a
and an immersion pulling O(1) back to L^a.
2. The structure module is quasi-coherent of finite type (`pqf-def-coherent`). Apply
`lem-weil-pbc-coherent-twist-global-generation` to it. The tensor-unit comparison gives
finite generating sections of L^e for all e at least a bound b, enlarged to be positive.
Set d0 = a + b.
3. For d at least d0 put e = d - a. Choose finitely many generators of L^e, padding
with a zero section to have q at least one. In every rank-one stalk one coefficient
is a unit, so their nonvanishing loci cover. Tensor powers remain invertible by
`lem-weil-pbc-invertible-pullback-tensor`. Apply
`lem-weil-pbc-sections-morphism-to-proj-polynomial-ring` to obtain the residual map
to projective (q-1)-space with pullback L^e. Use the specified affine polynomial
identification of `def-nagata-relative-projective-space` for its relative-Proj model.
4. The tuple with the fixed immersion is an immersion by `lem-chow-tuple-immersion`.
Compose with the Segre closed immersion (`lem-chow-segre`). Explicitly, factor the
tuple as a closed immersion into an open U of the product. Choose an ambient open V
whose inverse image under Segre is U. By `lem-weil-pbc-closed-immersion-base-change`,
U to V is closed; compose closed immersions by `lem-weil-pbc-closed-immersion-products`
and follow by the open inclusion. This supplies j_d over the base, with dimension
(m+1)q-1, a nonnegative integer.
5. By `lem-trf-segre-hyperplane-pullback` and the tensor/composition pullback comparisons
of `lem-weil-pbc-invertible-pullback-tensor`, the pullback of O(1) is L^a tensor L^e.
Associativity (`def-pur-sheaf-tensor-product`) identifies it with L^d. For empty T the
padding allows q=1; for A=0, any T over Spec A is empty. Thus both cases are included.
-/
theorem exists_eventual_power_immersion
    (A : Type u) [CommRing A] (T : Scheme.{u})
    (f : T ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (L : T.Modules) [L.IsInvertible] (hL : IsAmple T L) :
    ∃ d₀ : ℤ, 1 ≤ d₀ ∧ ∀ d : ℤ, d₀ ≤ d →
      ∃ r_d : ℕ, ∃ j_d : T ⟶ RelativeProjectiveSpace.scheme (Spec (.of A)) r_d,
        IsImmersion j_d ∧
        j_d ≫ RelativeProjectiveSpace.π (Spec (.of A)) r_d = f ∧
        Nonempty ((tensorPullback j_d).obj
          ((tensorPullback
            ((RelativeProjectiveSpace.scheme (Spec (.of A)) r_d).topIso.inv ≫
              ((RelativeProjectiveSpace.construction (Spec (.of A)) r_d).restrictionIso
                ⟨⊤, isAffineOpen_top (Spec (.of A))⟩).hom)).obj
            (@Proj.twist _ _ _ _ _
              ((RelativeProjectiveSpace.algebra (Spec (.of A)) r_d).sectionGrade
                ⟨⊤, isAffineOpen_top (Spec (.of A))⟩)
              (RelativeProjAlgebra.sectionGradedRing _ _) 1)) ≅
          L.tensorPow d.toNat) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
