/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q74
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.GeneralBorelFlagVariety
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousOrbitQuotientGeometry
import Sheaf.AlgebraicGeometry.CocharacterConjugateMaximalTorus
import Sheaf.AlgebraicGeometry.GroupScheme.SmoothGroupOrbitGeometry
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.Mathlib.RingTheory.Nullstellensatz
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-! # Luna's affine attraction neighbourhoods on the Borel variety

Source: Milne, Algebraic Groups (2017), Theorem 17.65 and proof, printed p.374.
(blueprint: lem-sfb-luna-borel-attraction-charts)

The flag presentation is exactly the data and properties supplied by
`exists_general_borel_flag_variety`. No choice from an unproved existence is used.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- Each Borel containing a maximal torus has an affine attraction neighbourhood,
stable under any smooth connected unipotent subgroup contained in all such Borels.
The complement is invariant on all underlying topological points, under V(k).
The restricted action is specified by its composite with the open immersion; its
unit and multiplication identities follow by cancellation of that immersion.

Source: Milne, Theorem 17.65 and proof, printed p.374.
(blueprint: lem-sfb-luna-borel-attraction-charts)

Proof:
1. Use lem-sfb-general-borel-flag-variety and
   lem-sfb-homogeneous-orbit-quotient-geometry to identify X with G/B. Obtain a
   projective equivariant embedding and an isolated cocharacter action from
   lem-sfb-general-flag-isolated-linear-action. Conjugate into T by
   lem-sfb-cocharacter-conjugate-maximal-torus; X^T is finite reduced nonempty.
2. Replace the representation by the span of X(k). It is a subrepresentation by
   lem-sfb-smooth-group-rational-point-subspace-test. Smoothness implies reducedness by
   sbc-lem-smooth-geometrically-reduced. The vanishing principle of
   lem-wf-affine-nullstellensatz-vanishing makes the embedding factor through this span.
   Apply lem-sfb-torus-extreme-weight-affine-chart to obtain a minimum weight line,
   its dual coordinate f₀ and the affine open with the stated orbit-closure description.
3. By lem-sfb-torus-normalizer-borel-transitivity, translate the attracting point to b_B
   by an element normalizing T. Conjugate the cocharacter and the weight coordinates.
   Normalization of T preserves exactly the orbit-closure description.
4. In the dual projective space, every orbit meets the complement of the hyperplane
   orthogonal to the minimum weight vector: otherwise a nonzero functional annihilates
   its G-translates, which span the representation. The inverse cocharacter contracts
   that affine complement to [f₀]. By lem-sfb-smooth-group-orbit-geometry the orbit of
   [f₀] has invariant closed boundary. If the boundary were nonempty, the
   Nullstellensatz would supply a rational point; translate it into the affine complement.
   Its limit would put [f₀] in the boundary, a contradiction. Thus the dual orbit is
   closed, and proper by lem-pc-projective-proper.
5. Apply lem-sfb-proper-homogeneous-torus-borel-stabilizer to this proper orbit and its
   T-fixed dual line. Its stabilizer contains a Borel C containing T. The containment
   hypothesis puts V in C. On every algebra, V acts on the direct summand line Af₀ by
   a unit. Hence it preserves f₀ ≠ 0 and its hyperplane complement. Restrict the action
   by the equivariant embedding. For v ∈ V(k), both v and v⁻¹ preserve the complement,
   giving equality of its image with itself. No normality of V in G is used.
-/
theorem exists_luna_borel_attraction_chart {k : Type u} [Field k] [IsAlgClosed k]
    (G : Grp (Over (Spec (.of k)))) (hG : SolvableGroupStructure.IsAlgebraic G)
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (X : Mod (Over (Spec (.of k))) G.X)
    (b : {B : Subobject G.X // ∃ h : GrpObj (B : Over (Spec (.of k))),
      @IsBorelGroupScheme k _ _ G.X (B : Over (Spec (.of k))) G.grp h B.arrow} ≃
        (𝟙_ (Over (Spec (.of k))) ⟶ X.X))
    (hflag : Nonempty X.X.left ∧ Smooth X.X.hom ∧ ConnectedSpace X.X.left ∧
      IsHProjective X.X.hom ∧ LocallyOfFiniteType X.X.hom ∧ QuasiCompact X.X.hom ∧
      IsProper X.X.hom ∧ IsSeparated X.X.hom ∧
      (∀ x y : 𝟙_ (Over (Spec (.of k))) ⟶ X.X,
        ∃ g : 𝟙_ (Over (Spec (.of k))) ⟶ G.X, g • x = y) ∧
      (∀ B C, ∀ g : 𝟙_ (Over (Spec (.of k))) ⟶ G.X,
        b C = g • b B ↔
          ∀ (A : Type u) [CommRing A] [Algebra k A]
            (z : StandardGroupSchemes.affine k A ⟶ G.X),
            (∃ c : StandardGroupSchemes.affine k A ⟶ (C.val : Over (Spec (.of k))),
              c ≫ C.val.arrow = z) ↔
            ∃ t : StandardGroupSchemes.affine k A ⟶ (B.val : Over (Spec (.of k))),
              t ≫ B.val.arrow =
                (toUnit (StandardGroupSchemes.affine k A) ≫ g)⁻¹ * z *
                  (toUnit (StandardGroupSchemes.affine k A) ≫ g)) ∧
      (∀ B, ∀ (A : Type u) [CommRing A] [Algebra k A]
          (g : StandardGroupSchemes.affine k A ⟶ G.X),
        g • (toUnit (StandardGroupSchemes.affine k A) ≫ b B) =
            toUnit (StandardGroupSchemes.affine k A) ≫ b B ↔
          ∃ t : StandardGroupSchemes.affine k A ⟶ (B.val : Over (Spec (.of k))),
            t ≫ B.val.arrow = g) ∧
      (∀ (T : Grp (Over (Spec (.of k)))) (i : T ⟶ G),
        IsClosedSubgroupScheme i.hom.hom → SolvableGroupStructure.IsTorus T →
          ∃ x : 𝟙_ (Over (Spec (.of k))) ⟶ X.X,
            ∃ j : T.X ⟶ ((b.symm x).val : Over (Spec (.of k))),
              j ≫ (b.symm x).val.arrow = i.hom.hom) ∧
      (∀ (T : Grp (Over (Spec (.of k)))) (i : T ⟶ G),
        IsClosedSubgroupScheme i.hom.hom → SolvableGroupStructure.IsTorus T → ∀ B,
          (∀ (A : Type u) [CommRing A] [Algebra k A]
            (t : StandardGroupSchemes.affine k A ⟶ T.X),
            (t ≫ i.hom.hom) • (toUnit (StandardGroupSchemes.affine k A) ≫ b B) =
              toUnit (StandardGroupSchemes.affine k A) ≫ b B) ↔
          ∃ j : T.X ⟶ (B.val : Over (Spec (.of k))), j ≫ B.val.arrow = i.hom.hom))
    (T : Grp (Over (Spec (.of k)))) (iT : T ⟶ G)
    (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (V : Grp (Over (Spec (.of k)))) (iV : V ⟶ G)
    (hValg : SolvableGroupStructure.IsAlgebraic V)
    (hVclosed : IsClosedSubgroupScheme iV.hom.hom)
    [ConnectedSpace V.X.left] (hVuni : SolvableGroupStructure.IsUnipotent V)
    (hV : ∀ (C : {C : Subobject G.X // ∃ h : GrpObj (C : Over (Spec (.of k))),
        @IsBorelGroupScheme k _ _ G.X (C : Over (Spec (.of k))) G.grp h C.arrow}),
      (∃ j : T.X ⟶ (C.val : Over (Spec (.of k))),
        j ≫ C.val.arrow = iT.hom.hom) →
      ∃ j : V.X ⟶ (C.val : Over (Spec (.of k))), j ≫ C.val.arrow = iV.hom.hom)
    (B : {B : Subobject G.X // ∃ h : GrpObj (B : Over (Spec (.of k))),
      @IsBorelGroupScheme k _ _ G.X (B : Over (Spec (.of k))) G.grp h B.arrow})
    (hTB : ∃ j : T.X ⟶ (B.val : Over (Spec (.of k))),
      j ≫ B.val.arrow = iT.hom.hom) :
    ∃ U : X.X.left.Opens, IsAffineOpen U ∧
      (∀ B', (b B').left (IsLocalRing.closedPoint k) ∈ U ↔
        (b B).left (IsLocalRing.closedPoint k) ∈
          closure (Set.range (fun t : 𝟙_ (Over (Spec (.of k))) ⟶ T.X ↦
            ((t ≫ iT.hom.hom) • b B').left (IsLocalRing.closedPoint k)))) ∧
      (∃ a : V.X ⊗ Over.mk (U.ι ≫ X.X.hom) ⟶ Over.mk (U.ι ≫ X.X.hom),
        a ≫ Over.homMk U.ι =
          (iV.hom.hom ⊗ₘ Over.homMk U.ι) ≫ γ[G.X, X.X]) ∧
      (∀ v : 𝟙_ (Over (Spec (.of k))) ⟶ V.X,
        Set.image (lift (toUnit X.X ≫ v ≫ iV.hom.hom) (𝟙 X.X) ≫ γ[G.X, X.X]).left
          ((U : Set X.X.left)ᶜ) = (U : Set X.X.left)ᶜ) := by
  sorry

end AlgebraicGeometry
