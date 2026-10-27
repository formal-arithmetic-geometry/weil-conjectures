/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q74
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousOrbitQuotientGeometry
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Algebra.Group.Subgroup.Basic

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfCoveringCalculus
import Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent
import Sheaf.AlgebraicGeometry.GeometricallyIrreducibleProduct
import WeilConjectures.RingTheory.FiniteTypeDomainDimensionTrdeg
import Sheaf.AlgebraicGeometry.FlatCompositeFibreDimensionAtPoint
import WeilConjectures.AlgebraicGeometry.DimensionLocallyAlgebraic
import Sheaf.AlgebraicGeometry.SchemeProductDimension
import Sheaf.DeligneLaumon.IrreducibleFibreDimensionLowerBound
import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Conjugation incidence and homogeneous quotients

Source: Milne, Algebraic Groups (2017), Lemma 17.32(a),(b), printed pp.361--362
(blueprint: lem-sfb-subgroup-conjugation-incidence-criterion).

The two conclusions concern rational points. No topology on the rational-point
set is substituted for the Zariski topology of the scheme.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- The conjugates of H(k) are the rational points of a closed subset when G/H is
proper. If an element of H(k) has finitely many fixed rational cosets, the conjugates
contain all rational points of a nonempty open subscheme, without assuming properness.

The quotient is supplied by `exists_homogeneous_fppf_quotient`: `hcoset` is its
kernel-pair criterion on test schemes, `hlift` its rational lifting property, and
`hequiv` specifies its canonical left action. `Group.conjugatesOfSet` is the existing
abstract conjugacy saturation, applied to the image of H(k) in G(k).

Source: Milne, Algebraic Groups (2017), Lemma 17.32(a),(b), printed pp.361--362
(blueprint: lem-sfb-subgroup-conjugation-incidence-criterion).

Proof, following the nine steps of the node:
1. Form I in X × G by pulling back the diagonal of X along (x,a) ↦ (a x,x).
   Separatedness makes I closed; finite-type composition, base change and
   lem-weil-pbc-proper-fp-permanence make I finite type and I → G locally finite type.
2. The quotient criterion identifies G × H with I ×_X G by
   (g,h) ↦ ((q(g),g h g⁻¹),g). The inverse is ((x,a),g) ↦ (g,g⁻¹ a g).
   The quotient is locally finitely presented by finite-type cancellation and
   pqf-lem-lft-fp-locnoeth. The fppf covering calculus then makes G × H → I flat,
   surjective and locally finitely presented. Its composite to G is conjugation.
3. The identity-component theorem makes G and H geometrically irreducible.
   The geometrically irreducible product theorem and surjectivity make I irreducible.
   The finite-type-domain dimension theorem makes the dimensions of G and H finite.
4. Over (q(1),1), the fibre of G × H → I is H via g ↦ (g,1).
   Apply lem-sbc-flat-composite-fibre-dimension-at-point and
   lem-sc-dimension-locally-algebraic. The product dimension theorem gives
   dim G + dim H = dim H + dim I, hence dim I = dim G.
5. The fibre I_a is a closed finite-type subscheme of X with rational points the
   fixed points of a. The Jacobson and closed-point residue-field theorems give a
   rational point in every nonempty I_a. Lift its coset to g in G(k); the quotient
   criterion gives g⁻¹ a g in H(k). Conversely, g h g⁻¹ fixes q(g). Thus the rational
   points of the incidence image are exactly the conjugacy saturation.
6. If X is proper, X × G → G is closed. Its image of I is therefore closed, and
   step 5 identifies its rational points with the saturation.
7. For h₀ as in the second assertion, I_h₀ is nonempty since q(1) is fixed.
   Its closed points are rational and dense. They form a finite closed subset,
   hence exhaust its topology, so its dimension is zero even if it is nonreduced.
8. Apply lem-zl-irreducible-fibre-dimension-lower-bound to I → G. The zero-dimensional
   fibre and dim I = dim G imply that the closure of its image has dimension dim G.
   Apply lem-wf-affine-dimension-drop to the integral affine reduction of G to
   conclude that this closure is G.
9. The affine fibre-product theorem identifies G × H with the spectrum of the
   tensor product of coordinate algebras. Lemma lem-wf-affine-constructible-open
   makes its conjugation image constructible and supplies a nonempty open in this
   dense image. Step 5 puts its rational points in the saturation. Properness was
   used only in step 6.
-/
theorem subgroup_conjugation_incidence_criterion
    {k : Type u} [Field k] [IsAlgClosed k]
    (G H : Over (Spec (.of k))) [GrpObj G] [GrpObj H]
    [IsAffine G.left] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [Smooth G.hom] [ConnectedSpace G.left]
    [IsAffine H.left] [LocallyOfFiniteType H.hom] [QuasiCompact H.hom]
    [Smooth H.hom] [ConnectedSpace H.left]
    (i : H ⟶ G) [IsClosedSubgroupScheme i]
    (X : Over (Spec (.of k))) [ModObj G X]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (q : G ⟶ X) [Flat q.left] [Surjective q.left]
    (hcoset : ∀ (T : Over (Spec (.of k))) (a b : T ⟶ G),
      a ≫ q = b ≫ q ↔ ∃ h : T ⟶ H, b = a * (h ≫ i))
    (hequiv : μ[G] ≫ q = lift (fst G G) (snd G G ≫ q) ≫ γ[G,X])
    (hlift : Function.Surjective (fun g : 𝟙_ (Over (Spec (.of k))) ⟶ G ↦ g ≫ q)) :
    (IsProper X.hom → ∃ Z : Set G.left, IsClosed Z ∧
      ∀ a : 𝟙_ (Over (Spec (.of k))) ⟶ G,
        a ∈ Group.conjugatesOfSet
          (Set.range (fun h : 𝟙_ (Over (Spec (.of k))) ⟶ H ↦ h ≫ i)) ↔
        a.left (IsLocalRing.closedPoint k) ∈ Z) ∧
    ((∃ h₀ : 𝟙_ (Over (Spec (.of k))) ⟶ H,
        {x : 𝟙_ (Over (Spec (.of k))) ⟶ X | (h₀ ≫ i) • x = x}.Finite) →
      ∃ V : G.left.Opens, (V : Set G.left).Nonempty ∧
        ∀ a : 𝟙_ (Over (Spec (.of k))) ⟶ G,
          a.left (IsLocalRing.closedPoint k) ∈ V →
          a ∈ Group.conjugatesOfSet
            (Set.range (fun h : 𝟙_ (Over (Spec (.of k))) ⟶ H ↦ h ≫ i))) := by
  sorry

end AlgebraicGeometry
