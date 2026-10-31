/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Borel
import WeilConjectures.AlgebraicGeometry.GroupScheme.HomogeneousQuotient
public import WeilConjectures.AlgebraicGeometry.GroupScheme.AssociatedCharacterLineBundle
public import WeilConjectures.AlgebraicGeometry.Picard.Group
import WeilConjectures.AlgebraicGeometry.SplitSolvableTorsorsAndVariety
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.AlgebraicGeometry.Descent
import WeilConjectures.AlgebraicGeometry.ProperReducedGlobalSectionsProduct

/-!
# Characteristic sequence of a Borel quotient

Source: Milne, Algebraic Groups (2017), Theorem 18.15, sequence (128), printed p.390;
its Borel-character proof in Section 18.f, pp.395--396. (blueprint:
lem-sfb-borel-characteristic-picard-sequence)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- Expose the canonical commutativity instance of the recorded Laurent Hopf group;
no group law is chosen. Source: Milne, Section 12.a, p.230.
(blueprint: lem-sfb-borel-characteristic-picard-sequence) -/
noncomputable instance borelCharacteristic_multiplicativeComm (F : Type u) [Field F] :
    IsCommMonObj (StandardGroupSchemes.multiplicative F) :=
  inferInstanceAs
    (IsCommMonObj ((Spec (.of (LaurentPolynomial F))).asOver (Spec (.of F))))

/-- Milne's characteristic sequence for a Borel quotient.

The character group `X^*(J)` is the additive copy of the group-object homomorphisms from
`J` to the canonical multiplicative group. The first map is restriction along the Borel
inclusion. For every character, the associated-character presentation records the line
bundle with action `(g,z)b = (gb,χ(b)⁻¹z)`; its Picard class is the characteristic map.
The quotient projection is a right Borel torsor, with the cartesian torsor square and
Zariski local sections stated explicitly.

Source: Milne, Algebraic Groups (2017), Theorem 18.15, sequence (128), printed p.390,
and Section 18.f, pp.395--396.

Proof (the six steps of the DAG):
1. Choose a smooth connected solvable closed subgroup of maximal dimension. Proper
   inclusions increase dimension by lem-wf-affine-dimension-drop, so it is Borel. For any
   Borel, lem-sfb-algebraic-group-homogeneous-quotient gives Q and q. The coset criterion
   identifies G × B with G ×_Q G by (g,b) ↦ (g,gb). The node
   lem-sfb-borel-quotient-proper-geometry gives smooth integral regular Noetherian geometry
   and proper Q. By lem-sfb-split-solvable-torsors-and-variety, B is split solvable and q
   admits Zariski local sections.
2. The action (g,z)b = (gb,χ(b)⁻¹z) gives descent data on the trivial line. The fpqc descent
   equivalence lem-pc-fpqc-descent constructs Lχ. Multiplication of fibre coordinates
   identifies Lχ ⊗ Lψ with L(χ+ψ), and L0 with O_Q. The frame [g,1] trivializes q*Lχ.
   If χ extends to G, the function χ(g)⁻¹ gives a global frame of Lχ on Q. Both consecutive
   composites are therefore zero.
3. Apply lem-sfb-rosenlicht-product-unit-factorization to u(xy) at (e,e). Every unit u
   with u(e)=1 on a smooth connected affine group is a character. By
   lem-weil-pbc-proper-reduced-algclosed-global-sections-product, Γ(Q,O_Q)=F. A character
   trivial on B descends along local sections to a constant unit on Q; its value at q(e)
   is 1. Thus restriction of characters is injective.
4. A global frame of Lχ pulls back to a unit t with t(gb)=χ(b)⁻¹t(g). The preceding
   normalized-unit observation makes t(g)/t(e) a character whose inverse restricts to χ.
   Thus the kernel of c is the image of restriction.
5. For a line bundle L with a frame s after pullback, write s(gb)=s(g)a(g,b). Rosenlicht
   factorization and a(g,e)=1 give a(g,b)=a(e,b). The cocycle identity makes χ(b)=a(e,b)
   a character. The invariant map (g,z) ↦ s(g)z descends by full faithfulness of fpqc
   descent to Lχ ≅ L. This proves exactness at Pic(Q).
6. Over the function field of Q, a local section identifies the generic fibre with B.
   Its Picard group is zero by lem-sfb-split-solvable-torsors-and-variety. Apply
   lem-sfb-smooth-generic-trivial-line-descent to descend each line bundle on G to Q;
   the geometry required there was obtained in step 1. Thus Picard pullback is surjective.
(blueprint: lem-sfb-borel-characteristic-picard-sequence) -/
theorem borel_characteristic_picard_sequence (F : Type u) [Field F] [IsAlgClosed F]
    (G : Grp (Over (Spec (.of F))))
    [IsAffine G.X.left] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] :
    (∃ (B₀ : Grp (Over (Spec (.of F)))) (i₀ : B₀ ⟶ G),
      IsBorelGroupScheme i₀.hom.hom) ∧
    ∀ (B : Grp (Over (Spec (.of F)))) (i : B ⟶ G),
      IsBorelGroupScheme i.hom.hom →
      ∃ (Q : Over (Spec (.of F))) (q : G.X ⟶ Q),
        IsPullback (fst G.X B.X) (fst G.X B.X * (snd G.X B.X ≫ i.hom.hom)) q q ∧
        (∀ x : Q.left, ∃ (U : Over (Spec (.of F))) (j : U ⟶ Q) (s : U ⟶ G.X),
          IsOpenImmersion j.left ∧ x ∈ Set.range j.left.base ∧ s ≫ q = j) ∧
        ∃ c : Additive (B ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)) →+
            Additive Q.left.Pic,
          (∀ χ : Additive (B ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
            ∃ (P : AssociatedCharacterLineBundle.Presentation G B i Q q χ.toMul)
              (hP : Scheme.Modules.IsInvertible P.L),
              (c χ).toMul = @Scheme.Pic.ofIsInvertible Q.left P.L hP) ∧
          Function.Injective (fun χ : Additive (G ⟶
            Grp.mk (StandardGroupSchemes.multiplicative F)) ↦
              Additive.ofMul (i ≫ χ.toMul)) ∧
          Function.Exact (fun χ : Additive (G ⟶
            Grp.mk (StandardGroupSchemes.multiplicative F)) ↦
              Additive.ofMul (i ≫ χ.toMul)) c ∧
          Function.Exact c (Scheme.Pic.mapHom q.left).toAdditive ∧
          Function.Surjective (Scheme.Pic.mapHom q.left).toAdditive := by
  sorry

end AlgebraicGeometry
