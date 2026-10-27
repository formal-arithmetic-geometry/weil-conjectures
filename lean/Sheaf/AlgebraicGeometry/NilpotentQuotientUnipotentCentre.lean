module

public import Sheaf.AlgebraicGeometry.UnitriangularUnipotentGroupScheme
public import Sheaf.AlgebraicGeometry.AffineGroupCentreBaseChange
public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
import Sheaf.AlgebraicGeometry.GroupScheme.AffineHomomorphismFlatImage
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Unipotent centre after removing the central multiplicative part

Source: Milne, Algebraic Groups (2017), Lemma 16.45, p.340, Proposition 5.59,
p.114, and Section 6(f), p.133
(blueprint: lem-sfb-nilpotent-quotient-unipotent-centre).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- Quotienting a connected nilpotent affine algebraic group by the largest
multiplicative-type subgroup of its centre leaves a connected nilpotent group
with unipotent scheme-theoretic centre. No smoothness or perfectness is assumed.
Centrality uses the universal centre functor, including after algebra extensions.

Source: Milne, Lemmas 16.43 and 16.45, p.340, Theorem 16.13(a), p.328,
Proposition 5.59(b), p.114, and Section 6(f), p.133
(blueprint: lem-sfb-nilpotent-quotient-unipotent-centre).

Proof plan:
1. By lem-sfb-affine-normal-quotient-geometry the quotient map is faithfully flat,
   finitely presented and surjective. Pull back a clopen partition of H to G.
   Connectedness and surjectivity imply that one part is empty; H has its identity point.
2. Choose the given central series of G. Factor its terms into H by
   lem-sfb-affine-homomorphism-flat-image to obtain closed images H_i. Lift points
   of H and H_i after faithfully flat algebra extensions. Their conjugates and
   commutators lift to those in G and G_i, hence belong to H_i and H_(i+1).
   Descend membership by injectivity of faithfully flat algebra maps, using
   lem-weil-pbc-faithfully-flat-base-change and
   lem-weil-pbc-faithfully-flat-universally-injective. The same ideal test gives
   nesting and endpoints, so these images form a central normal series of H.
3. Take C = Z(H) by lem-sfb-affine-group-centre-base-change. By
   lem-sfb-commutative-multiplicative-part its largest multiplicative subgroup S
   has unipotent quotient C/S. Pull S back to P in G. Quotient geometry gives
   a closed normal P containing D, with represented quotient P/D isomorphic to S.
4. Apply lem-sfb-normal-multiplicative-layers-central to D inside P inside G.
   The connected ambient group and the multiplicative types of D and P/D show
   that P is central and of multiplicative type. Maximality of D forces P = D,
   hence S = 1.
5. The unipotent quotient C/S is now C itself: on every algebra the cosets by
   the trivial subgroup are the original points, whose represented functor is
   already a sheaf. Transport its closed unitriangular immersion to C. -/
theorem nilpotent_quotient_unipotent_centre {k : Type u} [Field k]
    (G D H : Grp (Over (Spec (.of k)))) (iD : D ⟶ G) (q : G ⟶ H)
    (hG : SolvableGroupStructure.IsAlgebraic G)
    (hD : SolvableGroupStructure.IsAlgebraic D)
    (hH : SolvableGroupStructure.IsAlgebraic H)
    (hiD : IsClosedSubgroupScheme iD.hom.hom)
    (hconn : ConnectedSpace G.X.left)
    (hnil : ∃ (s : ℕ) (N : Fin (s + 1) → Grp (Over (Spec (.of k))))
        (i : ∀ j : Fin (s + 1), N j ⟶ G),
        (∀ j : Fin (s + 1), IsClosedSubgroupScheme (i j).hom.hom ∧
          IsNormalSubgroupScheme (i j).hom.hom) ∧
        IsIso (i 0) ∧ Nonempty (N (Fin.last s) ≅ Grp.trivial _) ∧
        (∀ j : Fin s, ∃ l : N j.succ ⟶ N j.castSucc, l ≫ i j.castSucc = i j.succ) ∧
        ∀ (j : Fin s) (A : Type u) [CommRing A] [Algebra k A]
          (g : StandardGroupSchemes.affine k A ⟶ G.X)
          (c : StandardGroupSchemes.affine k A ⟶ (N j.castSucc).X),
          ∃ z : StandardGroupSchemes.affine k A ⟶ (N j.succ).X,
            z ≫ (i j.succ).hom.hom =
              g * (c ≫ (i j.castSucc).hom.hom) * g⁻¹ * (c ≫ (i j.castSucc).hom.hom)⁻¹)
    (hcentral : ∀ (A : Type u) [CommRing A] [Algebra k A]
      (d : StandardGroupSchemes.affine k A ⟶ D.X),
      d ≫ iD.hom.hom ∈ ReductiveTorusCentralizer.centralizerPoints (𝟙 G) A)
    (hmult : MultiplicativeType.IsMultiplicativeType D)
    (hmax : ∀ (S : Grp (Over (Spec (.of k)))) (j : S ⟶ G),
      IsClosedSubgroupScheme j.hom.hom → MultiplicativeType.IsMultiplicativeType S →
      (∀ (A : Type u) [CommRing A] [Algebra k A]
        (s : StandardGroupSchemes.affine k A ⟶ S.X),
        s ≫ j.hom.hom ∈ ReductiveTorusCentralizer.centralizerPoints (𝟙 G) A) →
      ∃ f : S ⟶ D, f ≫ iD = j)
    (hq : SolvableGroupStructure.IsFppfQuotient iD.hom.hom q) :
    ConnectedSpace H.X.left ∧
      (∃ (s : ℕ) (N : Fin (s + 1) → Grp (Over (Spec (.of k))))
          (i : ∀ j : Fin (s + 1), N j ⟶ H),
          (∀ j : Fin (s + 1), IsClosedSubgroupScheme (i j).hom.hom ∧
            IsNormalSubgroupScheme (i j).hom.hom) ∧
          IsIso (i 0) ∧ Nonempty (N (Fin.last s) ≅ Grp.trivial _) ∧
          (∀ j : Fin s, ∃ l : N j.succ ⟶ N j.castSucc, l ≫ i j.castSucc = i j.succ) ∧
          ∀ (j : Fin s) (A : Type u) [CommRing A] [Algebra k A]
            (g : StandardGroupSchemes.affine k A ⟶ H.X)
            (c : StandardGroupSchemes.affine k A ⟶ (N j.castSucc).X),
            ∃ z : StandardGroupSchemes.affine k A ⟶ (N j.succ).X,
              z ≫ (i j.succ).hom.hom =
                g * (c ≫ (i j.castSucc).hom.hom) * g⁻¹ * (c ≫ (i j.castSucc).hom.hom)⁻¹) ∧
      ∃ (C : Grp (Over (Spec (.of k)))) (iC : C ⟶ H),
        SolvableGroupStructure.IsAlgebraic C ∧ IsClosedSubgroupScheme iC.hom.hom ∧
        IsNormalSubgroupScheme iC.hom.hom ∧ IsCommMonObj C.X ∧
        (∀ (A : Type u) [CommRing A] [Algebra k A],
          ReductiveTorusCentralizer.centralizerPoints (𝟙 H) A =
            Set.range (fun c : StandardGroupSchemes.affine k A ⟶ C.X ↦ c ≫ iC.hom.hom)) ∧
        IsUnitriangularUnipotentGroupScheme C := by
  sorry

end AlgebraicGeometry
