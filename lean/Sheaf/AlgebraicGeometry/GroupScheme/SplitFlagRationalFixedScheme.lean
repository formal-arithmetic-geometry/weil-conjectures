module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions
public import Sheaf.AlgebraicGeometry.GroupScheme.FieldBorel
public import Sheaf.AlgebraicGeometry.GroupScheme.SplitFlagFunctors
public import Mathlib.AlgebraicGeometry.Group.Affine
import Sheaf.AlgebraicGeometry.ReductiveTorusSelfCentralizer
import Sheaf.AlgebraicGeometry.SplitSolvableTorsorsAndVariety
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
import Sheaf.AlgebraicGeometry.FpqcClosedImmersionDescent

/-! # Rational torus-fixed flags of a split reductive group

Source: Milne, Algebraic Groups (2017), Proposition 21.1, p.424; Summary 21.41,
p.436; Section 21h, paragraph before Proposition 21.70, p.446
(blueprint: lem-sfb-split-flag-rational-fixed-scheme).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.SplitFlag

/-- Split Borel pairs remain split Borel pairs after every field extension. Their Weyl
quotient is finite constant, has rational normalizer representatives over every field,
and indexes the whole closed fixed subscheme of the flag quotient. The coproduct arrows
are the specified cosets, for every choice of rational representatives. The last clause
includes H = T and rank zero. `IsIso iT` expresses equality as subgroup schemes,
independently of the presentation of the torus embedding.

Source: Milne, Proposition 21.1, p.424; Summary 21.41, p.436; Section 21h, p.446
(blueprint: lem-sfb-split-flag-rational-fixed-scheme).

Proof plan, following all six steps of the node:
1. By lem-sfb-maximal-torus-field-extension, maximality is stable under field extension.
   The given torus splitting also base changes. Use
   lem-sfb-split-torus-solvable-cocharacter-containment to put B inside P_lambda for a
   regular cocharacter. By lem-sfb-reductive-cocharacter-parabolic-geometry its centralizer
   is T and P_lambda is split solvable, so B = P_lambda by maximality. Limit subgroups and
   tangent weights commute with field extension. By
   lem-sfb-regular-cocharacter-borel-description it stays Borel over an algebraic closure;
   faithful extension reflects equality of subgroup ideals. Its split series base changes.
2. Apply lem-sfb-relative-torus-centralizer-normalizer. The normalizer is the disjoint
   union of monomial-automorphism loci N_sigma; finite type makes the nonempty index set
   finite. Products and inverses multiply and invert the labels. By
   lem-sfb-reductive-torus-self-centralizer the identity locus is T. Each locus is a right
   T-torsor by (d,t) ↦ (d,dt), so the label map represents N/T as a finite constant group.
3. The loci and torsor identities commute with extension. By
   lem-sfb-split-solvable-torsors-and-variety each split-torus torsor over a field has a
   section. This proves surjectivity on every field and identifies W(F) with W(L).
4. Map the w-component to n_w B. Normalization and T ⊆ B make it universally T-fixed.
   Another lift differs by a T-point and gives the same coset. Restriction to L-algebras
   identifies the quotient and fixed functors with those of the extended pair.
5. Over an algebraic closure use lem-sfb-reductive-borel-pair-structure and
   lem-sfb-flag-torus-fixed-geometry: these components are the entire reduced fixed
   subscheme on all algebras. Descend the closed immersion using
   lem-pc-fpqc-descend-closed-immersion, and descend its unique factorizations using
   lem-weil-pbc-fpqc-representable-descent. This proves representation of the full functor.
6. Extend the same coset points to every L. The fixed-functor identity gives the displayed
   reduced coproduct of Spec L. If H = T, both quotients are T/T, hence trivial, and the
   fixed immersion is an isomorphism onto Q = Spec F.
-/
theorem split_flag_rational_fixed_scheme {F : Type u} [Field F]
    (H T B : Grp (Over (Spec (.of F))))
    (iT : T ⟶ H) (iB : B ⟶ H) (jB : T ⟶ B) (hTB : jB ≫ iB = iT)
    (hH : ReductiveTorusCentralizer.IsReductive H)
    (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (hTs : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (hB : IsFieldBorel iB) (hBs : IsSplitSolvable B)
    (Q : Over (Spec (.of F))) (π : H.X ⟶ Q) (hQ : IsCosetQuotient iB π) :
    (∀ (L : Type u) [Field L] [Algebra F L],
      ReductiveTorusCentralizer.IsMaximalTorus
        ((MultiplicativeType.baseChange (K := L)).map iT) ∧
      (∃ r : ℕ, Nonempty ((MultiplicativeType.baseChange (K := L)).obj T ≅
        MultiplicativeType.splitTorus L r)) ∧
      IsFieldBorel ((MultiplicativeType.baseChange (K := L)).map iB) ∧
      IsSplitSolvable ((MultiplicativeType.baseChange (K := L)).obj B)) ∧
    ∃ (N W : Grp (Over (Spec (.of F)))) (iN : N ⟶ H) (j : T ⟶ N) (p : N ⟶ W),
      Mono iN.hom.hom ∧ j ≫ iN = iT ∧
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (g : (algSpec (.of F)).obj (.op (CommAlgCat.of F A)) ⟶ H.X),
        Normalizes iT g ↔ ∃ n : (algSpec (.of F)).obj (.op (CommAlgCat.of F A)) ⟶ N.X,
          n ≫ iN.hom.hom = g) ∧
      SolvableGroupStructure.IsFppfQuotient j.hom.hom p ∧
      Finite (𝟙_ (Over (Spec (.of F))) ⟶ W.X) ∧
      IsIso (Sigma.desc (fun w : 𝟙_ (Over (Spec (.of F))) ⟶ W.X ↦ w)) ∧
      (∀ (L : Type u) [Field L] [Algebra F L],
        Function.Surjective (fun n : 𝟙_ (Over (Spec (.of L))) ⟶
            ((MultiplicativeType.baseChange (K := L)).obj N).X ↦
          n ≫ ((MultiplicativeType.baseChange (K := L)).map p).hom.hom) ∧
        Function.Bijective (fun w : 𝟙_ (Over (Spec (.of F))) ⟶ W.X ↦
          extendPoint (L := L) w)) ∧
      ∀ n : (𝟙_ (Over (Spec (.of F))) ⟶ W.X) →
          (𝟙_ (Over (Spec (.of F))) ⟶ N.X),
        (∀ w, n w ≫ p.hom.hom = w) →
        RepresentsFixed iT π (Sigma.desc (fun w ↦ n w ≫ iN.hom.hom ≫ π)) ∧
        (∀ (L : Type u) [Field L] [Algebra F L],
          RepresentsFixed ((MultiplicativeType.baseChange (K := L)).map iT)
            ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).map π)
            (Sigma.desc (fun w ↦ extendPoint (L := L) (n w ≫ iN.hom.hom ≫ π)))) ∧
        (IsIso iT → Nonempty (W ≅ Grp.trivial _) ∧
          Nonempty (Q ≅ 𝟙_ (Over (Spec (.of F)))) ∧
          IsIso (Sigma.desc (fun w ↦ n w ≫ iN.hom.hom ≫ π))) := by
  sorry

end AlgebraicGeometry.SplitFlag
