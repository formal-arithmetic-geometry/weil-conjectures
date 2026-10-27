module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.GroupScheme.Borel
public import Sheaf.AlgebraicGeometry.GroupScheme.SplitUnipotentSeries
public import Sheaf.AlgebraicGeometry.GroupScheme.AssociatedCharacterLineBundle
public import Sheaf.AlgebraicGeometry.TrivialTorusCoherentData
public import WeilConjectures.AlgebraicGeometry.Picard.Group
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.MultiplicativeCharacterData
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

import Sheaf.AlgebraicGeometry.SplitSolvableTorsorsAndVariety
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.Descent

/-! # The characteristic Picard sequence over an arbitrary splitting field

Source: Milne, Algebraic Groups (2017), Theorem 18.15, sequence (128), p.390,
and Section 18.f, pp.395--396; Brion, Lemma 2.3, equation (2), p.118.
(blueprint: lem-sfb-split-reductive-characteristic-sequence)

The auxiliary predicates only package the pair, quotient and canonical arrows in this
statement. Borels are tested over the algebraic closure. Character extension is pinned
by equality of regular Laurent coordinates, including on nonreduced test schemes.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.SplitReductiveCharacteristic

/-- A geometric Borel containing the specified torus, with its specified projection.
The kernel and multiplication isomorphism express B = U ⋊ T; the series is additive.
Source: Milne, Definition 17.66, p.375, and Section 18.c, p.390.
(blueprint: lem-sfb-split-reductive-characteristic-sequence) -/
def Pair {F : Type u} [Field F] {H T B : Grp (Over (Spec (.of F)))}
    (iT : T ⟶ H) (iB : B ⟶ H) (j : T ⟶ B) (r : B ⟶ T) : Prop :=
  IsClosedSubgroupScheme iB.hom.hom ∧ Smooth B.X.hom ∧
    IsBorelGroupScheme
      ((MultiplicativeType.baseChange (K := AlgebraicClosure F)).map iB).hom.hom ∧
    j ≫ iB = iT ∧ j ≫ r = 𝟙 T ∧
    ∃ (U : Grp (Over (Spec (.of F)))) (iU : U ⟶ B),
      IsClosedSubgroupScheme iU.hom.hom ∧ IsNormalSubgroupScheme iU.hom.hom ∧
      SolvableGroupStructure.IsUnipotent U ∧ (∃ n : ℕ, SplitUnipotentLength U n) ∧
      IsPullback iU.hom.hom (toUnit U.X) r.hom.hom η[T.X] ∧
      IsIso ((fst U.X T.X ≫ iU.hom.hom) * (snd U.X T.X ≫ j.hom.hom))

/-- Smooth projective geometrically integral quotient, with its actual right B-torsor.
An fppf epimorphism with this kernel pair represents sheafification of H(A)/B(A).
Source: Milne, Theorem 18.15 and Section 18.f.
(blueprint: lem-sfb-split-reductive-characteristic-sequence) -/
def QuotientGeometry {F : Type u} [Field F]
    {H B : Grp (Over (Spec (.of F)))} (iB : B ⟶ H)
    (Q : Over (Spec (.of F))) (f : H.X ⟶ Q) : Prop :=
  Smooth Q.hom ∧ IsProjective Q.hom ∧ GeometricallyIntegral Q.hom ∧
    Flat f.left ∧ Surjective f.left ∧ LocallyOfFinitePresentation f.left ∧
    IsPullback (fst H.X B.X)
      (fst H.X B.X * (snd H.X B.X ≫ iB.hom.hom)) f f

/-- The characteristic homomorphism is fixed by the associated line bundle, with
right action (h,z)b = (hb,χ(r(b))⁻¹z). Exactness is at Pic(Q), followed by surjectivity.
Source: Milne, Section 18.c and sequence (128), p.390.
(blueprint: lem-sfb-split-reductive-characteristic-sequence) -/
def Sequence {F : Type u} [Field F]
    {H T B : Grp (Over (Spec (.of F)))} (iB : B ⟶ H) (r : B ⟶ T)
    (Q : Over (Spec (.of F))) (f : H.X ⟶ Q)
    (c : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)) →+
      Additive Q.left.Pic) : Prop :=
  (∀ χ, ∃ P : AssociatedCharacterLineBundle.Presentation H B iB Q f (r ≫ χ.toMul),
    Nonempty (P.L ≅ (fromSkeleton Q.left.Modules).obj (c χ).toMul.val)) ∧
    Function.Exact c (Scheme.Pic.mapHom f.left).toAdditive ∧
    Function.Surjective (Scheme.Pic.mapHom f.left).toAdditive

/-- The exact characteristic sequence, and both scalar-extension squares, for every
split maximal torus over every field. No perfectness or algebraic closedness is assumed.

Source: Milne, Theorem 18.15, (128), p.390, Section 18.f, pp.395--396;
Brion, Lemma 2.3, (2), p.118.
(blueprint: lem-sfb-split-reductive-characteristic-sequence)

Proof (the ten DAG steps):
1. Extend T to the algebraic closure using lem-sfb-maximal-torus-field-extension.
Decompose the adjoint representation into Laurent monomial weight spaces. Avoid the
finitely many integer root hyperplanes to choose a regular integral cocharacter;
in rank zero choose zero. Apply lem-sfb-regular-cocharacter-borel-description.
2. lem-sfb-reductive-cocharacter-parabolic-geometry gives B = U ⋊ T, with U split,
and proves the Borel descends over F. No perfection hypothesis enters.
3. Every Borel containing T is such a cocharacter parabolic: descend equality of
its ideals faithfully flatly. lem-sfb-unipotent-to-multiplicative-trivial fixes r.
The parabolic geometry gives the smooth projective geometrically integral quotient.
lem-sfb-split-solvable-torsors-and-variety gives Zariski local sections and Pic(B_K)=0;
lem-weil-pbc-smooth-scheme-over-field-regular makes H and Q regular.
4. Descend the trivial line with multiplier χ(r(b))⁻¹ using lem-pc-fpqc-descent.
Multiplication of transition factors gives additivity; the zero character gives O_Q.
The global frame [h,1] trivializes its pullback, proving image contained in kernel.
5. Apply lem-sfb-rosenlicht-product-unit-factorization over the algebraic closure
at (1,1); descend its normalized identity by injectivity of faithfully flat tensor
extension. It holds on all test algebras, not only rational points.
6. By lem-sfb-unipotent-to-multiplicative-trivial every character of B kills U,
so restriction and composition with r identify its characters with those of T.
7. A frame of f^*M satisfies s(hb)=s(h)a(h,b). Step 5 makes a independent of h;
the cocycle makes it a character. Step 6 identifies it with χr. Then s(h)z is
invariant for the stated inverse-character action, and full faithful fpqc descent
gives M ≅ L_χ. This proves kernel contained in image with the specified sign.
8. At the generic point of Q, a local section identifies the fibre with B_K.
Its Picard group vanishes by step 3. Apply lem-sfb-smooth-generic-trivial-line-descent
to descend every invertible module on H, proving Picard pullback surjective.
9. Scalar extension preserves the cocharacter parabolic, its torus, additive series,
projection and torsor. Maximal-torus extension and regular-cocharacter description
verify the extended pair and quotient, so steps 4--8 give its exact sequence.
10. Choose local sections σ_i; write σ_j=σ_i b_ij. The transition factors are
χ(r(b_ij)). Their scalar extensions are precisely those for the extended character,
so fpqc descent proves p_Q^*c_F(χ)=c_L(χ_L). Tensor associativity, or the canonical
pullback composition comparison, proves p_H^*f^*M=f_L^*p_Q^*M. Laurent coordinate
pullback specifies the actual character-extension homomorphism uniquely.
-/
theorem split_reductive_characteristic_sequence {F : Type u} [Field F]
    (H T : Grp (Over (Spec (.of F)))) (iT : T ⟶ H)
    (hH : ReductiveTorusCentralizer.IsReductive H)
    (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (hsplit : ∃ n : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F n)) :
    (∃ (B : Grp (Over (Spec (.of F)))) (iB : B ⟶ H) (j : T ⟶ B) (r : B ⟶ T),
      Pair iT iB j r) ∧
    ∀ (B : Grp (Over (Spec (.of F)))) (iB : B ⟶ H) (j : T ⟶ B) (r : B ⟶ T),
      Pair iT iB j r → ∃ (Q : Over (Spec (.of F))) (f : H.X ⟶ Q),
        QuotientGeometry iB Q f ∧
        ∃ c : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)) →+
            Additive Q.left.Pic,
          Sequence iB r Q f c ∧
          ∀ (L : Type u) [Field L] [Algebra F L],
            ReductiveTorusCentralizer.IsReductive
              ((MultiplicativeType.baseChange (K := L)).obj H) ∧
            Pair ((MultiplicativeType.baseChange (K := L)).map iT)
              ((MultiplicativeType.baseChange (K := L)).map iB)
              ((MultiplicativeType.baseChange (K := L)).map j)
              ((MultiplicativeType.baseChange (K := L)).map r) ∧
            ReductiveTorusCentralizer.IsMaximalTorus
              ((MultiplicativeType.baseChange (K := L)).map iT) ∧
            (∃ n : ℕ, Nonempty ((MultiplicativeType.baseChange (K := L)).obj T ≅
              MultiplicativeType.splitTorus L n)) ∧
            QuotientGeometry ((MultiplicativeType.baseChange (K := L)).map iB)
              ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).obj Q)
              ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).map f) ∧
            ∃ (cL : Additive (((MultiplicativeType.baseChange (K := L)).obj T) ⟶
                Grp.mk (StandardGroupSchemes.multiplicative L)) →+
                Additive (((Over.pullback
                  (Spec.map (CommRingCat.ofHom (algebraMap F L)))).obj Q).left.Pic))
              (ext : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)) →+
                Additive (((MultiplicativeType.baseChange (K := L)).obj T) ⟶
                  Grp.mk (StandardGroupSchemes.multiplicative L))),
              Sequence ((MultiplicativeType.baseChange (K := L)).map iB)
                ((MultiplicativeType.baseChange (K := L)).map r)
                ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).obj Q)
                ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).map f) cL ∧
              (∀ χ, TrivialTorusCoherent.characterValue _ (ext χ) _ (𝟙 _) =
                (MultiplicativeType.scalarProjection T).appTop
                  (TrivialTorusCoherent.characterValue T χ T.X (𝟙 _))) ∧
              (∀ χ, cL (ext χ) =
                (Scheme.Pic.mapHom (pullback.fst Q.hom
                  (Spec.map (CommRingCat.ofHom (algebraMap F L))))).toAdditive (c χ)) ∧
              (∀ M : Additive Q.left.Pic,
                (Scheme.Pic.mapHom (MultiplicativeType.scalarProjection H)).toAdditive
                    ((Scheme.Pic.mapHom f.left).toAdditive M) =
                  (Scheme.Pic.mapHom ((Over.pullback
                    (Spec.map (CommRingCat.ofHom (algebraMap F L)))).map f).left).toAdditive
                    ((Scheme.Pic.mapHom (pullback.fst Q.hom
                      (Spec.map (CommRingCat.ofHom (algebraMap F L))))).toAdditive M)) := by
  sorry

end AlgebraicGeometry.SplitReductiveCharacteristic
