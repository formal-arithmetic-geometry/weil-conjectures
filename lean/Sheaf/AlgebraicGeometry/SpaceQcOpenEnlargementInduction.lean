/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests
import Sheaf.AlgebraicGeometry.SpaceChangeBase
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus

/-! # Enlarging a fixed quasi-compact open of an algebraic space

Source: Stacks Project, Derived Categories of Spaces, Tag 09IT
(blueprint: lem-sfb-space-qc-open-enlargement-induction).

Open subspaces are the existing subfunctors. The property is evaluated only on their
quasi-compact members; its isomorphism invariance concerns isomorphisms of open
subspaces of X, i.e. those over X. A presentation `e` identifies the upper open with an algebraic
space `Y`, so its reduced complement uses the existing `ClosedSubspace Y`. The overlap
is the actual presheaf pullback, represented by a quasi-compact open subscheme of `V`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A property propagating from a fixed quasi-compact open by affine elementary
 distinguished squares holds on the whole space. Every overlap in such a square is
 a quasi-compact open subscheme of the affine chart.

Source: Stacks Project, Tags 09IT and 08GP
(blueprint: lem-sfb-space-qc-open-enlargement-induction).

Proof:
1. For any square, lem-sfb-space-qcqs-permanence makes the quasi-compact lower open's
inclusion in X quasi-compact, since X is absolutely quasi-separated. Base change and
scheme tests (lem-sfb-space-quasicompact-affine-tests) make its pullback to V a
quasi-compact scheme. The upper open is monic in X, so this is the stated overlap.
The defining scheme tests of def-a1-space-open-subspace make its projection open.
2. Use lem-sfb-space-change-base-to-integers to view X over Spec Z, retaining atlases,
fibre products, open subspaces, reduced complements, point topology and absolute qcqs.
Apply lem-sfb-qcqs-space-splitting-filtration and transport back. We obtain finitely
many quasi-compact opens from empty to X and surjective etale quasi-compact separated
scheme charts that are isomorphisms over the successive reduced complements.
3. Form A_p = W0 union U_p. Finite unions of quasi-compact opens are quasi-compact,
by combining finite subcovers. Descend on p, starting at A_(n+1) = W0. Cover V_p by
finitely many affine opens (lem-weil-pbc-qcqs-finite-affine-open-cover) and successively
adjoin their images to A_(p+1). By lem-a1-space-etale-open-image these are quasi-compact
opens B_i, containing W0, ending at A_p by surjectivity.
4. Each affine chart factors etale through B_i, by lem-a1-space-etale-open-image and
lem-trf-space-representable-etale-scheme-tests. The reduced closed complement C_i of
B_(i-1) in B_i exists by lem-sfb-space-reduced-closed-support. Its support lies in
U_p minus U_(p+1), so it factors through U_p and its reduced closed complement Z_p.
On etale affine charts the ideal of Z_p is radical; its image in the reduced chart of
C_i lies in every prime, hence is zero. Uniqueness through a closed immersion glues
these factorizations.
5. Pulling back the filtration isomorphism over Z_p identifies V_p times C_i with C_i.
Every point newly in B_i lies in the ith affine image. The fibre-product image and
full-image open clauses of lem-a1-space-point-open-calculus identify the restriction
of the ith affine chart over C_i with all of C_i. Hence these are distinguished squares.
6. Apply h_step successively to the B_i, proving P(A_p) from P(A_(p+1)). An empty
finite cover has empty target by surjectivity, so no square step is needed. Descending
induction ends at A_1 = X. Step 1 proves the additional overlap conclusion
independently of P, including empty opens and W0 = X. The invariance h_iso is over X:
an isomorphism of open subspaces commutes with the inclusions, so it is never used.
-/
theorem qc_open_enlargement_induction {S : Scheme.{u}}
    (X : AlgebraicSpace S) (hXqc : CompactSpace (Point X.obj.obj))
    (hXqs : IsAbsolutelyQuasiSeparated X)
    (W₀ : OpenSubspace X) (hW₀ : CompactSpace (Point W₀.val.toFunctor))
    (P : Subfunctor X.obj.obj → Prop)
    (h_iso : ∀ (A B : OpenSubspace X),
      CompactSpace (Point A.val.toFunctor) → CompactSpace (Point B.val.toFunctor) →
      ∀ e : A.val.toFunctor ≅ B.val.toFunctor, e.hom ≫ B.val.ι = A.val.ι →
      (P A.val ↔ P B.val))
    (h_start : P W₀.val)
    (h_step : ∀ (W₁ W₂ : OpenSubspace X),
      CompactSpace (Point W₁.val.toFunctor) → CompactSpace (Point W₂.val.toFunctor) →
      W₀ ≤ W₁ → ∀ (h₁₂ : W₁ ≤ W₂) (Y : AlgebraicSpace S)
      (e : Y.obj.obj ≅ W₂.val.toFunctor) (V : Over S), IsAffine V.left →
      ∀ f : yoneda.obj V ⟶ Y.obj.obj, IsEtale f →
      ∀ C : ClosedSubspace Y, IsReduced (C.val : AlgebraicSpace S) →
      pointImage C.val.arrow.hom.hom =
        (pointImage (Subfunctor.homOfLe h₁₂ ≫ e.inv))ᶜ →
      IsIso (Limits.pullback.snd f C.val.arrow.hom.hom) → P W₁.val → P W₂.val) :
    P ⊤ ∧
      ∀ (W₁ W₂ : OpenSubspace X),
        CompactSpace (Point W₁.val.toFunctor) → CompactSpace (Point W₂.val.toFunctor) →
        W₀ ≤ W₁ → ∀ (h₁₂ : W₁ ≤ W₂) (Y : AlgebraicSpace S)
        (e : Y.obj.obj ≅ W₂.val.toFunctor) (V : Over S), IsAffine V.left →
        ∀ f : yoneda.obj V ⟶ Y.obj.obj, IsEtale f →
        ∀ C : ClosedSubspace Y, IsReduced (C.val : AlgebraicSpace S) →
        pointImage C.val.arrow.hom.hom =
          (pointImage (Subfunctor.homOfLe h₁₂ ≫ e.inv))ᶜ →
        IsIso (Limits.pullback.snd f C.val.arrow.hom.hom) →
        ∃ (H : Over S) (i : H ⟶ V)
          (a : yoneda.obj H ⟶ W₁.val.toFunctor),
          IsPullback a (yoneda.map i) (Subfunctor.homOfLe h₁₂ ≫ e.inv) f ∧
          IsOpenImmersion i.left ∧ CompactSpace H.left := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
