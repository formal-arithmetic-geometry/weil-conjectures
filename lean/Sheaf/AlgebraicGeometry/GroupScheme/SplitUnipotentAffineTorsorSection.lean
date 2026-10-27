module

public import Sheaf.AlgebraicGeometry.GroupScheme.SplitUnipotentSeries
public import Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
import Sheaf.AlgebraicGeometry.AdditiveAffineTorsorSection

/-! # Sections of split unipotent torsors over affine schemes

Source: Milne, Algebraic Groups (2017), Proposition 16.55(b), printed p.344;
Definition 6.33, Section 14.61 and Example 2.72, printed p.61.
(blueprint: lem-sfb-split-unipotent-affine-torsor-section)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A represented right torsor under a group with a finite split additive series has
an affine-base section. The series includes smoothness and connectedness of every term,
including U. The section is a morphism over k. Neither perfectness of k, reducedness of S,
nor commutativity or centrality of the series is assumed; length zero is included.

Source: Milne, Algebraic Groups (2017), Proposition 16.55(b), printed p.344;
Definition 6.33, Section 14.61 and Example 2.72, printed p.61.
(blueprint: lem-sfb-split-unipotent-affine-torsor-section)

Proof:
1. Induct on m. For m = 0 the series identifies U with the trivial group. The torsor
comparison is the diagonal, so the projection is a monomorphism. It is flat and locally
finitely presented. By lem-pe-flat-lfp-monomorphism-open it is an open immersion;
surjectivity makes it an isomorphism, whose inverse is the required section.
2. For m > 0 take N = U_1. By lem-sfb-affine-normal-quotient-geometry the quotient U/N
is affine and finite type, with faithfully flat finitely presented quotient map and
scheme-theoretic kernel N. The supplied series identifies this quotient with G_a.
By lem-sfb-normal-extension-torsor-reduction, P/N is represented by a right G_a-torsor
R over S. Pulling P back along any section a of R gives a represented N-torsor P_a
whose section composes to a section of P.
3. Write the affine base as Spec A and apply lem-sfb-additive-affine-torsor-section to R.
Its hypotheses are precisely the flat, surjective, finitely presented projection and
torsor comparison after identifying U/N with G_a. This gives a section a. The tail
series of N has length m - 1; its terms are smooth and connected and remain closed,
affine and finite type. The induction hypothesis gives a section b of P_a. The final
clause of lem-sfb-normal-extension-torsor-reduction composes b to a section of P. -/
theorem split_unipotent_affine_torsor_section {k : Type u} [Field k]
    (U : Grp (Over (Spec (.of k))))
    [IsAffine U.X.left] [LocallyOfFiniteType U.X.hom] [QuasiCompact U.X.hom]
    (m : ℕ) (hseries : SplitUnipotentLength U m)
    (S : Over (Spec (.of k)))
    [IsAffine S.left] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    (P : RepresentedRightTorsor U S) :
    ∃ s : S ⟶ P.space, s ≫ P.projection = 𝟙 S := by
  sorry

end AlgebraicGeometry
