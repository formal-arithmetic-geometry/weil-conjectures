module

public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.Lie

/-! # Semisimple points of group schemes

Source: Milne, Algebraic Groups (2017), Lemma 16.42, printed p.339, and the
representation convention preceding Theorem 12.12, printed pp.234--235
(blueprint: def-sfb-semisimple-group-scheme-point).

Semisimplicity is tested in every algebraic representation, including dimension zero.
Choosing a basis identifies a finite-dimensional representation with one on k^n;
diagonalizability is expressed by conjugation by an invertible matrix.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A rational point is semisimple if every finite-dimensional algebraic representation
sends it to a diagonalizable matrix. Testing representations on k^n for every n is equivalent
to testing all finite-dimensional vector spaces, by choosing a basis; n = 0 is included.
Source: Milne, Algebraic Groups (2017), Lemma 16.42, p.339 and Theorem 12.12, pp.234--235
(blueprint: def-sfb-semisimple-group-scheme-point). -/
def IsSemisimpleGroupSchemePoint {k : Type u} [Field k] [IsAlgClosed k]
    (G : Over (Spec (.of k))) [GrpObj G]
    (s : StandardGroupSchemes.affine k k ⟶ G) : Prop :=
  ∀ (ι : Type u) [Fintype ι] [DecidableEq ι]
    (ρ : GeneralLinearGroup.RationalHom G ι) [IsMonHom ρ],
    ∃ (P : GL ι k) (d : ι → k),
      (↑P⁻¹ : Matrix ι ι k) *
        (GeneralLinearGroup.homMulEquiv ι k k (s ≫ ρ) : Matrix ι ι k) *
          (↑P : Matrix ι ι k) = Matrix.diagonal d

end AlgebraicGeometry
