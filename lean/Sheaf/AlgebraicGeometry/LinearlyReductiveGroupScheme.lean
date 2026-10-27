module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Order.SupIndep

/-! # Linear reductivity of group schemes in arbitrary characteristic

Source: Milne, Algebraic Groups (2017), Definition 12.52, printed p.248, and
Corollary 13.8, printed p.257 (blueprint: def-sfb-linearly-reductive-group-scheme).

Finite-dimensional representations are written in a basis. Invariance is tested on
all algebra-valued points, including points valued in nonreduced algebras. The direct
sum consists of nonzero invariant subspaces minimal among invariant subspaces.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Scheme-theoretic invariance of a subspace in a rational representation. After
extension to any algebra A, its span is preserved by every A-valued point. This is
invariance of U tensor A under the given group scheme, since a basis identifies
k^ι tensor A with A^ι. Source: Milne, Algebraic Groups (2017), Definition 12.52 and
Corollary 13.8 (blueprint: def-sfb-linearly-reductive-group-scheme). -/
def IsInvariantRationalSubspace {k : Type u} [Field k]
    {G : Over (Spec (.of k))} [GrpObj G]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (ρ : GeneralLinearGroup.RationalHom G ι) [IsMonHom ρ]
    (U : Submodule k (ι → k)) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra k A] (g : points G A),
    ∀ v ∈ Submodule.span A ((fun w : ι → k ↦ fun i ↦ algebraMap k A (w i)) '' (U : Set _)),
      Matrix.toLin' (ρ.points A g : Matrix ι ι A) v ∈
        Submodule.span A ((fun w : ι → k ↦ fun i ↦ algebraMap k A (w i)) '' (U : Set _))

/-- A group scheme is linearly reductive when every finite-dimensional rational
representation is an internal direct sum of simple subrepresentations. Each summand
is nonzero and has no nonzero proper invariant subspace. Independence and the supremum
condition express the direct sum, and the empty family covers the zero representation.
No characteristic, smoothness or connectedness condition is imposed.
Source: Milne, Algebraic Groups (2017), Definition 12.52, printed p.248
(blueprint: def-sfb-linearly-reductive-group-scheme). -/
def IsLinearlyReductiveGroupScheme {k : Type u} [Field k]
    (G : Over (Spec (.of k))) [GrpObj G] : Prop :=
  ∀ (ι : Type u) [Fintype ι] [DecidableEq ι]
    (ρ : GeneralLinearGroup.RationalHom G ι) [IsMonHom ρ],
    ∃ S : Set (Submodule k (ι → k)),
      (∀ U ∈ S, IsInvariantRationalSubspace ρ U ∧ U ≠ ⊥ ∧
        ∀ W : Submodule k (ι → k), W ≤ U → IsInvariantRationalSubspace ρ W →
          W = ⊥ ∨ W = U) ∧
      iSupIndep (fun U : S ↦ U.1) ∧ (⨆ U : S, U.1) = ⊤

end AlgebraicGeometry
