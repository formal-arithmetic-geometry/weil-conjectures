/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A6
-/
module

public import Sheaf.Paper.AdicLisseCalculusData

/-! # Lisse linear duals and the completed derived internal dual

Source: Bhatt--Scholze 6.8.4 and Remark 6.8.15.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Qbar : Type (u + 1)) [Field Qbar]
  [Algebra ℚ_[l] Qbar] [IsAlgClosure ℚ_[l] Qbar] (X : Scheme.{u})
  [IsNoetherian X] [X.IsSeparated]
  [hDim : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [hInv : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]


/-- The contravariant lisse dual, with fibre evaluation and derived-dual
normalizations. This statement does not assert any cohomology/tensor comparison.
Source: Bhatt--Scholze, Proposition 6.8.4(1),(4), Remark 6.8.15; the linear-dual
calculation in the blueprint lisse tensor permanence argument.
(blueprint: lem-per-adic-lisse-linear-dual-comparisons).

Proof: choose a common finite coefficient field and, componentwise, a stable
finite-free integral lattice. At level n take the sheaf Hom of its finite-free
quotient L_n into the constant quotient coefficient sheaf. Finite-free duality
commutes with reduction: a change of basis acts on the dual by inverse transpose,
and reduction preserves this formula. Thus the duals form a normalized lisse
system. Morphisms act by precomposition. Dualization reverses scalar-extension
comparisons; evaluation fixes their unit and composition equations. Consequently
these systems and maps rationalize and descend to a contravariant functor on the
adic lisse category, independently of the chosen lattice.

At a geometric point take finite etale fibres and inverse limits. In a local
basis evaluation is the usual sum of coordinate products. The finite-module
adic limit theorem identifies the limit dual with the integral linear dual.
Inversion of the uniformizer and finite-free scalar extension identify its Qbar
fibre with the displayed vector-space dual. Precomposition with a map gives
exactly dual_fiber_naturality, first on integral maps and then on the generators
of the coefficient localizations.

The completed realization of the dual system is Hom_B(N,B). Sheaf Hom from N is
exact: on a trivializing slice it is a finite direct sum of the identity, and
exactness descends by the sheaf axiom. Apply bounded exact-term Hom preservation
to N[0] and a K-injective resolution of B[0]. It identifies Hom_B(N,B)[0] with
the recorded derived internal Hom. Its local finite-free model puts it in the
integral constructible category. Thus the rational and common-stage Hom pair is
permitted. Rationalizing the evaluation-defined comparison and transporting
through models.comparison gives dual_realization. Precomposition on the complex Hom
model proves the displayed naturality equation. The scalar-operation comparisons
and their tower laws prove compatibility with every coefficient-change map.
Rank zero and empty components give the zero dual and require no exception. -/
theorem adic_lisse_linear_dual_comparisons (models : AdicLisseCalculusModels l Qbar X) :
    ∃ dual : (LisseAlgebraicSheaf l X Qbar)ᵒᵖ ⥤ LisseAlgebraicSheaf l X Qbar,
    ∃ dual_fiber : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ X)
    (L : LisseAlgebraicSheaf l X Qbar),
    (lisseAlgebraicFiberFunctor l X x Qbar).obj (dual.obj (op L)) ≅
      ModuleCat.of Qbar (Module.Dual Qbar ((lisseAlgebraicFiberFunctor l X x Qbar).obj L)),
    (∀ (k : Type u) [Field k] [IsAlgClosed k]
    (x : Spec (.of k) ⟶ X) (L M : LisseAlgebraicSheaf l X Qbar) (f : L ⟶ M),
    (lisseAlgebraicFiberFunctor l X x Qbar).map (dual.map f.op) ≫
        (dual_fiber k x L).hom =
      (dual_fiber k x M).hom ≫ ModuleCat.ofHom
        (LinearMap.dualMap ((lisseAlgebraicFiberFunctor l X x Qbar).map f).hom)) ∧
    ∃ dual_permitted : ∀ L : LisseAlgebraicSheaf l X Qbar,
    commonStageHomPairs l Qbar X
      (op (models.comparison.functor.obj (models.realization.obj L)),
        models.comparison.functor.obj (models.realization.obj (lisseAlgebraicUnit l X Qbar))),
    ∃ dual_realization : ∀ L : LisseAlgebraicSheaf l X Qbar,
    models.realization.obj (dual.obj (op L)) ≅ models.comparison.inverse.obj
      ((commonStageDerivedInternalHom l Qbar X).obj
        ⟨(op (models.comparison.functor.obj (models.realization.obj L)),
          models.comparison.functor.obj (models.realization.obj (lisseAlgebraicUnit l X Qbar))),
          dual_permitted L⟩),
    ∀ (L M : LisseAlgebraicSheaf l X Qbar) (f : L ⟶ M),
    models.realization.map (dual.map f.op) ≫ (dual_realization L).hom =
      (dual_realization M).hom ≫ models.comparison.inverse.map
        ((commonStageDerivedInternalHom l Qbar X).map
          (ObjectProperty.homMk
            ((models.comparison.functor.map (models.realization.map f)).op,
              𝟙 (models.comparison.functor.obj
                (models.realization.obj (lisseAlgebraicUnit l X Qbar)))))) := by sorry

end AlgebraicGeometry.Scheme
