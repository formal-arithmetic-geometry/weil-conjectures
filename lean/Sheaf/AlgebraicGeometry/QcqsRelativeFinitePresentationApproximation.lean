module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.AlgebraicGeometry.LimitFibreProducts

/-!
# Relative finite-presentation approximation of a qcqs morphism

Source: Stacks Project, Limits, Tag 09MV, `lemma-relative-approximation`,
the quasi-compact quasi-separated base case.
(blueprint: lem-trf-qcqs-relative-finite-presentation-approximation).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A morphism between qcqs schemes is a directed inverse limit of finitely presented
schemes over its target, with affine transitions and qcqs stages.

Source: Stacks Project, Limits, Tag 09MV, `lemma-relative-approximation`,
the qcqs-base special case.
(blueprint: lem-trf-qcqs-relative-finite-presentation-approximation).

Proof:
1. Apply lem-trf-qcqs-arrow-absolute-approximation to obtain arrows `Aᵢ ⟶ Bᵢ`
   of finite-type schemes over `Spec ℤ`, with affine transitions and limiting arrow
   `Z ⟶ S`. Write their projections as `uᵢ : Z ⟶ Aᵢ` and `vᵢ : S ⟶ Bᵢ`.
2. By lem-weil-pbc-finite-type-over-noetherian, `Spec ℤ` is Noetherian.
   Apply pqf-lem-lft-fp-locnoeth and lem-a1-map-over-base-finite-presentation to
   see that `Aᵢ ⟶ Bᵢ` is locally of finite presentation. Its qcqs source and target
   make it quasi-compact and quasi-separated by lem-weil-pbc-qcqs-morphism-permanence.
3. Set `Zᵢ = Aᵢ ×[Bᵢ] S` (def-pc-fibre-product). Its map to `S` is of finite
   presentation by base change; its source is qcqs by
   lem-weil-pbc-qcqs-morphism-permanence. The pairs consisting of the transitions
   on `Aᵢ` and the identity on `S` give transitions on `Zᵢ`. Projection identities
   prove their functor laws and compatibility over `S`. They are affine by
   lem-weil-pbc-limit-fibre-products, applied to the two systems and the constant `S`.
4. The constant system has limit `S` since the index set is nonempty and directed.
   By lem-weil-pbc-limit-fibre-products, the pullback system has limit `Z ×[S] S`.
   The first projection identifies this with `Z`, with inverse `(id, f)`.
   Thus the projections `(uᵢ, f)` give the asserted limiting cone in schemes;
   their second projections give `πᵢ ≫ qᵢ = f`. For any test scheme, the two
   projections of a compatible family give a unique map into that pullback,
   hence a unique map into `Z`. -/
theorem exists_qcqs_relative_finitePresentation_approximation
    {Z S : Scheme.{u}} [CompactSpace Z] [QuasiSeparatedSpace Z]
    [CompactSpace S] [QuasiSeparatedSpace S] (f : Z ⟶ S) :
    ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
      (D : Iᵒᵖ ⥤ Scheme.{u}) (q : D ⟶ (Functor.const Iᵒᵖ).obj S)
      (π : (Functor.const Iᵒᵖ).obj Z ⟶ D),
      (∀ i : Iᵒᵖ, LocallyOfFinitePresentation (q.app i) ∧
        QuasiCompact (q.app i) ∧ QuasiSeparated (q.app i)) ∧
      (∀ (i j : Iᵒᵖ) (h : i ⟶ j), IsAffineHom (D.map h)) ∧
      (∀ i : Iᵒᵖ, π.app i ≫ q.app i = f) ∧
      (∀ i : Iᵒᵖ, CompactSpace (D.obj i) ∧ QuasiSeparatedSpace (D.obj i)) ∧
      Nonempty (IsLimit (Cone.mk Z π)) := by
  sorry

end AlgebraicGeometry
