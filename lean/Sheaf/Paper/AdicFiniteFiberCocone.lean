/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.Paper.CompletedCoefficientPresentationTransport
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.AdicHeartPullbackFibres

/-! # Scalar compatibility of normalized finite coefficient fibres

The finite-stage compatibility is separate from descent to the common-stage category.
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The completed geometric fibres at finite coefficient fields form a coherent cocone
when each fibre has the actual completed-section normalization.
Source: Bhatt--Scholze, Proposition 6.8.4(6), Proposition 6.8.14 and Remark 6.8.15
(blueprint: lem-intrinsic-adic-finite-fibre-cocone).
Proof: first compare the normalized integral coefficient model with the ordinary
completed module model. At the geometric point, evaluation of the constant-to-completion
map identifies scalar multiplication with the prescribed integer inclusion. For a
finite coefficient extension, the finite free integral scalar tensor therefore commutes
with completed pullback, H-zero, and point sections. On a K-flat representative these
comparisons send a pure tensor a tensor m to the tensor of a with its point section.
Their composition law follows on pure tensors from associativity of balanced tensor
products; naturality and additivity give the equality on all integral arrows. Inverting
the uniformizer extends both the comparisons and this equation to all rational arrows,
because the localization inverts precisely the uniformizer-power torsion cones.
Finally extend to the closure field. The actual coefficient embeddings compose, so
associativity of extension of scalars gives exactly the displayed cocycle, including
identity inclusions and zero objects. Uniqueness of normalized localization allows
any family G satisfying the given normalization to replace the constructed fibres.
This argument is on arbitrary schemes and does not use a finite-field datum. -/
theorem sfAdicFiniteFiberCocone
    (l : ℕ) [Fact l.Prime] (W : Scheme.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ W)
    (Qbar : Type v) [Field Qbar] [Algebra (Padic l) Qbar]
    [IsAlgClosure (Padic l) Qbar]
    (G : ∀ L : Padic.FiniteCoefficientFields l Qbar,
      sfRationalConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) W ⥤
          ModuleCat.{u + 1} (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L))
    (hG : ∀ L, sfRationalConstructibleLocalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) W ⋙ G L =
      (sfIntegralConstructible l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) W).ι ⋙
        (purCoefficientModel l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) W).inverse ⋙
        pbcActualCompletedPull x (pbcIntegralDatum l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L)) ⋙
        DerivedCategory.homologyFunctor _ 0 ⋙
        PerAdic.pointSections l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) Ω ⋙
        ModuleCat.extendScalars (PerAdic.integerToField l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L))) :
    let Φ := fun L : Padic.FiniteCoefficientFields l Qbar ↦ G L ⋙
      ModuleCat.extendScalars
        (L.val.subtype.comp (Shrink.algEquiv (Padic l) L.val).toRingHom)
    let S := GeneralAlgebraicallyClosedCoefficients.stageSystem l Qbar W
    ∃ β : ∀ {L M : Padic.FiniteCoefficientFields l Qbar} (h : L ≤ M),
        S.T h ⋙ Φ M ≅ Φ L,
      ∀ {L M N : Padic.FiniteCoefficientFields l Qbar} (h : L ≤ M) (k : M ≤ N)
        (K : GeneralAlgebraicallyClosedCoefficients.Stage l Qbar W L),
        (Φ N).map ((S.assoc h k).hom.app K) ≫ (β (h.trans k)).hom.app K =
          (β k).hom.app ((S.T h).obj K) ≫ (β h).hom.app K := by
  sorry

end WeilConjectures
