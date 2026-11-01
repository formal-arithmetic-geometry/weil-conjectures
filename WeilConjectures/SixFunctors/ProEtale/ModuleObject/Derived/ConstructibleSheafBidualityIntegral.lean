/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicIntegralModel
public import WeilConjectures.SixFunctors.Integral.IntegralVerdier

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
open scoped CategoryTheory.Obj
attribute [local instance] DerivedCategory.braidedCategory'
attribute [local irreducible] DerivedCategory.monoidalClosed
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]

/-- Integral Verdier evaluation is invertible for the native condensed integral model.

Source: Bhatt--Scholze, Lemmas 6.7.13 and 6.7.18--6.7.20; latest blueprint
`sk-thm-sf-ctf-stability/det-prop-sf-biduality-general.proof.md`.
Proof in words: normalize the integral dualizing complex by the structure map.
Its reductions are finite exceptional pullbacks of the coefficient unit.  Reduction
of internal Hom commutes with evaluation.  Applying this twice identifies each
reduction of the displayed arrow with finite-stage Verdier biduality.  The cone is
derived complete and all its reductions vanish, so derived Nakayama kills it.
For a nonclosed base field, check the finite assertion after algebraic closure;
the geometric pullback and internal-Hom comparison preserve evaluation and are
conservative.  This is integral biduality, before either rationalization or Qbar
extension, and includes zero and torsion lattices.
(blueprint: lem-pd-constructible-sheaf-biduality-integral) -/
theorem isIso_biduality_integral_constructible
    [IsIso S.hom] (a : X ⟶ S)
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (L : BoundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X.left)) :
    IsIso (toIhomIhom
      ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 a).obj (𝟙_ _)).obj
      L.obj) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Integral coefficient-stage Verdier biduality used by the constructible transport.

Source: `literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sf-ctf-stability/det-prop-sf-biduality-general.proof.md`, the
finite-stage-to-integral sentence.  The existing integral theorem supplies its
complete derived-complete conclusion; this interface exposes that conclusion
without assuming any condensed Qbar biduality statement.
(blueprint: lem-pd-constructible-sheaf-biduality-integral) -/
theorem integral_stage_biduality
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p) (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    (ω : WeilConjectures.sfIntegralConstructibleCategory l E X)
    (r : ∀ n : ℕ,
      (WeilConjectures.scalarReductionDerivedExtension l E X n).obj ω.obj ≅
        WeilConjectures.integralDualizingFiniteTerm l E D X n) :
    WeilConjectures.IntegralVerdier.Conclusion l E X D hl ω r := by
  exact WeilConjectures.integral_verdier_biduality D l hl E X ω r

end AlgebraicGeometry.ProEtale.CondensedRing
