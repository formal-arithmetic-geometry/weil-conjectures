/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R7
-/
module

public import Sheaf.SixFunctors.ProEtale.IntegralPresentationEncoding
public import Sheaf.Paper.FiniteDiscreteOrdinaryEncoding

/-! # Normalized integral restriction squares -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralPresentation
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- The integral-limit comparison admits identity-on-sections finite restriction squares.
Source: blueprint integral-criterion-reductions, coefficient comparison; Stacks 06YY;
Bhatt--Scholze, the integral-limit coefficient identification
(blueprint: lem-pe-integral-normalized-restriction-squares).

Proof: reconstruct commutative section rings from the monoidal integral-limit comparison.
Its nth projection is the pulled-back quotient map. Use the normalized finite-discrete
encodings of each positive quotient. Section reconstruction followed by scalar transport
along the inverse integral comparison is an additive equivalence. On a finite-level module,
the two restricted scalar actions agree because the integral comparison followed by its nth
projection is the original quotient. The identity of its underlying abelian sheaf is therefore
linear in both directions and gives the square. Its naturality is the identity on every
module morphism. The displayed equation accounts for the recorded equalities of the concrete
section-action functors; no derived functor or completeness hypothesis is used. -/
theorem integral_completion_normalized_squares :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    ∃ (A : Encoding l E X) (e : ∀ n : ℕ,
      FiniteDiscreteOrdinary.Encoding (Padic.coefficientExtensionRing l E (n + 1)) X)
      (a : ∀ n : ℕ,
      Mod.comap (AdicCompletion.quotient l E X n) ⋙ A.modules.functor ≅
        (e n).ordinary.functor ⋙ scalarReductionRestriction.{u, u} l E X n),
      ∀ (n : ℕ) (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (AdicCompletion.finiteRing l E X n)),
      (SheafOfModules.toSheaf (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)).map
          ((a n).hom.app M) =
        (SheafOfModules.toSheaf
          (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)).map
            (eqToIso (congrArg (fun F ↦ F.obj
              ((Mod.comap (AdicCompletion.quotient l E X n)).obj M)) A.functor_eq)).hom ≫
          (SheafOfModules.toSheaf (integralCoefficientSheaf.{u, u} l E X n)).map
            (eqToIso (congrArg (fun F ↦ F.obj M) (e n).ordinary_functor)).inv := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralPresentation
