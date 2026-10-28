/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.NativeConstantSupportModel
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison

/-! # Pushout square for completed constant coefficient maps

The finite-free completion comparison identifies the completed coefficient square
with the sectionwise pushout of the constant coefficient map and the two
constant-to-completion maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- The completed coefficient square is a sectionwise pushout.

Source: Bhatt--Scholze, Lemma 6.8.2(1), together with the finite-free completed
scalar comparison.  At every pro-etale object, choose the integral E-basis of F
from the finite-free comparison.  Its compatible reductions identify the target
completed coefficient ring with the finite direct sum of copies of the source
completion indexed by that basis.  The resulting multiplication map is the
pushout of the constant map and the two constant-to-completion maps.  The
identification is compatible with restrictions because the coefficient maps are
constant and their residue normalizations determine the completion map uniquely;
therefore the sectionwise pushout condition follows from the universal property
of tensor product.  For an empty site object all four section rings are zero; for the identity
field extension the square is the identity square.  Both satisfy the same
universal property.
(blueprint: new-completed-constant-square-pushout).
-/
theorem completedConstantSquare_isPushout (W : Scheme.{u}) :
    ∀ U : W.ProEtᵒᵖ,
      IsPushout
        ((PurStrictScalar.constantMap l E F i W).hom.app U)
        (CommRingCat.ofHom (show
          ((PurStrictScalar.constants l E).ring W).obj.obj U →+*
            (completedIntegralCommRingSheafUnrestricted l E W).obj.obj U from
          ((integralConstantToCompletionOfUniverses l E W).hom.app U).hom))
        (CommRingCat.ofHom (show
          ((PurStrictScalar.constants l F).ring W).obj.obj U →+*
            (completedIntegralCommRingSheafUnrestricted l F W).obj.obj U from
          ((integralConstantToCompletionOfUniverses l F W).hom.app U).hom))
        ((completedCoefficientMap l E F i W).hom.app U) := by
  sorry

end WeilConjectures
