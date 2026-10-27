module
public import Sheaf.SixFunctors.CoefIntegralFiniteExtensionCore
import Sheaf.Paper.IntegralConstructibleReductionHom
/-! Reconstruction of an isomorphism from compatible finite reductions.
Source: current blueprint, lem-coef-integral-finite-extension.proof.md, paragraphs 2-3
(blueprint: lem-sf-integral-finite-extension-u-invertibility).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
  (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
  (wE : DualizingDatum l X D hl E) (wL : DualizingDatum l X D hl L)
/-- A comparison whose reductions are all invertible is itself invertible.

Use `integralConstructibleReductionHom` on the inverse finite reductions. Its
successor compatibility follows from naturality of the reduction functor and
inversion of the transition square. The lifted inverse is a two-sided inverse
by the uniqueness clause of the same reconstruction theorem. This is the
Milnor/Roos effectivity step and is independent of the finite-level calculation.
(blueprint: lem-sf-integral-finite-extension-u-reconstruction)
-/
theorem comparison_invertibility_u_of_reductions
    (hred : ∀ n : ℕ,
      IsIso ((scalarReductionDerivedExtension l L X n).map
        (u l E L ι X D hl wE wL))) :
    IsIso (u l E L ι X D hl wE wL) := by
  sorry
end WeilConjectures.IntegralFiniteExtension
