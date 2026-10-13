module

public import Sheaf.AlgebraicGeometry.FormalFunctionsFinitePullback
public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.QuotientBaseChangeIdeal
import Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
namespace AlgebraicGeometry

/-! The two residual finite-level identifications used by the main theorem. -/

/-- The canonical finite-level map is the base change of a quotient immersion.
Source: Stacks Project, Tag 02OD, finite fibre factorisation.
The finite fibre is obtained by pulling back the quotient
`Spec (A / m^(n+1)) → Spec A` along `X → Y`. The quotient map is
surjective, hence its affine morphism is a closed immersion. Stability of
closed immersions under pullback, together with the defining pullback
comparison for `formalFunctionsFiniteι`, gives the result.
(blueprint: lem-weil-pbc-formal-functions-finite-sheaf-quotient-closed) -/
theorem formalFunctionsFiniteι_isClosedImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    (y : Y) (n : ℕ) : IsClosedImmersion (formalFunctionsFiniteι f y n) := by
  sorry

/-- Transport the closed-immersion unit quotient to the canonical finite-level map.
Source: Stacks Project, Tags 02OD and 04CJ (1).
Apply `closedImmersion_unit_quotient` to the finite-level closed immersion.
The quotient-base-change ideal calculation identifies its kernel with the
extension of the `(n+1)`-st power of the maximal ideal; the product formula
identifies this with the ideal used by `formalModuleQuotient`. Finally, the
canonical tensor-pullback comparison identifies the resulting unit with
`formalFunctionsFiniteFMap`, yielding the displayed isomorphism and equation.
(blueprint: lem-weil-pbc-formal-functions-finite-sheaf-quotient-iso) -/
theorem formalFunctionsFinite_sheaf_quotient_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) (y : Y) (n : ℕ) :
    let F' := (Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F
    let J := (Scheme.IdealSheafData.ofIdealTop
      ((maximalIdeal (Y.presheaf.stalk y)).map
        (Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv.hom)).comap
          (pullback.fst (Y.fromSpecStalk y) f)
    ∃ e : formalModuleQuotient J (n + 1) F' ≅
        (Scheme.Modules.pushforward (formalFunctionsFiniteι f y n)).obj
          ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F),
      formalModuleQuotientπ J (n + 1) F' ≫ e.hom =
        formalFunctionsFiniteFMap f y F n := by
  sorry

end AlgebraicGeometry
