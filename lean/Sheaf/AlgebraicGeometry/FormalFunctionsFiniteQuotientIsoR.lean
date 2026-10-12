module
public import Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientIsoB
import Sheaf.AlgebraicGeometry.AffineMorphismCohomologyEdge
import Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient
import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Sheaf.AlgebraicGeometry.FormalFunctionsFinitePullback
import Sheaf.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties
import Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial
import Sheaf.AlgebraicGeometry.QuotientBaseChangeIdeal
import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
namespace AlgebraicGeometry
/-- The finite pullback maps are linear and factor through a quotient-system isomorphism.
Source: Stacks Project, Tag 02OD and Tags 01F7, 01FB.
(blueprint: lem-weil-pbc-formal-functions-finite-quotient-iso-r)
Proof: Define each component by canonical finite pullback. The scalar identity for
restricted completed scalars proves linearity, and the quotient-unit equation gives
both displayed component formulas. -/
theorem formalFunctions_finite_quotient_iso_r {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [IsLocallyNoetherian Y] (F : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F) (y : Y) (p : ℕ) :
    let X' := pullback (Y.fromSpecStalk y) f
    let f' := pullback.fst (Y.fromSpecStalk y) f
    let F' := (Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F
    let J := (Scheme.IdealSheafData.ofIdealTop
      ((maximalIdeal (Y.presheaf.stalk y)).map
        (Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv.hom)).comap f'
    let C := RingedSpace.moduleCohomology X'.toRingedSpace p ⋙
      ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv ≫ f'.appTop).hom
    ∀ (b : formalCompletionSystem J F' ⋙ C ≅
      formalFibreCohomologySystem f y F p ⋙ ModuleCat.restrictScalars
        (algebraMap (Y.presheaf.stalk y)
          (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)))),
      (∀ (n : ℕ) (z : formalFunctionsLocalCohomology f y F p),
        (b.hom.app (op n)) ((C.map (formalModuleQuotientπ J (n + 1) F')) z) =
          formalFunctionsFinitePullback f y F p n z) →
      ∃ r : ∀ n : ℕ, formalFunctionsLocalCohomology f y F p →ₗ[Y.presheaf.stalk y]
        formalFibreCohomologyLocal f y F p n,
        (∀ (n : ℕ) (z : formalFunctionsLocalCohomology f y F p),
          r n z = (b.hom.app (op n)) ((C.map (formalModuleQuotientπ J (n + 1) F')) z)) ∧
        ∀ (n : ℕ) (z : formalFunctionsLocalCohomology f y F p),
          r n z = formalFunctionsFinitePullback f y F p n z := by
  sorry
end AlgebraicGeometry
