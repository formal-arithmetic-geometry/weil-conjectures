module
public import Sheaf.AlgebraicGeometry.FormalFunctionsFinitePullback
public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Sheaf.AlgebraicGeometry.QuotientBaseChangeIdeal
import Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient
import Sheaf.AlgebraicGeometry.AffineMorphismCohomologyEdge
import Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial
import Sheaf.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties
import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
namespace AlgebraicGeometry
/-- Finite quotient-system isomorphism and quotient-unit factorization.
Source: Stacks Project, Tag 02OD and Tag 089W.
(blueprint: lem-weil-pbc-formal-functions-finite-quotient-iso-b)
Proof: Construct the finite-level closed-immersion quotient identifications, apply
cohomology and the affine edge isomorphism, and check adjacent-level naturality.
The quotient-unit equation is the defining adjunction-unit equation. -/
theorem formalFunctions_finite_quotient_iso_b {X Y : Scheme.{u}} (f : X ⟶ Y)
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
    ∃ b : formalCompletionSystem J F' ⋙ C ≅
      formalFibreCohomologySystem f y F p ⋙ ModuleCat.restrictScalars
        (algebraMap (Y.presheaf.stalk y)
          (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))),
    ∀ (n : ℕ) (z : formalFunctionsLocalCohomology f y F p),
      (b.hom.app (op n)) ((C.map (formalModuleQuotientπ J (n + 1) F')) z) =
        formalFunctionsFinitePullback f y F p n z := by
  sorry
end AlgebraicGeometry
