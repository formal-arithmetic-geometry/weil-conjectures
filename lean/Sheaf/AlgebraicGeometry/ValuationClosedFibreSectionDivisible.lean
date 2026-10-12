module

public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.ValuationClosedFibreSectionVanishing
import Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry.Scheme.Modules

/-- A section vanishing on the closed fibre is divisible by a maximal-ideal element,
assuming the closed fibre is integral.
Source: Stacks Project, More on Morphisms, Tag 0EX8.
(blueprint: new-valuation-closed-fibre-section-divisible)
-/
theorem closed_fibre_section_is_divisible
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of A))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (L : X.Modules) [L.IsInvertible]
    (hX₀ : IsIntegral (Limits.pullback f (Spec.map
      (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))))))
    (s : Γ(L, ⊤))
    (hs : (((Classical.choose (exists_tensorPullbackAdjunction
      (f.fiberι (IsLocalRing.closedPoint A)))).unit.app L).val.app (op ⊤) s = 0)) :
    ∃ π : A, π ∈ IsLocalRing.maximalIdeal A ∧ ∃ t : Γ(L, ⊤),
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom π • t = s := by sorry

end AlgebraicGeometry.Scheme.Modules
