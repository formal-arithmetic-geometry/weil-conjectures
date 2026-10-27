module

public import Sheaf.Paper.FiniteTorLocalizingClosureOfSize
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek

/-! # Compact-support restrictions with a specified coproduct universe

Source: blueprint main-20261015, sk-prop-sf-existence, definition of the left functor
(blueprint: def-sfb-finite-tor-localizing-lower-shriek-of-size).

The ambient compactification composite and Brown existence interface remain unchanged.
Only the indexing universe of the full hulls is made explicit.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe w u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Restriction of the actual ambient compactification composite to finite-Tor hulls
with coproducts indexed in `w`. The argument supplies membership only; objects and maps
are those of the existing ambient functor. No adjoint is chosen by this definition.
Source: blueprint main-20261015, sk-prop-sf-existence, displayed compact-support functor
(blueprint: def-sfb-finite-tor-localizing-lower-shriek-of-size). -/
def finiteTorLocalizingLowerShriekOfSize
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (h : ∀ K, finiteTorLocalizingClosureOfSize.{w} Λ X K →
      finiteTorLocalizingClosureOfSize.{w} Λ Y
        ((rightDerivedLowerShriekOfCompactification Λ c).obj K)) :
    (finiteTorLocalizingClosureOfSize.{w} Λ X).FullSubcategory ⥤
      (finiteTorLocalizingClosureOfSize.{w} Λ Y).FullSubcategory :=
  (finiteTorLocalizingClosureOfSize.{w} Λ Y).lift
    ((finiteTorLocalizingClosureOfSize.{w} Λ X).ι ⋙
      rightDerivedLowerShriekOfCompactification Λ c)
    (fun K ↦ h K.obj K.property)

end AlgebraicGeometry.ProEtale.CondensedRing
