/- Copyright (c) 2026. All rights reserved. -/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
public import WeilConjectures.TateTwist.ProEtale
import Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Purity

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left]

omit [SmoothOfRelativeDimension d f.left] in
/--
The normalized diagonal/DNC construction of smooth purity provides mutually inverse maps
between the exceptional inverse image of the coefficient unit and the shifted Tate twist.
The finite coefficient maps are compatible with coefficient extension, so their coherent
reconstruction gives the displayed maps in the condensed bounded constructible category.
This is the geometric reconstruction step: the source is SGA 4, Exposé XVIII, Théorème 3.2.5,
and the condensed coefficient passage is the reconstruction argument of the smooth-purity
blueprint (finite diagonal class, deformation to the normal bundle, and the coherent
finite-extension tower).

(blueprint: lem-pur-condensed-normalized-witness)
-/
theorem exists_normalizedSmoothPurityMaps :
    Nonempty {p :
      (((boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))).obj ⟶
        (shiftFunctor _ (2 * d : ℤ)).obj (tateTwistDerived X.left ℓ d)) ×
      (((shiftFunctor _ (2 * d : ℤ)).obj (tateTwistDerived X.left ℓ d)) ⟶
        ((boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj
          (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))).obj)
      // p.1 ≫ p.2 = 𝟙 _ ∧ p.2 ≫ p.1 = 𝟙 _} := by
  sorry

end Purity

end AlgebraicGeometry.ProEtale.CondensedRing
