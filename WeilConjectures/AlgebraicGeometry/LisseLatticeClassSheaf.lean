/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LisseLatticeCoefficients
public import WeilConjectures.AlgebraicGeometry.LatticeSheafLocallyConstant
public import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
import WeilConjectures.AlgebraicGeometry.LisseLatticeCoefficientNormalization
import WeilConjectures.AlgebraicGeometry.LisseLatticePresentationTransport

/-!
# Locally inhabited lattice-class sheaves

## References

* Bhatt--Scholze, *The pro-étale topology for schemes*, Proposition 6.8.4(6).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false

/-- Lattice classes form a locally constant, locally inhabited sheaf, and every
section has a representative lattice on the localized pro-etale site. -/
theorem exists_lisse_lattice_class_sheaf (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (L : ringedSiteModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheaf l E X)))
    (hL : L.IsFiniteLocallyFree) :
    ∃ F : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)),
      Scheme.IsProEtaleLocallyConstant X F ∧
      (∃ (I : Type (u + 1)) (U : I → X.ProEt),
        (Scheme.ProEt.topology X).CoversTop U ∧
          ∀ i : I, Nonempty (F.obj.obj (op (U i)))) ∧
      ∀ U : X.ProEt, Nonempty (F.obj.obj (op U)) →
        Nonempty (IntegralLatticePair (lisseIntegerToField l E X) L U) := by
  obtain ⟨eA, eE, hsquare, hfree⟩ := lisse_coefficient_normalization l E X L hL
  let L' := (SheafOfModules.pushforward (F := 𝟭 X.ProEt)
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map eE.hom)).obj L
  have : L'.IsFiniteLocallyFree := hfree
  obtain ⟨F, c, hpresentation, hcosets⟩ :=
    integralLatticeSheaf_locallyConstant X l (ULift.{u} E) L'
  apply small_lattice_sheaf_of_coset_presentation (lisseIntegerToField l E X)
    (integralLatticeCoefficientMap X l (ULift.{u} E)) eA eE hsquare L L'
    (Iso.refl _) hfree F c hpresentation
  intro U n e
  obtain ⟨k, hk⟩ := hcosets U n e
  exact ⟨integralMatrixCosets (latticeCoefficientIntegers l (ULift.{u} E)) n,
    inferInstance, ⟨k⟩⟩

end AlgebraicGeometry.ProEtale
