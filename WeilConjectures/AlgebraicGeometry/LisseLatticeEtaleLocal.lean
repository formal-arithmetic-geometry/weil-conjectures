/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LisseLatticeCoefficients
import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
import WeilConjectures.AlgebraicGeometry.LisseLatticeClassSheaf
import WeilConjectures.AlgebraicGeometry.LisseLatticeSliceTransport

/-!
# Etale-local integral lattices in lisse coefficient sheaves

## References

* Bhatt--Scholze, *The pro-étale topology for schemes*, Proposition 6.8.4(6) and
  Definition 6.8.3.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtale

/-- A lisse coefficient sheaf admits lisse integral lattices after an etale cover.
The right-hand presheaf is the sectionwise slice-site presentation of `f⁻¹ L`, with
its coefficient action identified by the identity on continuous functions. Finite local
freeness allows variable ranks and rank zero. -/
theorem exists_lisse_lattice_etale_local (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (L : ringedSiteModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheaf l E X)))
    (hL : L.IsFiniteLocallyFree) :
    ∃ (I : Type (u + 1)) (Y : I → X.Etale),
      (X.smallEtaleTopology).CoversTop Y ∧
      ∀ i : I, ∃ M : ringedSiteModules.{u + 1}
        ((sheafCompose (Scheme.ProEt.topology (Y i).left)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (lisseIntegerSheaf l E (Y i).left)),
        M.IsFiniteLocallyFree ∧
        Nonempty ((SheafOfModules.changeOfRings
          (lisseIntegerToField l E (Y i).left) M).val ≅
          (PresheafOfModules.pushforward
            (lisseEtaleCoefficientIdentification l E (Y i).hom)).obj L.val) := by
  obtain ⟨F, hconst, hlocal, hrepresent⟩ := exists_lisse_lattice_class_sheaf l E X L hL
  have hclass := ((Scheme.proEtale_locallyClassical_etaleCover X F).2.1 hconst).1
  obtain ⟨I, Y, hcover, hsections⟩ :=
    (Scheme.proEtale_locallyClassical_etaleCover X F).2.2 hclass hlocal
  refine ⟨I, Y, hcover, fun i ↦ ?_⟩
  obtain ⟨P⟩ := hrepresent ((Scheme.toProEt X).obj (Y i)) (hsections i)
  exact lisse_lattice_of_slice l E X L (Y i) P

end AlgebraicGeometry.ProEtale
