/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.CechComparisonSystem
import WeilConjectures.AlgebraicGeometry.Cohomology.CechComparisonSystemExistence
import WeilConjectures.AlgebraicGeometry.Cohomology.CechComparisonInverseImageCompatibility

/-! # Inverse-image naturality before affine degeneration

Source: Stacks Project, Tag 01FD, with the normalized comparison of Tag 01EQ.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] cohomologyHasSheafify cohomologyHasExt

/-- Normalized additive Čech comparisons can be chosen compatibly with inverse image.
There is no acyclicity hypothesis and no assertion that either comparison is invertible.

Source: Stacks Project, Tags 01EQ and 01FD. -/
theorem exists_cechComparison_inverseImage
    {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}} {ι : Type u}
    (g : Y ⟶ X) (f : X ⟶ Spec (.of R)) (f' : Y ⟶ Spec (.of S))
    (U : ι → X.Opens) (V : ι → Y.Opens)
    (hcover : iSup U = ⊤) (hcover' : iSup V = ⊤)
    (M : X.Modules) (N : Y.Modules)
    (φ : M ⟶ (pushforward g).obj N)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l))) :
    ∃ c : CechComparisonSystem U hcover,
    ∃ c' : CechComparisonSystem V hcover',
    ∀ (q : ℕ) (z : (cechOver f U M).cycles q) (z' : (cechOver f' V N).cycles q),
      (∀ y : Fin (q + 1) → ι,
        cechCoordinate f' V N q y ((cechOver f' V N).iCycles q z') =
          N.presheaf.map (homOfLE (hinter q y)).op
            (φ.val.app (op (⨅ l, U (y l)))
              (cechCoordinate f U M q y ((cechOver f U M).iCycles q z)))) →
      c'.overMap f' N q ((cechOver f' V N).homologyπ q z') =
        Sheaf.H.map (coeff g φ) q
          (Sheaf.H.mapFunctor (invImage g) (constIso g).symm
            ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) q
              (c.overMap f M q ((cechOver f U M).homologyπ q z))) := by
  obtain ⟨c⟩ := exists_cechComparisonSystem U hcover
  obtain ⟨c'⟩ := exists_cechComparisonSystem V hcover'
  refine ⟨c, c', ?_⟩
  exact cechComparison_inverseImage_compatibility g f f' U V hcover hcover'
    M N φ hinter c c'

end AlgebraicGeometry.Scheme.Modules
