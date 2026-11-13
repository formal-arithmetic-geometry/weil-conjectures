/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechTotal
import WeilConjectures.AlgebraicGeometry.PrincipalOpenSectionsResolutionQuasiIso
import WeilConjectures.AlgebraicGeometry.PrincipalCechFiniteColumnModel
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns

/-!
# Principal Čech totalization of a quasi-coherent resolution

## References

* Stacks Project, Tag 08D2, <https://stacks.math.columbia.edu/tag/08D2>
* Stacks Project, Tag 08C2, <https://stacks.math.columbia.edu/tag/08C2>
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- On a finite principal-open cover, totalization takes a K-injective resolution
of a termwise quasi-coherent complex to a quasi-isomorphism. The resolution's
terms need not be quasi-coherent (Stacks, Tags 08D2 and 08C2). -/
theorem principalCech_resolution_quasiIso
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (F J : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (hF : ∀ n : ℤ, (F.X n).IsQuasicoherent)
    [J.IsKInjective] (i : F ⟶ J) [QuasiIso i] :
    QuasiIso ((principalCechFunctor r f).map i) := by
  have hsections (S : {S : Finset (Fin r) // S.Nonempty}) :
      QuasiIso (((affineOpenSections A
        (principalCechIntersection r f S.val)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map i) := by
    exact principalOpenSections_resolution_quasiIso A (∏ j ∈ S.val, f j) F J hF i
  obtain ⟨K, L, φ, hKge, hKle, hLge, hLle, hcolumns, ⟨e⟩⟩ :=
    principalCech_finiteColumn_model A r f F J i
  have := hKge
  have := hKle
  have := hLge
  have := hLle
  have htotal : QuasiIso (HomologicalComplex₂.total.map φ (ComplexShape.up ℤ)) :=
    HomologicalComplex₂.total.quasiIso_map_of_finitely_many_columns φ 0 ((r : ℤ) - 1)
      (fun p hp hp' ↦ hcolumns p hp hp' hsections)
  exact (quasiIso_iff_of_arrow_mk_iso _ _ e).mpr htotal

end AlgebraicGeometry
