/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechTotal
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.AlgebraicGeometry.PrincipalCechBicomplexComparison

/-!
# Finite-column bicomplex models for principal Čech maps

## References

* Stacks Project, Tag 08D1, <https://stacks.math.columbia.edu/tag/08D1>
* Stacks Project, Tag 08C2, <https://stacks.math.columbia.edu/tag/08C2>
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A principal Čech map is a total map of bicomplexes supported in columns `0..,r-1`.
Column quasi-isomorphisms require only the section quasi-isomorphisms on intersections.
No quasi-coherence, K-injectivity or quasi-isomorphism assumption is made on `i` itself
(Stacks, Tags 08D1 and 08C2). -/
theorem principalCech_finiteColumn_model
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (F G : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (i : F ⟶ G) :
    ∃ (K L : HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)) (φ : K ⟶ L),
      CochainComplex.IsStrictlyGE K 0 ∧ CochainComplex.IsStrictlyLE K ((r : ℤ) - 1) ∧
      CochainComplex.IsStrictlyGE L 0 ∧ CochainComplex.IsStrictlyLE L ((r : ℤ) - 1) ∧
      (∀ p : ℤ, 0 ≤ p → p ≤ (r : ℤ) - 1 →
        (∀ S : {S : Finset (Fin r) // S.Nonempty},
          QuasiIso (((affineOpenSections A
            (principalCechIntersection r f S.val)).mapHomologicalComplex
              (ComplexShape.up ℤ)).map i)) → QuasiIso (φ.f p)) ∧
      Nonempty (Arrow.mk ((principalCechFunctor r f).map i) ≅
        Arrow.mk (HomologicalComplex₂.total.map φ (ComplexShape.up ℤ))) := by
  refine ⟨principalCechBicomplex r f F, principalCechBicomplex r f G,
    (principalCechBicomplexFunctor r f).map i, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (CochainComplex.isStrictlyGE_iff _ 0).mpr
    intro p hp
    exact principalCechColumn_isZero r f p (Or.inl hp) F
  · apply (CochainComplex.isStrictlyLE_iff _ ((r : ℤ) - 1)).mpr
    intro p hp
    exact principalCechColumn_isZero r f p (Or.inr hp) F
  · apply (CochainComplex.isStrictlyGE_iff _ 0).mpr
    intro p hp
    exact principalCechColumn_isZero r f p (Or.inl hp) G
  · apply (CochainComplex.isStrictlyLE_iff _ ((r : ℤ) - 1)).mpr
    intro p hp
    exact principalCechColumn_isZero r f p (Or.inr hp) G
  · intro p _ _ hi
    exact principalCechColumn_quasiIso r f p F G i hi
  · obtain ⟨e⟩ := principalCechBicomplexComparison_exists r f
    exact ⟨Arrow.isoOfNatIso e (Arrow.mk i)⟩

end AlgebraicGeometry
