module

public import Sheaf.RingTheory.MPseudoCoherent
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Away.Basic
import Sheaf.RingTheory.FiniteHomologyOfMPseudoCoherent
import Sheaf.RingTheory.PseudoCoherentDistinguishedTriangle

@[expose] public section

universe w₁ w₂ v₁ u₁

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

/-- Exact localization transports pseudo-coherence across the cone constructed in
`localization_cone_construction` (Stacks, Tag 066D).
(blueprint: lem-pc-m-pseudo-coherent-localization-cone-local).

Proof: apply exactness of localization and the first clause of the distinguished-triangle
pseudo-coherence lemma to the localized cone triangle. -/
theorem localization_cone_local
    {A : Type u₁} [CommRing A] [HasDerivedCategory.{w₁} (ModuleCat.{max u₁ v₁} A)]
    (M : CochainComplex (ModuleCat.{max u₁ v₁} A) ℤ)
    (r : ℕ) (f : Fin r → A)
    [∀ i : Fin r, HasDerivedCategory.{w₂} (ModuleCat.{max u₁ v₁}
      (Localization.Away (f i)))]
    (hf : Ideal.span (Set.range f) = ⊤)
    (m n : ℤ) (hmn : m ≤ n)
    (hvan : ∀ j : ℤ, n < j → IsZero
      ((homologyFunctor (ModuleCat.{max u₁ v₁} A) j).obj (Q.obj M)))
    (hlocal : ∀ i : Fin r, IsMPseudoCoherent m (Q.obj ((Functor.mapHomologicalComplex
      (ModuleCat.extendScalars (algebraMap A (Localization.Away (f i))))
      (ComplexShape.up ℤ)).obj M)))
    (E N : CochainComplex (ModuleCat.{max u₁ v₁} A) ℤ)
    (a : Q.obj E ⟶ Q.obj M) (b : Q.obj M ⟶ Q.obj N)
    (c : Q.obj N ⟶ (Q.obj E)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk a b c ∈ distTriang (DerivedCategory (ModuleCat.{max u₁ v₁} A)))
    (hE : IsMPseudoCoherent m (Q.obj E))
    (hN : ∀ j : ℤ, n - 1 < j → IsZero
      ((homologyFunctor (ModuleCat.{max u₁ v₁} A) j).obj (Q.obj N))) :
    ∀ i : Fin r, IsMPseudoCoherent m (Q.obj ((Functor.mapHomologicalComplex
      (ModuleCat.extendScalars (algebraMap A (Localization.Away (f i))))
      (ComplexShape.up ℤ)).obj N)) := by
  sorry

end DerivedCategory
