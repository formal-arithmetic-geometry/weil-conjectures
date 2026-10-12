/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.DoubleDual

/-!
# Isomorphisms in the derived category are local on an open cover

A morphism of `D(X_ét, Λ)` is an isomorphism as soon as its restrictions to the members of an
open cover of `X` are.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Locality of isomorphisms in `D(X_ét, Λ)`.** A morphism of `D(X_ét, Λ)` is an isomorphism
as soon as its restrictions to the members of an open cover of `X` are. -/
theorem isIso_of_forall_isIso_leftDerivedUpperStar_map {X : Scheme.{u}} {ι : Type*}
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    {K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (f : K ⟶ L) (h : ∀ i, IsIso ((L(((U i).ι)^*[ModuleCat.{u + 1} Λ])).map f)) :
    IsIso f := by
  have hx (x : X) : ∃ i, x ∈ U i := by
    rw [← TopologicalSpace.Opens.mem_iSup, hU]
    trivial
  choose c hc using hx
  rw [DerivedCategory.isIso_iff]
  intro n
  refine isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ)
    (fun x ↦ (U (c x)).ι) (fun x ↦ ⟨x, ⟨x, hc x⟩, rfl⟩) _ fun x ↦ ?_
  have h₁ : IsIso (D(((U (c x)).ι)^*[ModuleCat.{u + 1} Λ]).map f) :=
    (NatIso.isIso_map_iff (leftDerivedUpperStarIsoMapDerivedCategory _ (U (c x)).ι) f).1 (h _)
  exact (NatIso.isIso_map_iff
    ((((U (c x)).ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso n) f).2
      (inferInstanceAs (IsIso ((DerivedCategory.homologyFunctor _ n).map
        (D(((U (c x)).ι)^*[ModuleCat.{u + 1} Λ]).map f))))

end Etale

end AlgebraicGeometry
