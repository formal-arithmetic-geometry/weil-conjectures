/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Restrictions of morphisms of schemes along open immersions

We record:

- `AlgebraicGeometry.morphismRestrictArrowIso` — transport of a morphism restriction along
  compatible open immersions;
- `AlgebraicGeometry.mem_opensRange_homOfLE` / `AlgebraicGeometry.homOfLE_preimage_opensRange`
  — membership and preimage formulas for the ranges of inclusions of opens;
- `AlgebraicGeometry.isIso_morphismRestrict_of_isPullback` — a base change of a morphism
  that is an isomorphism over an open is an isomorphism over the preimage of that open;
- `AlgebraicGeometry.Scheme.Hom.liftPreimage` — the factorization of a morphism through a
  preimage open containing its range;
- `AlgebraicGeometry.Scheme.Hom.liftOfIsIsoRestrict` — the (unique) lift of a morphism
  along a morphism that is an isomorphism over an open containing its range.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y Z Z' : Scheme.{u}}

/-- If `e ≫ f = q ≫ j` with `e`, `j` open immersions and `f ⁻¹ᵁ (range j) = range e`, then
the restriction `f ∣_ j.opensRange` is isomorphic to `q` in the arrow category. -/
noncomputable def morphismRestrictArrowIso (f : X ⟶ Y) {e : Z ⟶ X} {j : Z' ⟶ Y}
    (q : Z ⟶ Z') [IsOpenImmersion e] [IsOpenImmersion j]
    (w : e ≫ f = q ≫ j) (h : f ⁻¹ᵁ j.opensRange = e.opensRange) :
    Arrow.mk (f ∣_ j.opensRange) ≅ Arrow.mk q := by
  have hα : Set.range ⇑(f ⁻¹ᵁ j.opensRange).ι = Set.range ⇑e := by
    rw [Scheme.Opens.range_ι, h]; rfl
  have hβ : Set.range ⇑j.opensRange.ι = Set.range ⇑j := by
    rw [Scheme.Opens.range_ι]; rfl
  refine Arrow.isoMk' (f ∣_ j.opensRange) q
    (IsOpenImmersion.isoOfRangeEq (f ⁻¹ᵁ j.opensRange).ι e hα)
    (IsOpenImmersion.isoOfRangeEq j.opensRange.ι j hβ) ?_
  rw [← cancel_mono j, Category.assoc, Category.assoc, ← w,
    IsOpenImmersion.isoOfRangeEq_hom_fac_assoc,
    IsOpenImmersion.isoOfRangeEq_hom_fac, morphismRestrict_ι]

/-- Membership in the range of the inclusion of a smaller open. -/
lemma mem_opensRange_homOfLE {X : Scheme.{u}} {U V : X.Opens} (hUV : U ≤ V)
    (x : V.toScheme) : x ∈ (X.homOfLE hUV).opensRange ↔ x.1 ∈ U := by
  rw [Scheme.opensRange_homOfLE]
  exact Iff.rfl

/-- Preimages of ranges of inclusions of opens. -/
lemma homOfLE_preimage_opensRange {X : Scheme.{u}} {U V W : X.Opens} (hWU : W ≤ U)
    (hUV : U ≤ V) :
    X.homOfLE hUV ⁻¹ᵁ (X.homOfLE (hWU.trans hUV)).opensRange =
      (X.homOfLE hWU).opensRange := by
  rw [Scheme.opensRange_homOfLE, Scheme.opensRange_homOfLE, ← Scheme.Hom.comp_preimage,
    Scheme.homOfLE_ι]

/-- **A base change of an isomorphism over an open is an isomorphism over the preimage
of that open**: if the square

```
T' --ρ--> T
|         |
p         q
↓         ↓
U --j---> X
```

is cartesian and `j` restricts to an isomorphism over an open `V ⊆ X`, then `ρ` restricts
to an isomorphism over `q ⁻¹ᵁ V`. -/
lemma isIso_morphismRestrict_of_isPullback {T T' U : Scheme.{u}} {ρ : T' ⟶ T} {p : T' ⟶ U}
    {q : T ⟶ X} {j : U ⟶ X} (H : IsPullback ρ p q j) (V : X.Opens) [IsIso (j ∣_ V)] :
    IsIso (ρ ∣_ (q ⁻¹ᵁ V)) := by
  -- `T'|_{ρ⁻¹ q⁻¹ V}` is `U ×_X T|_{q⁻¹ V}` by pasting the restriction square onto the
  -- cartesian square, ...
  have hA : IsPullback (ρ ∣_ (q ⁻¹ᵁ V)) (ρ ⁻¹ᵁ (q ⁻¹ᵁ V)).ι (q ⁻¹ᵁ V).ι ρ :=
    isPullback_morphismRestrict _ _
  have hpaste := hA.paste_vert H
  -- ... and `T|_{q⁻¹ V} ⟶ X` factors through `V`, so it is `j ∣_ V` base-changed.
  have ht : IsPullback (j ⁻¹ᵁ V).ι (j ∣_ V) j V.ι := (isPullback_morphismRestrict j V).flip
  have hs : IsPullback ((ρ ⁻¹ᵁ (q ⁻¹ᵁ V)).ι ≫ p) (ρ ∣_ (q ⁻¹ᵁ V)) j ((q ∣_ V) ≫ V.ι) := by
    rw [morphismRestrict_ι]
    exact hpaste.flip
  exact (IsPullback.of_right' hs ht).flip.isIso_fst_of_isIso

section LiftPreimage

variable {P : Scheme.{u}} (g : P ⟶ X) (U : X.Opens) (k : Z ⟶ P)
    (hk : Set.range (k ≫ g) ⊆ (U : Set X))

include hk in
/-- A morphism whose composite with `g : P ⟶ X` has range inside an open `U ⊆ X` has
range inside the open `g ⁻¹ᵁ U` of `P`. -/
lemma range_subset_range_preimage_ι : Set.range k ⊆ Set.range (g ⁻¹ᵁ U).ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨z, rfl⟩
  simpa [Scheme.Hom.comp_apply] using hk ⟨z, rfl⟩

/-- **The lift into a preimage open**: a morphism `k : Z ⟶ P` whose composite with
`g : P ⟶ X` has range inside an open `U ⊆ X` factors through the open `g ⁻¹ᵁ U`. -/
noncomputable def Scheme.Hom.liftPreimage : Z ⟶ (g ⁻¹ᵁ U).toScheme :=
  IsOpenImmersion.lift (g ⁻¹ᵁ U).ι k (range_subset_range_preimage_ι g U k hk)

@[reassoc (attr := simp)]
lemma Scheme.Hom.liftPreimage_ι : g.liftPreimage U k hk ≫ (g ⁻¹ᵁ U).ι = k :=
  IsOpenImmersion.lift_fac _ _ _

end LiftPreimage

section Lift

variable {X' : Scheme.{u}} (π : X' ⟶ X) (U : X.Opens) [IsIso (π ∣_ U)] (h : Z ⟶ X)
    (hrange : Set.range h ⊆ (U : Set X))

/-- **The lift along a morphism that is an isomorphism over an open**: if `π : X' ⟶ X`
restricts to an isomorphism over an open `U ⊆ X` and the range of `h : Z ⟶ X` is
contained in `U`, then `h` lifts along `π`, by inverting `π ∣_ U`. -/
noncomputable def Scheme.Hom.liftOfIsIsoRestrict : Z ⟶ X' :=
  IsOpenImmersion.lift U.ι h (by rwa [Scheme.Opens.range_ι]) ≫ inv (π ∣_ U) ≫ (π ⁻¹ᵁ U).ι

@[reassoc (attr := simp)]
lemma Scheme.Hom.liftOfIsIsoRestrict_comp :
    π.liftOfIsIsoRestrict U h hrange ≫ π = h := by
  rw [Scheme.Hom.liftOfIsIsoRestrict, Category.assoc, Category.assoc, ← morphismRestrict_ι,
    IsIso.inv_hom_id_assoc]
  exact IsOpenImmersion.lift_fac _ _ _

/-- **Uniqueness of the lift**: two morphisms to `X'` whose composites with `π` agree and
land in an open `U` over which `π` is an isomorphism are equal. -/
lemma Scheme.Hom.hom_ext_of_isIso_restrict {h₁ h₂ : Z ⟶ X'} (hcomp : h₁ ≫ π = h₂ ≫ π)
    (h₁range : Set.range (h₁ ≫ π) ⊆ (U : Set X)) : h₁ = h₂ := by
  -- both morphisms factor through the open `π ⁻¹ᵁ U`, where `π` is an isomorphism
  set k₁ := π.liftPreimage U h₁ h₁range
  set k₂ := π.liftPreimage U h₂ (hcomp ▸ h₁range)
  have e₁ : k₁ ≫ (π ⁻¹ᵁ U).ι = h₁ := π.liftPreimage_ι U h₁ h₁range
  have e₂ : k₂ ≫ (π ⁻¹ᵁ U).ι = h₂ := π.liftPreimage_ι U h₂ (hcomp ▸ h₁range)
  have hk : k₁ = k₂ := by
    rw [← cancel_mono (π ∣_ U), ← cancel_mono U.ι]
    simp only [Category.assoc, morphismRestrict_ι]
    rw [← Category.assoc, ← Category.assoc, e₁, e₂, hcomp]
  rw [← e₁, ← e₂, hk]

end Lift

end AlgebraicGeometry
