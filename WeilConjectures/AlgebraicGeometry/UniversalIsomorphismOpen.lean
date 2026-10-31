/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import WeilConjectures.AlgebraicGeometry.UniversalSurjectiveFlatOpen
import WeilConjectures.AlgebraicGeometry.UniversalClosedImmersionOpen

/-! # The universal isomorphism locus in the base is open

Source: Stacks Project, Tag 05XD, `spaces-more-morphisms-lemma-where-isomorphism`,
specialized to schemes. (blueprint: lem-sfb-universal-isomorphism-open)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The base changes making a morphism between the specified families an isomorphism
are represented by an open subscheme of the base.

Source: Stacks Project, Tag 05XD, `spaces-more-morphisms-lemma-where-isomorphism`.
(blueprint: lem-sfb-universal-isomorphism-open)

Proof: Universal closedness makes p closed, and local finite presentation makes p
locally of finite type. Apply lem-sfb-universal-surjective-flat-open (Tag 05XC) to
obtain an open U₁ representing the base changes where f is surjective and flat.
Apply lem-sfb-universal-closed-immersion-open (Tag 05XA), using universal closedness
of p and separatedness of q, to obtain an open U₂ representing the base changes
where f is a closed immersion. Take U = U₁ ∩ U₂. A morphism factors through an
open exactly when its image lies in that open, so it factors through U exactly
when it factors through both U₁ and U₂. For any test scheme T, factorization
therefore makes f_T a surjective flat closed immersion, hence an isomorphism by
lem-sfb-surjective-flat-closed-immersion-isomorphism, the specialization of
Flat.isIso_of_surjective_of_mono using the monomorphism and quasi-compactness
of a closed immersion. Conversely an isomorphism is surjective, flat and a
closed immersion, so both universal properties give factorization through U.
The reasoning applies to arbitrary test schemes, including nonreduced ones. -/
theorem exists_universalIsomorphismOpen {B A C : Scheme.{u}}
    (p : A ⟶ B) (q : C ⟶ B) (f : A ⟶ C) (hf : f ≫ q = p)
    [Flat p] [LocallyOfFinitePresentation p] [UniversallyClosed p]
    [LocallyOfFiniteType q] [IsSeparated q] (hq : IsClosedMap q) :
    ∃ U : B.Opens, ∀ (T : Scheme.{u}) (h : T ⟶ B),
      IsIso (pullback.map p h q h f (𝟙 T) (𝟙 B)
        (by simpa only [Category.comp_id] using hf.symm) (by simp)) ↔
      ∃ l : T ⟶ U.toScheme, l ≫ U.ι = h := by
  obtain ⟨U₁, h₁⟩ := exists_universalSurjectiveFlatOpen p q f hf p.isClosedMap hq
  obtain ⟨U₂, h₂⟩ := exists_universalClosedImmersionOpen p q f hf
  refine ⟨U₁ ⊓ U₂, fun T h ↦ ?_⟩
  have factors (V : B.Opens) :
      (∃ l : T ⟶ V.toScheme, l ≫ V.ι = h) ↔ Set.range h ⊆ (V : Set B) := by
    constructor
    · rintro ⟨l, rfl⟩ x ⟨t, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact (Scheme.Opens.range_ι V).le ⟨l t, rfl⟩
    · intro hh
      have hrange : Set.range h ⊆ Set.range V.ι := by
        simpa only [Scheme.Opens.range_ι] using hh
      exact ⟨IsOpenImmersion.lift V.ι h hrange, IsOpenImmersion.lift_fac _ _ _⟩
  have hfactor :
      (∃ l : T ⟶ (U₁ ⊓ U₂).toScheme, l ≫ (U₁ ⊓ U₂).ι = h) ↔
        (∃ l : T ⟶ U₁.toScheme, l ≫ U₁.ι = h) ∧
        (∃ l : T ⟶ U₂.toScheme, l ≫ U₂.ι = h) := by
    rw [factors, factors, factors]
    exact Set.subset_inter_iff
  rw [hfactor, ← h₁ T h, ← h₂ T h]
  constructor
  · intro hg
    have := hg
    exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  · rintro ⟨⟨hsurj, hflat⟩, hclosed⟩
    have := hsurj
    have := hflat
    have := hclosed
    exact Flat.isIso_of_surjective_of_mono _

end AlgebraicGeometry
