/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Blowup.AdmissibleBlowup
public import WeilConjectures.Compactification.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!

# Boundary preparation for the two-open compactification theorem

This file provides the boundary-preparation inputs of the two-open compactification
theorem, following the blueprint chapter "Nagata compactification", sections
"Separating boundary pieces" and "The two-open compactification theorem"
(proof order items 34 and 36):

- `AlgebraicGeometry.Compactification.denseRefinement`: the scheme-theoretically dense
  refinement of a compactification, replacing the ambient scheme by the
  scheme-theoretic image of the open immersion (blueprint:
  `def:nagata-dense-refinement`, `prop:nagata-dense-refinement`), together with
  `AlgebraicGeometry.exists_compactification_isSchemeTheoreticallyDominant`
  (blueprint: `def:nagata-two-open-dense-compactifications`,
  `lemma:nagata-two-open-dense-compactifications`; proof order item 34);
- `AlgebraicGeometry.exists_admissibleBlowup_disjoint_closures`: the
  **constructible-boundary separation blow-up** (Stacks Project Tags 080P and 0F3V):
  two disjoint constructible closed subsets of a quasi-compact open `U ⊆ X` acquire
  disjoint closures of their inverse images after a `U`-admissible blow-up
  (blueprint: `def:nagata-separate-constructible-closed`,
  `lemma:nagata-separate-constructible-closed`,
  `def:nagata-two-open-prepared-boundaries`; proof order item 36).

The proof of `exists_admissibleBlowup_disjoint_closures` combines the boundary
separation theorem `disjoint_range_strictTransformMap_sup` of
`WeilConjectures.Blowup.AdmissibleBlowup` (Stacks Tag 0F3V) with the range
comparisons of `WeilConjectures.Compactification.StrictTransform`: the closure of
the inverse image of the `U`-part of a closed center is contained in the strict
transform (`closure_preimage_subset_range_strictTransformMap`).

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section DenseRefinement

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- The **scheme-theoretically dense refinement** of a compactification of a
quasi-compact morphism: replace the ambient scheme by the scheme-theoretic image of
the open immersion. The refined open immersion is the factor map `c.i.toImage`, an
open immersion because `c.i` is a quasi-compact immersion; the refined proper
morphism is the composite of the image closed immersion with `c.g`. The original
factorization triangle refines as

```
X --c.i.toImage--> c.i.image --c.i.imageι--> c.Z
 \                     |                     /
  \                    |                    /
   f            c.i.imageι ≫ c.g        c.g
    \                  |                 /
     \                 ↓                /
      *--------------> Y <-------------*
```

(Blueprint: `def:nagata-dense-refinement`.) -/
def Compactification.denseRefinement (c : Compactification f) [QuasiCompact f] :
    Compactification f where
  Z := c.i.image
  g := c.i.imageι ≫ c.g
  i := c.i.toImage
  comm := by
    rw [Scheme.Hom.toImage_imageι_assoc]
    exact c.comm
  isProper := inferInstance
  isOpenImmersion := by
    have : QuasiCompact c.i := c.quasiCompact_openImmersion ‹_›
    infer_instance

/-- The open immersion into the dense refinement of a compactification is
scheme-theoretically dominant: it is the factor map through the scheme-theoretic
image. (Blueprint: `prop:nagata-dense-refinement`.) -/
theorem Compactification.isSchemeTheoreticallyDominant_denseRefinement_i
    (c : Compactification f) [QuasiCompact f] :
    IsSchemeTheoreticallyDominant c.denseRefinement.i :=
  have : QuasiCompact c.i := c.quasiCompact_openImmersion ‹_›
  inferInstanceAs (IsSchemeTheoreticallyDominant c.i.toImage)

/-- **Choice of dense compactifications** (blueprint:
`def:nagata-two-open-dense-compactifications`,
`lemma:nagata-two-open-dense-compactifications`; proof order item 34): every
compactifiable quasi-compact morphism admits a compactification whose open immersion
is scheme-theoretically dominant, namely the dense refinement of any chosen
compactification. -/
theorem exists_compactification_isSchemeTheoreticallyDominant
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] :
    ∃ c : Compactification f, IsSchemeTheoreticallyDominant c.i :=
  ⟨_, (HasCompactification.compactification f).isSchemeTheoreticallyDominant_denseRefinement_i⟩

end DenseRefinement

section BoundarySeparation

variable {X : Scheme.{u}} {U : X.Opens}

/-- The closure of the inverse image of the `U`-part of a closed center is contained
in the range of its strict transform along a `U`-admissible blow-up: the case of
`AlgebraicGeometry.closure_preimage_subset_range_strictTransformMap` for the closed
subscheme of an ideal sheaf and the blow-up of an admissible center. -/
theorem IsAdmissible.closure_preimage_subset_range_strictTransformMap
    (B : IsAdmissible X U) (I : X.IdealSheafData) {T : Set U.toScheme}
    (hT : T ⊆ U.ι ⁻¹' (I.support : Set X)) :
    closure (B.I.blowupMap ⁻¹' (U.ι '' T)) ⊆
      Set.range (strictTransformMap I.subschemeι B.I.blowupMap B.preservedOpen) :=
  AlgebraicGeometry.closure_preimage_subset_range_strictTransformMap I.subschemeι
    B.I.blowupMap B.le_preservedOpen
    (by rwa [Scheme.IdealSheafData.range_subschemeι])

/-- **The constructible-boundary separation blow-up** (Stacks Project Tags 080P and
0F3V): let `X` be qcqs, `U ⊆ X` a quasi-compact open, and let `T₁`, `T₂` be disjoint
closed subsets of `U` with quasi-compact complements (i.e. constructible closed
subsets of `U`). Then there is a `U`-admissible blow-up of `X` in which the closures
of the inverse images of `T₁` and `T₂` are disjoint.

The blow-up is the boundary-separation blow-up of the sum of two finite-type ideals
`I₁`, `I₂` extending the vanishing ideals of `T₁`, `T₂` from `U` (Stacks Tags 01PH
and 01PF, `Scheme.IdealSheafData.exists_finiteType_preimage_coe_support_eq`); the
closure of the inverse image of `Tᵢ` is contained in the strict transform of `V(Iᵢ)`
(`closure_preimage_subset_range_strictTransformMap`), and these strict transforms are
disjoint by `disjoint_range_strictTransformMap_sup`.
(Blueprint: `def:nagata-separate-constructible-closed`,
`lemma:nagata-separate-constructible-closed`,
`def:nagata-two-open-prepared-boundaries`, `lemma:nagata-prepared-boundaries`;
proof order item 36.) -/
theorem exists_admissibleBlowup_disjoint_closures
    [CompactSpace X] [QuasiSeparatedSpace X] (hU : IsCompact (U : Set X))
    {T₁ T₂ : Set U.toScheme} (hT₁ : IsClosed T₁) (hT₂ : IsClosed T₂)
    (hc₁ : IsCompact T₁ᶜ) (hc₂ : IsCompact T₂ᶜ) (hdisj : Disjoint T₁ T₂) :
    ∃ B : IsAdmissible X U,
      Disjoint (closure (B.I.blowupMap ⁻¹' (U.ι '' T₁)))
        (closure (B.I.blowupMap ⁻¹' (U.ι '' T₂))) := by
  -- extend the vanishing ideals of `T₁`, `T₂` to finite-type ideals on `X`
  obtain ⟨I₁, hI₁ft, hpre₁⟩ :=
    Scheme.IdealSheafData.exists_finiteType_preimage_coe_support_eq hU hT₁ hc₁
  obtain ⟨I₂, hI₂ft, hpre₂⟩ :=
    Scheme.IdealSheafData.exists_finiteType_preimage_coe_support_eq hU hT₂ hc₂
  -- the common support misses `U`
  have hdisjX : Disjoint (U : Set X) ((I₁.support : Set X) ∩ (I₂.support : Set X)) := by
    rw [Set.disjoint_left]
    rintro x hxU ⟨hx1, hx2⟩
    obtain ⟨t, rfl⟩ : x ∈ Set.range U.ι := by
      rwa [Scheme.Opens.range_ι]
    exact Set.disjoint_left.mp hdisj (hpre₁ ▸ Set.mem_preimage.mpr hx1)
      (hpre₂ ▸ Set.mem_preimage.mpr hx2)
  -- blow up the sum of the ideals
  let B := separationBlowup I₁ I₂ hI₁ft hI₂ft hdisjX
  exact ⟨B, (disjoint_range_strictTransformMap_sup I₁ I₂ hI₁ft hI₂ft).mono
    (B.closure_preimage_subset_range_strictTransformMap I₁ hpre₁.symm.le)
    (B.closure_preimage_subset_range_strictTransformMap I₂ hpre₂.symm.le)⟩

end BoundarySeparation

end AlgebraicGeometry
