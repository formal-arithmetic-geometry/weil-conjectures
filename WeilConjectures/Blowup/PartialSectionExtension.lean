/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.AdmissibleBlowup

/-!

# Extending a partial section after an admissible blow-up

This file states **Conrad's Theorem 2.4** in the reduced form in which it is used on the
Conrad/Zariski's-Main-Theorem route to elimination of indeterminacy (Stacks Project Tag
081S), together with the special case recorded as Conrad's Remark 2.5.

Reference: Brian Conrad, *Deligne's notes on Nagata compactifications*, Theorem 2.4 and
Remark 2.5.

Conrad states his theorem over an auxiliary base `S`, for a morphism `Y ⟶ S` and a
rational `S`-map from `X` to `Y`; the first step of his proof replaces `Y` by `Y ×_S X`
and thereby reduces to the case `S = X`. Only that reduced form is stated here:

- `AlgebraicGeometry.exists_admissibleBlowup_extend_partialSection`: let `X` be a qcqs
  scheme, `U ≤ V` quasi-compact opens of `X` with `U` dense, and `p : Y ⟶ X` a separated
  quasi-compact morphism locally of finite type with `Y` qcqs. A section `f` of `p` over
  `U` whose image is closed in `p⁻¹(V)` extends, after a `V`-admissible blow-up of `X`,
  to a section of `p` over an open `W` of the blow-up containing the preimage of `U`, and
  the graph of the extension is closed in `Y ×_X X'`
  (blueprint: `thm:nagata-conrad-elimination`, in the form reduced to the base `X`);
- `AlgebraicGeometry.exists_admissibleBlowup_extend_section`: **Conrad's Remark 2.5**, the
  case `V = U`. Here the closed-image hypothesis is automatic: `f` is then a section of
  the separated morphism `p ∣_ U`, hence a closed immersion
  (blueprint: `lemma:nagata-conrad-morphism-is-quasi-domination`).

The first statement is the single remaining primitive obligation of the modification
layer of the Nagata compactification proof: it is what
`AlgebraicGeometry.exists_admissibleBlowup_isOpenImmersion_strictTransformMap` (Tag 081S)
in `WeilConjectures.Compactification.Modification` is deduced from.

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- **Conrad's Theorem 2.4, reduced to the base `X`**: let `X` be a quasi-compact
quasi-separated scheme, let `U ≤ V` be quasi-compact opens of `X` with `U` dense in `X`,
and let `p : Y ⟶ X` be a separated quasi-compact morphism, locally of finite type, from a
qcqs scheme `Y`. Let `f : U ⟶ Y` be a section of `p` over `U` whose image is closed in
`p⁻¹(V)`.

Then there is a `V`-admissible blow-up `X' = Bl_I(X) ⟶ X`, an open `W ⊆ X'` containing the
preimage of `U`, and a section `g : W ⟶ Y` of `p` over `W` extending `f`, whose graph
`W ⟶ Y ×_X X'` has closed image.

Conrad's Theorem 2.4 is stated for a rational map over an auxiliary base `S`; the first
step of his proof replaces `Y` by `Y ×_S X`, which is the reduction to the form stated
here.

In the vocabulary of the blueprint the hypothesis says that `(U, f)` is a
quasi-domination of `V` over `Y`, and the conclusion that `(W, g)` is a
quasi-domination of the blow-up over `Y` extending `f`.

This is the one primitive obligation of the modification layer of the Nagata
compactification proof: elimination of indeterminacy (Stacks Project Tag 081S,
`AlgebraicGeometry.exists_admissibleBlowup_isOpenImmersion_strictTransformMap`) is
deduced from it.
(Blueprint: `thm:nagata-conrad-elimination`, in the form reduced to the base `X`;
`def:nagata-conrad-quasi-domination`.) -/
theorem exists_admissibleBlowup_extend_partialSection
    [CompactSpace X] [QuasiSeparatedSpace X] {U V : X.Opens} (hUV : U ≤ V)
    (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X))
    (hUdense : Dense (U : Set X))
    {Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y] {p : Y ⟶ X}
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    (f : U.toScheme ⟶ Y) (hf : f ≫ p = U.ι)
    (hfc : IsClosed ((p ⁻¹ᵁ V).ι ⁻¹' Set.range f)) :
    ∃ (B : IsAdmissible X V) (W : B.I.blowup.Opens) (hUW : B.I.blowupMap ⁻¹ᵁ U ≤ W)
      (g : W.toScheme ⟶ Y) (hg : g ≫ p = W.ι ≫ B.I.blowupMap),
      B.I.blowup.homOfLE hUW ≫ g = (B.I.blowupMap ∣_ U) ≫ f ∧
        IsClosed (Set.range (pullback.lift g W.ι hg)) := by
  /- This `sorry` is discharged by issue 292, from the case lemmas of issues 287, 290
  and 291 in `WeilConjectures.Blowup.EliminationOfIndeterminacy`: issue 287 supplies
  Conrad's Case 1 (the quasi-affine, in fact affine-space, target), issues 290 and 291
  the reduction of a general target to that case via Zariski's Main Theorem and Stacks
  Project Tag 04II, and issue 292 assembles them into the statement above. -/
  sorry

/-- **Conrad's Remark 2.5**: the case `V = U` of
`AlgebraicGeometry.exists_admissibleBlowup_extend_partialSection`. A section of `p` over a
dense quasi-compact open `U` of a qcqs scheme `X` extends, after a `U`-admissible blow-up,
to a section over an open `W` of the blow-up containing the preimage of `U`, with closed
graph.

No closedness hypothesis is needed: over `U` the morphism `f` is a section of the
separated morphism `p ∣_ U`, hence a closed immersion, so its image is closed in
`p⁻¹(U)`.
(Blueprint: `thm:nagata-conrad-elimination` with `V = U`, together with
`lemma:nagata-conrad-morphism-is-quasi-domination`.) -/
theorem exists_admissibleBlowup_extend_section
    [CompactSpace X] [QuasiSeparatedSpace X] {U : X.Opens}
    (hU : IsCompact (U : Set X)) (hUdense : Dense (U : Set X))
    {Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y] {p : Y ⟶ X}
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    (f : U.toScheme ⟶ Y) (hf : f ≫ p = U.ι) :
    ∃ (B : IsAdmissible X U) (W : B.I.blowup.Opens) (hUW : B.I.blowupMap ⁻¹ᵁ U ≤ W)
      (g : W.toScheme ⟶ Y) (hg : g ≫ p = W.ι ≫ B.I.blowupMap),
      B.I.blowup.homOfLE hUW ≫ g = (B.I.blowupMap ∣_ U) ≫ f ∧
        IsClosed (Set.range (pullback.lift g W.ι hg)) := by
  refine exists_admissibleBlowup_extend_partialSection le_rfl hU hU hUdense f hf ?_
  -- `f` factors through the open `p ⁻¹ᵁ U`, since `p ∘ f` is the inclusion of `U`
  have hrange : Set.range f ⊆ Set.range (p ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨u, rfl⟩
    change p (f u) ∈ U
    rw [← Scheme.Hom.comp_apply, hf]
    exact u.2
  set f₀ : U.toScheme ⟶ (p ⁻¹ᵁ U).toScheme := IsOpenImmersion.lift (p ⁻¹ᵁ U).ι f hrange
  have hf₀ : f₀ ≫ (p ⁻¹ᵁ U).ι = f := IsOpenImmersion.lift_fac _ _ _
  -- `f₀` is a section of the separated morphism `p ∣_ U`, hence a closed immersion
  have hsec : f₀ ≫ (p ∣_ U) = 𝟙 U.toScheme := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hf₀, hf,
      Category.id_comp]
  have : IsClosedImmersion (f₀ ≫ (p ∣_ U)) := by rw [hsec]; infer_instance
  have : IsClosedImmersion f₀ := IsClosedImmersion.of_comp f₀ (p ∣_ U)
  have hcl : IsClosed (Set.range f₀) := f₀.isClosedEmbedding.isClosed_range
  have himg : (p ⁻¹ᵁ U).ι ⁻¹' Set.range f = Set.range f₀ := by
    rw [← hf₀, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.preimage_image_eq _ (p ⁻¹ᵁ U).ι.isOpenEmbedding.injective]
  rw [himg]
  exact hcl

end AlgebraicGeometry
