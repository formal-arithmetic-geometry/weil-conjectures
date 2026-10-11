/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Descent of morphisms along an fpqc covering

Source: Stacks Project, Descent, Lemma Tag 02W0 (blueprint: lem-galois-fpqc-morphisms-descend).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

namespace Scheme

variable {S X U W : Scheme.{u}}

/-- The canonical comparison isomorphism `pr₀^*(U ×ₛ X) ≅ pr₁^*(U ×ₛ X)` over `X ×ₛ X`:
the composite of the canonical isomorphisms of both sides with `U ×ₛ (X ×ₛ X)`, which exist
since `pr₀ ≫ f = pr₁ ≫ f`.
Source: Stacks Project, Descent, Definition Tag 023V
(blueprint: lem-galois-fpqc-morphisms-descend). -/
noncomputable def canonicalDescentIso (pU : U ⟶ S) (f : X ⟶ S) :
    pullback (pullback.snd pU f) (pullback.fst f f) ≅
      pullback (pullback.snd pU f) (pullback.snd f f) :=
  pullbackLeftPullbackSndIso pU f (pullback.fst f f) ≪≫
    pullback.congrHom rfl pullback.condition ≪≫
    (pullbackLeftPullbackSndIso pU f (pullback.snd f f)).symm

/-- The morphism induced on fibre products by a morphism over `S`.
Source: Stacks Project, Descent, Definition Tag 023V
(blueprint: lem-galois-fpqc-morphisms-descend). -/
noncomputable def baseChangeMap (pU : U ⟶ S) (pW : W ⟶ S) (f : X ⟶ S)
    (α : U ⟶ W) (hα : pU = α ≫ pW) :
    pullback pU f ⟶ pullback pW f :=
  pullback.map pU f pW f α (𝟙 X) (𝟙 S) hα (by simp)

/-- The base change of an `S`-morphism is a morphism of descent data.
Source: Stacks Project, Descent, Definition Tag 023V
(blueprint: lem-galois-fpqc-morphisms-descend). -/
theorem baseChangeMap_compatible (pU : U ⟶ S) (pW : W ⟶ S) (f : X ⟶ S)
    (α : U ⟶ W) (hα : pU = α ≫ pW) :
    ∃ hβ : (baseChangeMap pU pW f α hα) ≫ pullback.snd pW f = pullback.snd pU f,
      pullback.map (pullback.snd pU f) (pullback.fst f f)
            (pullback.snd pW f) (pullback.fst f f)
            (baseChangeMap pU pW f α hα) (𝟙 _) (𝟙 _) (by simp [baseChangeMap]) (by simp) ≫
          (canonicalDescentIso pW f).hom =
        (canonicalDescentIso pU f).hom ≫
        pullback.map (pullback.snd pU f) (pullback.snd f f)
            (pullback.snd pW f) (pullback.snd f f)
            (baseChangeMap pU pW f α hα) (𝟙 _) (𝟙 _) (by simpa using hβ.symm) (by simp) := by
  sorry

/-- Morphisms of schemes over `S` descend uniquely along an fpqc singleton.
Source: Stacks Project, Descent, Lemma Tag 02W0 (blueprint: lem-galois-fpqc-morphisms-descend).

The proof pulls back the fpqc covering to `U`, translates the compatibility equation to
equality on the double overlap, applies fpqc representable descent, verifies the descended
morphism is over `S`, and proves reconstruction and uniqueness by the pullback universal
property. -/
theorem fpqc_morphisms_descend (f : X ⟶ S)
    (hfpqc : Presieve.singleton f ∈ Scheme.fpqcPrecoverage S)
    (pU : U ⟶ S) (pW : W ⟶ S) :
    Function.Bijective
      (fun (α : {α : U ⟶ W // α ≫ pW = pU}) =>
        ⟨baseChangeMap pU pW f α α.property.symm,
          baseChangeMap_compatible pU pW f α α.property.symm⟩ :
        {α : U ⟶ W // α ≫ pW = pU} →
          {β : pullback pU f ⟶ pullback pW f //
            ∃ hβ : β ≫ pullback.snd pW f = pullback.snd pU f,
              pullback.map (pullback.snd pU f) (pullback.fst f f)
                    (pullback.snd pW f) (pullback.fst f f) β (𝟙 _) (𝟙 _)
                    (by simpa using hβ.symm) (by simp) ≫
                  (canonicalDescentIso pW f).hom =
                (canonicalDescentIso pU f).hom ≫
                pullback.map (pullback.snd pU f) (pullback.snd f f)
                    (pullback.snd pW f) (pullback.snd f f) β (𝟙 _) (𝟙 _)
                    (by simpa using hβ.symm) (by simp)}) := by
  sorry

end Scheme

end AlgebraicGeometry
