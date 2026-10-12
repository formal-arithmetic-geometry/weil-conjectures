/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FiniteEtaleTraceLocalSums

/-!
# Transport of the local trace section formula

The algebraic and pullback-pasting step of trace compatibility with localization.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The transported trace section satisfies the local sum formula on every split
object over `W`. This lemma concerns only the trace on `X`; no trace on `X'` is used.
Source: Stacks Project, Section 03SH, paragraph after Definition 03SE;
SGA 4, Exposé IX, 5.1.
(blueprint: lem-weil-pbc-finite-etale-trace-localization-section-formula)

Proof. Write `rho` for the restriction isomorphism for `g`. Naturality of `rho`
and the trace on `X` identifies the restriction of the displayed section to `T`
with the trace applied to the input restricted to `T`, transported through the
pasting isomorphism for `T`. Construct that isomorphism by the pullback universal
property. Its projections, and the two specified projections of the isomorphism
at `W`, imply compatibility with the pullback maps induced by `h`.

Transport the given splitting of `T ×_X' Y'` along the pasting isomorphism.
Compose each inclusion with its hom and retain the same inverse map from `T`.
Isomorphisms preserve the colimit cofan, open and closed immersions. The first
projection identity preserves both inverse equations, so this is a splitting of
`T ×_X Y`. Apply the local sum predicate for the trace on `X` to this splitting.
Naturality of `rho` along each section identifies its summands, after transport
back by `rho.inv`, with the summands displayed here. Additive homomorphisms
preserve finite sums. The second projection identity ensures that the sections
are morphisms over `X`. This proves the formula, with an empty index type giving
zero on both sides; no existence of a splitting cover or separatedness is needed. -/
theorem finiteEtaleTrace_localization_section_formula
    {X Y X' : Scheme.{u}} (f : Y ⟶ X) (hf : Etale f)
    (g : X' ⟶ X) (hg : Etale g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    let A := AddCommGrpCat.{u + 1}
    let B := fun {S Z : Scheme.{u}} (q : Z ⟶ S) (hq : Etale q) (W : S.Etale) ↦
      (MorphismProperty.Over.map ⊤ hq).obj
        ((MorphismProperty.Over.pullback @Etale ⊤ q).obj W)
    letI := hf
    let f' := pullback.snd f g
    let hf' : Etale f' := inferInstance
    let F' := (upperStar A g).obj F
    ∀ (τ : (lowerStar A f).obj ((upperStar A f).obj F) ⟶ F),
      FiniteEtaleTraceLocalSums f hf F τ →
      ∀ (W : X'.Etale)
        (κ : (MorphismProperty.Over.map ⊤ hg).obj (B f' hf' W) ≅
          B f hf ((MorphismProperty.Over.map ⊤ hg).obj W)),
        κ.hom.left ≫ pullback.fst (W.hom ≫ g) f = pullback.fst W.hom f' →
        κ.hom.left ≫ pullback.snd (W.hom ≫ g) f =
          pullback.snd W.hom f' ≫ pullback.fst f g →
        ∀ (s : F'.obj.obj (op (B f' hf' W)))
          (T : X'.Etale) (h : T ⟶ W) (J : Type u) [Fintype J]
          (V : J → Scheme.{u}) (i : ∀ j, V j ⟶ pullback T.hom f')
          (t : ∀ j, T.left ⟶ V j)
          (_ : IsColimit (Cofan.mk (pullback T.hom f') i))
          (hinv₁ : ∀ j, t j ≫ i j ≫ pullback.fst T.hom f' = 𝟙 T.left)
          (_ : ∀ j, i j ≫ pullback.fst T.hom f' ≫ t j = 𝟙 (V j))
          (_ : ∀ j, IsOpenImmersion (i j)) (_ : ∀ j, IsClosedImmersion (i j)),
          F'.obj.map h.op
            ((((upperStarIsoLocalizationRestriction A g hg).app F).hom.hom.app
              (op (B f' hf' W)) ≫ F.obj.map κ.inv.op ≫
              (((upperStarIsoLocalizationRestriction A f hf).app F).inv.hom.app
                (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj
                  ((MorphismProperty.Over.map ⊤ hg).obj W)))) ≫
              τ.hom.app (op ((MorphismProperty.Over.map ⊤ hg).obj W)) ≫
              ((upperStarIsoLocalizationRestriction A g hg).app F).inv.hom.app (op W)) s) =
            ∑ j, F'.obj.map (MorphismProperty.Over.homMk
              (A := T) (B := B f' hf' T) (t j ≫ i j)
              (by
                change (t j ≫ i j) ≫ pullback.snd T.hom f' ≫ f' = T.hom
                rw [← pullback.condition]
                simpa [← Category.assoc] using
                  congrArg (fun k ↦ k ≫ T.hom) (hinv₁ j))).op
                    (F'.obj.map
                      ((MorphismProperty.Over.pullback @Etale ⊤ f' ⋙
                        MorphismProperty.Over.map ⊤ hf').map h).op s) := by sorry

end AlgebraicGeometry.Etale
