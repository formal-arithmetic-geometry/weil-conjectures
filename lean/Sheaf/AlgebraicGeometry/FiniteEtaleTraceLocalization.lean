/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FiniteEtaleTraceLocalSums
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.Paper.FiniteEtaleEtaleLocalSplit

/-!
# Local sum characterization of finite étale traces

Source: Stacks Project, Section 03SH, paragraph after Definition 03SE;
SGA 4, Exposé IX, 5.1.
(blueprint: lem-weil-pbc-finite-etale-trace-localization)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Local sum characterizations identify two trace morphisms under étale localization.
No compatibility between the choices of the two morphisms is assumed.
Source: Stacks Project, Section 03SH, after Definition 03SE, localization property;
SGA 4, Exposé IX, 5.1.
(blueprint: lem-weil-pbc-finite-etale-trace-localization)

Proof. Work at `W` over `X'`. A splitting cover of `W` for the finite étale pullback
of `f` exists by Stacks 04HN and covering base change. The canonical pasting
isomorphism identifies its pullback with the pullback used for `f` on the same
objects regarded as objects of `X.Etale`. Its two projection identities identify
the sections of each splitting: compose a section with the pasting isomorphism,
and its projections are the identity and the same map to `Y`. Conversely use the
inverse isomorphism to transport a splitting in the other direction.

The natural restriction isomorphism `g⁻¹ F ≅ F|_X'` commutes with the restriction
along every such section. The two local sum hypotheses therefore make the two sides
of the desired identity the same finite sum on each member of the splitting cover.
Naturality of the sheaf morphisms and of the restriction isomorphism shows that these
are the restrictions of the displayed maps at `W`, including their input restricted
to the pulled-back object. For each input section, separatedness of `F|_X'` implies
equality of their images at `W`. Extensionality of additive group homomorphisms gives
the asserted equality. Empty splitting covers and empty objects are covered by the
empty-cover sheaf condition. The proof only uses the two projection identities for
`κ`, so it applies to every isomorphism specified in the statement. -/
theorem finiteEtaleTrace_localization_of_localSums
    {X Y X' : Scheme.{u}} (f : Y ⟶ X) (hfin : IsFinite f) (hf : Etale f)
    (g : X' ⟶ X) (hg : Etale g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    let A := AddCommGrpCat.{u + 1}
    let B := fun {S Z : Scheme.{u}} (q : Z ⟶ S) (hq : Etale q) (W : S.Etale) ↦
      (MorphismProperty.Over.map ⊤ hq).obj
        ((MorphismProperty.Over.pullback @Etale ⊤ q).obj W)
    letI := hfin
    letI := hf
    let f' := pullback.snd f g
    let hf' : Etale f' := inferInstance
    let F' := (upperStar A g).obj F
    ∀ (τ : (lowerStar A f).obj ((upperStar A f).obj F) ⟶ F)
      (τ' : (lowerStar A f').obj ((upperStar A f').obj F') ⟶ F'),
      FiniteEtaleTraceLocalSums f hf F τ → FiniteEtaleTraceLocalSums f' hf' F' τ' →
      ∀ (W : X'.Etale)
        (κ : (MorphismProperty.Over.map ⊤ hg).obj (B f' hf' W) ≅
          B f hf ((MorphismProperty.Over.map ⊤ hg).obj W)),
        κ.hom.left ≫ pullback.fst (W.hom ≫ g) f = pullback.fst W.hom f' →
        κ.hom.left ≫ pullback.snd (W.hom ≫ g) f =
          pullback.snd W.hom f' ≫ pullback.fst f g →
        (((upperStarIsoLocalizationRestriction A f' hf').app F').inv.hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤ f').obj W))) ≫
          τ'.hom.app (op W) ≫
          ((upperStarIsoLocalizationRestriction A g hg).app F).hom.hom.app (op W) =
        ((upperStarIsoLocalizationRestriction A g hg).app F).hom.hom.app
            (op (B f' hf' W)) ≫ F.obj.map κ.inv.op ≫
          (((upperStarIsoLocalizationRestriction A f hf).app F).inv.hom.app
            (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj
              ((MorphismProperty.Over.map ⊤ hg).obj W)))) ≫
            τ.hom.app (op ((MorphismProperty.Over.map ⊤ hg).obj W)) := by sorry

end AlgebraicGeometry.Etale
