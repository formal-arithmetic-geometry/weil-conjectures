/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Sheaf.CategoryTheory.Sites.TorsorExtensionPresentation
import Sheaf.CategoryTheory.Sites.ContractedProductPresentation
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Pushout of the canonical étale torsor extension

Source: Stacks Project, Cohomology on Sites, Lemma 03AJ, and the blueprint's pushout-fibre
argument (blueprint: lem-sc-etale-torsor-pushout-extension).
-/

universe uP wP

open CategoryTheory CategoryTheory.Limits Opposite

-- Use the site itself as a small model in the larger coefficient universe.
attribute [local instance] CategoryTheory.essentiallySmallSelf
attribute [local instance 2000]
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

attribute [local instance 2000] CategoryTheory.sheafIsAbelian
  CategoryTheory.Abelian.hasPushouts

namespace CategoryTheory.Sheaf.Torsor

/-- Pushing out the canonical extension of `T` along `φ` gives the canonical extension of
`T ∧ᴳ G'`; its fibre over the constant `1` is that contracted product, canonically.
Source: Stacks, Tag 03AJ; blueprint pushout-fibre argument.

Proof: (0) The canonical extension `0 → G → E → ℤ → 0` is short exact (`lem-sc-torsor-h1`,
Stacks 03AJ): over a cover on which `T` has a section `t₀`, `E` is `G ⊕ ℤ` through
`i(g) + n·generator(t₀) ↦ (g, n)`, and local nonemptiness of `T` makes the augmentation
an epimorphism. (1) Apply `lem-weil-pbc-pushout-short-exact-sequence` in the abelian category of
étale abelian sheaves. The categorical pushout is the cokernel of `(φ, -inclusion)` into
`G' ⊕ E`, and gives the unique projection, exactness, and a morphism of short exact sequences.
(2) The map `(t, h) ↦ inl(h) + inr(generator(t))` is invariant under
`(t, h) ↦ (g +ᵥ t, h - φ(g))` and is `G'`-equivariant. It descends through the sheaf quotient.
The fibre is locally nonempty because `T` is, and exactness makes translation simply
transitive; thus this map is an isomorphism of torsors. These are the constructions of
`lem-sc-torsor-h1` and `def-sc-gm-torsor`.
(3) The universal property of the canonical extension of the contracted product extends
that fibre map to a morphism of extensions. It is the identity on `G'` and on the constant
integer sheaf, so the five lemma makes it an isomorphism. This is precisely the canonical
extension construction of `lem-sc-torsor-h1`.
(blueprint: lem-sc-etale-torsor-pushout-extension) -/
theorem etale_pushout_extension (S : AlgebraicGeometry.Scheme.{uP})
    {G G' : Sheaf S.smallEtaleTopology AddCommGrpCat.{max uP wP + 1}} (φ : G ⟶ G')
    (T : Torsor G) (E : ExtensionPresentation.{uP, wP} S T)
    (T' : Torsor G') (q : ContractedProductPresentation.{uP, wP} S φ T T')
    (E' : ExtensionPresentation.{uP, wP} S T') :
    ∃ σ' : pushout φ E.inclusion ⟶
        (constantSheaf S.smallEtaleTopology AddCommGrpCat.{max uP wP + 1}).obj
          (AddCommGrpCat.of (ULift.{max uP wP + 1} ℤ)),
      (pushout.inr φ E.inclusion ≫ σ' = E.projection ∧
        pushout.inl φ E.inclusion ≫ σ' = 0) ∧
      (∀ τ : pushout φ E.inclusion ⟶
          (constantSheaf S.smallEtaleTopology AddCommGrpCat.{max uP wP + 1}).obj
            (AddCommGrpCat.of (ULift.{max uP wP + 1} ℤ)),
        pushout.inr φ E.inclusion ≫ τ = E.projection →
          pushout.inl φ E.inclusion ≫ τ = 0 → τ = σ') ∧
      ∃ hz : pushout.inl φ E.inclusion ≫ σ' = 0,
        (ShortComplex.mk (pushout.inl φ E.inclusion) σ' hz).ShortExact ∧
        (φ ≫ pushout.inl φ E.inclusion = E.inclusion ≫ pushout.inr φ E.inclusion) ∧
        ∃ (a : ∀ U : S.Etaleᵒᵖ, T'.sheaf.obj.obj U → (pushout φ E.inclusion).obj.obj U),
          (∀ ⦃U V : S.Etaleᵒᵖ⦄ (f : U ⟶ V) (t : T'.sheaf.obj.obj U),
            (pushout φ E.inclusion).obj.map f (a U t) = a V (T'.sheaf.obj.map f t)) ∧
          (∀ U : S.Etaleᵒᵖ, Set.BijOn (a U) Set.univ
            {x | σ'.hom.app U x = (toSheafify S.smallEtaleTopology
              ((Functor.const S.Etaleᵒᵖ).obj
                (AddCommGrpCat.of (ULift.{max uP wP + 1} ℤ)))).app U ⟨1⟩}) ∧
          (∀ (U : S.Etaleᵒᵖ) (h : G'.obj.obj U) (t : T'.sheaf.obj.obj U),
            a U (T'.vadd U h t) = a U t + (pushout.inl φ E.inclusion).hom.app U h) ∧
          (∀ (U : S.Etaleᵒᵖ) (t : T.sheaf.obj.obj U) (h : G'.obj.obj U),
            a U (q.quotient U t h) = (pushout.inl φ E.inclusion).hom.app U h +
              (pushout.inr φ E.inclusion).hom.app U (E.generator U t)) ∧
          ∃ e : E'.middle ≅ pushout φ E.inclusion,
            E'.inclusion ≫ e.hom = pushout.inl φ E.inclusion ∧
            e.hom ≫ σ' = E'.projection ∧
            ∀ (U : S.Etaleᵒᵖ) (t : T'.sheaf.obj.obj U),
              e.hom.hom.app U (E'.generator U t) = a U t := sorry

end CategoryTheory.Sheaf.Torsor
