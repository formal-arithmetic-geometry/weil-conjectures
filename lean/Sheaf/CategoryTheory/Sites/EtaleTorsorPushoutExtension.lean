/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.CategoryTheory.Sites.TorsorExtensionPresentation
public import WeilConjectures.CategoryTheory.Sites.ContractedProductPresentation
import Sheaf.CategoryTheory.Sites.ExtensionPresentationShortExact
import Sheaf.CategoryTheory.Sites.ExtensionPresentationGeneratorFiber
import WeilConjectures.CategoryTheory.PushoutShortExactSequence

/-!
# Pushout of the canonical étale torsor extension

Source: Stacks Project, Cohomology on Sites, Lemma 03AJ, and the blueprint's pushout-fibre
argument (blueprint: lem-sc-etale-torsor-pushout-extension).
-/

@[expose] public section

universe uP wP

open CategoryTheory CategoryTheory.Limits Opposite

-- Use the site itself as a small model in the larger coefficient universe.
attribute [local instance] CategoryTheory.essentiallySmallSelf
attribute [local instance 2000]
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

attribute [local instance 2000] CategoryTheory.sheafIsAbelian
  CategoryTheory.Abelian.hasPushouts

attribute [local instance] GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall

namespace CategoryTheory.Sheaf.Torsor

private theorem presentation_hom_ext (S : AlgebraicGeometry.Scheme.{uP})
    {G : Sheaf S.smallEtaleTopology AddCommGrpCat.{max uP wP + 1}}
    {T : Torsor G} (E : ExtensionPresentation.{uP, wP} S T)
    {A : Sheaf S.smallEtaleTopology AddCommGrpCat.{max uP wP + 1}}
    (f g : E.middle ⟶ A) (hi : E.inclusion ≫ f = E.inclusion ≫ g)
    (hj : ∀ U t, f.hom.app U (E.generator U t) = g.hom.app U (E.generator U t)) : f = g := by
  obtain ⟨l, hl, hu⟩ := E.universal A (E.inclusion ≫ g)
    (fun U t ↦ g.hom.app U (E.generator U t))
    (by
      intro U V i t
      have hn := ConcreteCategory.congr_hom (g.hom.naturality i) (E.generator U t)
      simpa only [ConcreteCategory.comp_apply, E.generator_natural] using hn.symm)
    (by
      intro U h t
      rw [E.generator_vadd, map_add]
      rfl)
  exact (hu f ⟨hi, hj⟩).trans (hu g ⟨rfl, fun _ _ ↦ rfl⟩).symm

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
              e.hom.hom.app U (E'.generator U t) = a U t := by
  have hE := extension_presentation_shortExact S E
  have hE' := extension_presentation_shortExact S E'
  obtain ⟨b, hb, _⟩ := E.universal E'.middle (φ ≫ E'.inclusion)
    (fun U t ↦ E'.generator U (q.quotient U t 0))
    (by
      intro U V f t
      rw [E'.generator_natural, q.quotient_natural, map_zero])
    (by
      intro U g t
      have hq := q.quotient_invariant U g t (φ.hom.app U g)
      rw [_root_.sub_self] at hq
      rw [hq, ← zero_add (φ.hom.app U g), q.quotient_vadd, E'.generator_vadd]
      rfl)
  have hbσ : b ≫ E'.projection = E.projection := by
    apply presentation_hom_ext S E
    · rw [← Category.assoc, hb.1, Category.assoc, E'.inclusion_projection, comp_zero,
        E.inclusion_projection]
    · intro U t
      change E'.projection.hom.app U (b.hom.app U (E.generator U t)) = _
      rw [hb.2, E'.projection_generator, E.projection_generator]
  obtain ⟨σ, hz, hp, hu, hP, _⟩ :=
    (pushout_short_exact_sequence _ hE φ).2
  let c : pushout φ E.inclusion ⟶ E'.middle :=
    pushout.desc E'.inclusion b hb.1.symm
  have hcI : pushout.inl φ E.inclusion ≫ c = E'.inclusion := by simp [c]
  have hcE : pushout.inr φ E.inclusion ≫ c = b := by simp [c]
  have hcσ : c ≫ E'.projection = σ := by
    apply hu
    · rw [← Category.assoc, hcE, hbσ]
    · rw [← Category.assoc, hcI, E'.inclusion_projection]
  let m : ShortComplex.mk (pushout.inl φ E.inclusion) σ hz ⟶
      ShortComplex.mk E'.inclusion E'.projection E'.inclusion_projection :=
    { τ₁ := 𝟙 G'
      τ₂ := c
      τ₃ := 𝟙 _
      comm₁₂ := by simpa using hcI.symm
      comm₂₃ := by simpa using hcσ }
  have hm : IsIso m.τ₂ := ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ m hP hE'
  have : IsIso c := hm
  let e : E'.middle ≅ pushout φ E.inclusion := (asIso c).symm
  have heI : E'.inclusion ≫ e.hom = pushout.inl φ E.inclusion := by
    rw [← hcI, Category.assoc]
    change pushout.inl φ E.inclusion ≫ (e.inv ≫ e.hom) = _
    simp
  have heσ : e.hom ≫ σ = E'.projection := by
    rw [← hcσ, ← Category.assoc]
    change (e.hom ≫ e.inv) ≫ E'.projection = _
    simp
  refine ⟨σ, ⟨hp, hz⟩, hu, hz, hP, pushout.condition, ?_⟩
  refine ⟨fun U t ↦ e.hom.hom.app U (E'.generator U t), ?_, ?_, ?_, ?_,
    e, heI, heσ, fun _ _ ↦ rfl⟩
  · intro U V f t
    have hn := ConcreteCategory.congr_hom (e.hom.hom.naturality f) (E'.generator U t)
    simpa only [ConcreteCategory.comp_apply, E'.generator_natural] using hn.symm
  · intro U
    have hgen := extension_presentation_generator_bijOn S E' U
    have hec (x : E'.middle.obj.obj U) :
        σ.hom.app U (e.hom.hom.app U x) = E'.projection.hom.app U x :=
      congrArg (fun k ↦ k.hom.app U x) heσ
    refine ⟨fun t _ ↦ (hec _).trans (E'.projection_generator U t), ?_, ?_⟩
    · intro t ht t' ht' heq
      apply hgen.2.1 ht ht'
      exact (ConcreteCategory.bijective_of_isIso (e.hom.hom.app U)).1 heq
    · intro x hx
      obtain ⟨y, hy⟩ := (ConcreteCategory.bijective_of_isIso (e.hom.hom.app U)).2 x
      obtain ⟨t, ht⟩ := hgen.2.2 (by
        change E'.projection.hom.app U y = _
        rw [← hec, hy]
        exact hx)
      exact ⟨t, ht.1, (congrArg (fun z ↦ e.hom.hom.app U z) ht.2).trans hy⟩
  · intro U h t
    dsimp only
    rw [E'.generator_vadd, map_add]
    congr 1
    exact congrArg (fun k : G' ⟶ pushout φ E.inclusion ↦ k.hom.app U h) heI
  · intro U t h
    apply (ConcreteCategory.bijective_of_isIso (c.hom.app U)).1
    have hec (x : E'.middle.obj.obj U) : c.hom.app U (e.hom.hom.app U x) = x := by
      change (e.hom ≫ c).hom.app U x = x
      simp [e]
    rw [hec, map_add]
    have hcl := congrArg (fun k : G' ⟶ E'.middle ↦ k.hom.app U h) hcI
    have hcr := congrArg (fun k : E.middle ⟶ E'.middle ↦
      k.hom.app U (E.generator U t)) hcE
    change E'.generator U (q.quotient U t h) = _
    rw [show q.quotient U t h = T'.vadd U h (q.quotient U t 0) by
      simpa only [zero_add] using q.quotient_vadd U t 0 h, E'.generator_vadd]
    change _ = (pushout.inl φ E.inclusion ≫ c).hom.app U h +
      (pushout.inr φ E.inclusion ≫ c).hom.app U (E.generator U t)
    rw [hcI, hcE, hb.2]
    exact add_comm _ _

end CategoryTheory.Sheaf.Torsor
