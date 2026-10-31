/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousRational.ContinuousRationalRealizationData
import WeilConjectures.AlgebraicGeometry.ContinuousRational.ContinuousAmbientGeometricCoherence
import WeilConjectures.AlgebraicGeometry.ContinuousRational.ContinuousIntegralScalarTower
import WeilConjectures.AlgebraicGeometry.ContinuousRational.ContinuousMixedIntegralComponent

/-! # Coherence forced by normalized tensor and completion comparisons

Source: Bhatt--Scholze, Remark 6.8.15; Stacks 0D6D, 0A0E and 0A0G
(blueprint: lem-per-rational-continuous-comparison-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.ContinuousRational

private def realizationFullyFaithful (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {X : Base.{u} l} (a : At l E X) :
    a.J.FullyFaithful where
  preimage {K L} f := (Equiv.ofBijective _ (a.fully_faithful K L)).symm f
  map_preimage f := (Equiv.ofBijective _ (a.fully_faithful _ _)).apply_symm_apply f
  preimage_map f := (Equiv.ofBijective _ (a.fully_faithful _ _)).symm_apply_apply f

private def liftComposition (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y Z : Base.{u} l} (g : X.scheme ⟶ Y.scheme) (h : Z.scheme ⟶ X.scheme)
    (aX : At l E X) (aY : At l E Y) (aZ : At l E Z)
    (ag : Along l E g aX aY) (ah : Along l E h aZ aX)
    (ac : Along l E (h ≫ g) aZ aY)
    (c : AmbientComposition l E g h aX aY aZ ag ah ac) :
    Composition l E g h aX aY aZ ag ah ac := by
  let ff := (realizationFullyFaithful l E aZ).whiskeringRight
    (PbcRationalCategory Y.scheme (pbcIntegralDatum l E) (pbcUniformizer l E))
  let e₁ := ac.comparison ≪≫ Functor.isoWhiskerLeft aY.J c.ambient
  let e₂ := Functor.isoWhiskerLeft (ag.raw l E) ah.comparison ≪≫
    Functor.isoWhiskerRight ag.comparison (derivedPull h ah.coefficient)
  let r : ac.raw l E ≅ ag.raw l E ⋙ ah.raw l E :=
    ff.preimageIso (e₁ ≪≫ e₂.symm)
  refine
    { coefficient := c.coefficient
      ordinary := c.ordinary
      ordinary_units := c.ordinary_units
      complex := c.complex
      complex_components := c.complex_components
      ambient := c.ambient
      ambient_normalization := c.ambient_normalization
      raw := r
      compatibility := ?_ }
  intro K
  have hr := congr_app (ff.map_preimage
    (X := ac.raw l E) (Y := ag.raw l E ⋙ ah.raw l E) (e₁ ≪≫ e₂.symm).hom) K
  change aZ.J.map (r.hom.app K) = (e₁ ≪≫ e₂.symm).hom.app K at hr
  change e₁.hom.app K = aZ.J.map (r.hom.app K) ≫ e₂.hom.app K
  rw [hr]
  change e₁.hom.app K = (e₁.hom.app K ≫ e₂.inv.app K) ≫ e₂.hom.app K
  rw [Category.assoc, Iso.inv_hom_id_app]
  exact (Category.comp_id (e₁.hom.app K)).symm

private def liftIdentity (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Base.{u} l) (a : At l E X) (ai : Along l E (𝟙 X.scheme) a a)
    (c : AmbientIdentity l E X a ai) : Identity l E X a ai := by
  let ff := (realizationFullyFaithful l E a).whiskeringRight
    (PbcRationalCategory X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E))
  let e := ai.comparison ≪≫ Functor.isoWhiskerLeft a.J c.ambient
  let r : ai.raw l E ≅
      𝟭 (PbcRationalCategory X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)) :=
    ff.preimageIso e
  refine
    { site := c.site
      site_normalization := c.site_normalization
      ordinary := c.ordinary
      ordinary_units := c.ordinary_units
      ambient := c.ambient
      ambient_normalization := c.ambient_normalization
      raw := r
      compatibility := ?_ }
  intro K
  exact (congr_app (ff.map_preimage (X := ai.raw l E)
    (Y := 𝟭 (PbcRationalCategory X.scheme (pbcIntegralDatum l E)
      (pbcUniformizer l E))) e.hom) K).symm

private def liftMixed (l : ℕ) [Fact l.Prime] (E F : Type u) [Field E] [Field F]
    [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
    (i : E →ₐ[ℚ_[l]] F) {X Y : Base.{u} l} (g : X.scheme ⟶ Y.scheme)
    (aXE : At l E X) (aYE : At l E Y) (aXF : At l F X) (aYF : At l F Y)
    (agE : Along l E g aXE aYE) (agF : Along l F g aXF aYF)
    (bX : FieldChange l E F i X aXE aXF) (bY : FieldChange l E F i Y aYE aYF)
    (m : AmbientMixed l E F i g aXE aYE aXF aYF agE agF bX bY) :
    Mixed l E F i g aXE aYE aXF aYF agE agF bX bY := by
  let ff := (realizationFullyFaithful l F aXF).whiskeringRight
    (PbcRationalCategory Y.scheme (pbcIntegralDatum l E) (pbcUniformizer l E))
  let e₁ := Functor.isoWhiskerLeft
      (pbcRationalScalarExtension l E F i Y.scheme Y.dimension Y.prime_unit) agF.comparison ≪≫
    Functor.isoWhiskerRight bY.comparison (derivedPull g agF.coefficient) ≪≫
      Functor.isoWhiskerLeft aYE.J m.ambient
  let e₂ := Functor.isoWhiskerLeft (agE.raw l E) bX.comparison ≪≫
    Functor.isoWhiskerRight agE.comparison (pbcDerivedExtend bX.coefficient)
  let r : pbcRationalScalarExtension l E F i Y.scheme Y.dimension Y.prime_unit ⋙
      agF.raw l F ≅ agE.raw l E ⋙
        pbcRationalScalarExtension l E F i X.scheme X.dimension X.prime_unit :=
    ff.preimageIso (e₁ ≪≫ e₂.symm)
  have hr (K) : aXF.J.map (r.hom.app K) ≫ e₂.hom.app K = e₁.hom.app K := by
    have he := congr_app (ff.map_preimage
      (X := pbcRationalScalarExtension l E F i Y.scheme Y.dimension Y.prime_unit ⋙
        agF.raw l F)
      (Y := agE.raw l E ⋙
        pbcRationalScalarExtension l E F i X.scheme X.dimension X.prime_unit)
      (e₁ ≪≫ e₂.symm).hom) K
    change aXF.J.map (r.hom.app K) = (e₁ ≪≫ e₂.symm).hom.app K at he
    rw [he]
    change (e₁.hom.app K ≫ e₂.inv.app K) ≫ e₂.hom.app K = e₁.hom.app K
    rw [Category.assoc, Iso.inv_hom_id_app]
    exact Category.comp_id (e₁.hom.app K)
  refine
    { coefficient := m.coefficient
      ordinary := m.ordinary
      ordinary_sections := m.ordinary_sections
      complex := m.complex
      complex_components := m.complex_components
      ambient := m.ambient
      ambient_normalization := m.ambient_normalization
      raw := r
      raw_normalization := ?_
      compatibility := ?_ }
  · intro K
    obtain ⟨t, ht, he⟩ := continuousMixedIntegralComponent l E F i g
      aXE aYE aXF aYF agE agF bX bY m K.obj
    have ht' : r.hom.app K = t := by
      apply (aXF.fully_faithful _ _).1
      apply (cancel_mono (e₂.hom.app K)).1
      exact (hr K).trans he.symm
    rw [ht']
    exact ht
  · intro K
    exact hr K

/-- The specified normalized pullback and scalar comparisons satisfy composition,
identity, successive scalar extension and the mixed square.
Source: Bhatt--Scholze, Remark 6.8.15; Stacks 0D6D, 0A0E and 0A0G
(blueprint: lem-per-rational-continuous-comparison-coherence).

Proof: the ambient geometric coherence theorem supplies normalized ordinary,
cochain and derived comparisons for composition and identity. Postcomposition by
the fully faithful realization is fully faithful on functor categories. Lift the
ambient comparison conjugated by the supplied Along comparisons through that
functor. Its map-preimage equation gives the required raw compatibility. For the
identity lift the composite of the supplied comparison with the ambient identity.

For scalar composition the three coefficient maps agree sectionwise, since each
is normalized by the prescribed field embedding. Every raw object has an underlying
integral representative. On that representative, continuousIntegralScalarTower
substitutes the three FieldChange integral equations, uses naturality of the
integral comparison on the published integral associator, and cancels the common
invertible comparison. Three reduction-normalization associativity equations give
the remaining diagram.

For the mixed square lift the ambient mixed isomorphism conjugated by the four
supplied comparisons, again through fully faithful postcomposition. This produces
an actual natural isomorphism and its compatibility equation. On each integral
representative, continuousMixedIntegralComponent identifies the specified published
scalar/completed-pullback arrow and proves the same realized equation. Cancel the
common invertible factor and use faithfulness to identify this arrow with the
component of the lifted natural isomorphism. Its heterogeneous normalization is
therefore the prescribed one. These constructions allow empty schemes, identity
scheme maps, repeated fields and identity coefficient embeddings. -/
theorem rationalContinuousComparisonCoherence (l : ℕ) [Fact l.Prime]
    (realization : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
      [FiniteDimensional ℚ_[l] A] (X : Base.{u} l), At l A X)
    (along : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
      {X Y : Base.{u} l} (g : X.scheme ⟶ Y.scheme),
      Along l A g (realization A X) (realization A Y))
    (fieldChange : ∀ (A B : Type u) [Field A] [Field B]
      [Algebra ℚ_[l] A] [Algebra ℚ_[l] B]
      [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
      (i : A →ₐ[ℚ_[l]] B) (X : Base.{u} l),
      FieldChange l A B i X (realization A X) (realization B X)) :
    (∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    {X Y Z : Base.{u} l} (g : X.scheme ⟶ Y.scheme) (h : Z.scheme ⟶ X.scheme),
    Nonempty (Composition l A g h (realization A X) (realization A Y) (realization A Z)
      (along A g) (along A h) (along A (h ≫ g)))) ∧
    (∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    (X : Base.{u} l), Nonempty (Identity l A X (realization A X) (along A (𝟙 X.scheme)))) ∧
    (∀ (A B C : Type u) [Field A] [Field B] [Field C]
    [Algebra ℚ_[l] A] [Algebra ℚ_[l] B] [Algebra ℚ_[l] C]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
    [FiniteDimensional ℚ_[l] C]
    (i : A →ₐ[ℚ_[l]] B) (j : B →ₐ[ℚ_[l]] C) (X : Base.{u} l),
    Nonempty (FieldComposition l A B C i j X (realization A X) (realization B X) (realization C X)
      (fieldChange A B i X) (fieldChange B C j X) (fieldChange A C (j.comp i) X))) ∧
    (∀ (A B : Type u) [Field A] [Field B] [Algebra ℚ_[l] A] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
    (i : A →ₐ[ℚ_[l]] B) {X Y : Base.{u} l} (g : X.scheme ⟶ Y.scheme),
    Nonempty (Mixed l A B i g (realization A X) (realization A Y)
      (realization B X) (realization B Y)
      (along A g) (along B g) (fieldChange A B i X) (fieldChange A B i Y))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A _ _ _ X Y Z g h
    obtain ⟨c⟩ := (continuousAmbientGeometricCoherence l A g h
      (realization A X) (realization A Y) (realization A Z)
      (along A g) (along A h) (along A (h ≫ g)) (along A (𝟙 Y.scheme))).1
    exact ⟨liftComposition l A g h (realization A X) (realization A Y) (realization A Z)
      (along A g) (along A h) (along A (h ≫ g)) c⟩
  · intro A _ _ _ X
    obtain ⟨c⟩ := (continuousAmbientGeometricCoherence l A (𝟙 X.scheme) (𝟙 X.scheme)
      (realization A X) (realization A X) (realization A X)
      (along A (𝟙 X.scheme)) (along A (𝟙 X.scheme))
      (along A (𝟙 X.scheme ≫ 𝟙 X.scheme)) (along A (𝟙 X.scheme))).2
    exact ⟨liftIdentity l A X (realization A X) (along A (𝟙 X.scheme)) c⟩
  · intro A B C _ _ _ _ _ _ _ _ _ i j X
    have hc : (fieldChange A B i X).coefficient ≫ (fieldChange B C j X).coefficient =
        (fieldChange A C (j.comp i) X).coefficient := by
      let := coefficientExtensionNormedField l C
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro s
      apply ContinuousMap.ext
      intro x
      apply ULift.ext
      change rationalCoefficientValue l C X.scheme U
          ((fieldChange B C j X).coefficient.hom.app U
            ((fieldChange A B i X).coefficient.hom.app U s)) x =
        rationalCoefficientValue l C X.scheme U
          ((fieldChange A C (j.comp i) X).coefficient.hom.app U s) x
      exact ((fieldChange B C j X).normalized U
        ((fieldChange A B i X).coefficient.hom.app U s) x).trans
          ((congrArg j ((fieldChange A B i X).normalized U s x)).trans
            ((fieldChange A C (j.comp i) X).normalized U s x).symm)
    refine ⟨{ coefficient := hc, compatibility := ?_ }⟩
    intro K
    exact continuousIntegralScalarTower l A B C i j X
      (realization A X) (realization B X) (realization C X)
      (fieldChange A B i X) (fieldChange B C j X) (fieldChange A C (j.comp i) X) hc K.obj
  · intro A B _ _ _ _ _ _ i X Y g
    obtain ⟨m⟩ := continuousAmbientMixedCoherence l A B i g
      (realization A X) (realization A Y) (realization B X) (realization B Y)
      (along A g) (along B g) (fieldChange A B i X) (fieldChange A B i Y)
    exact ⟨liftMixed l A B i g (realization A X) (realization A Y)
      (realization B X) (realization B Y) (along A g) (along B g)
      (fieldChange A B i X) (fieldChange A B i Y) m⟩

end AlgebraicGeometry.Scheme.ContinuousRational
