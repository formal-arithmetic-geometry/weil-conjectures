/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.Paper.RealizationCompletedPullData
import Sheaf.Paper.RealizationPullOrdinarySystem
import Sheaf.Paper.RealizationPullRationalDescent

/-! # Proof of the completion-unit-normalized scalar pullback comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj TensorProduct
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
namespace WeilConjectures

section CompletionCoherence

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {l : ℕ} [Fact l.Prime] {E : Type u} [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {k : Type u} [Field k]
variable {scalar : ∀ T : RealizationPullScheme l k, RealizationScalarFunctorData l E T.scheme}

private def unitIso (s : RealizationPullOrdinarySystem scalar)
    {T U : RealizationPullScheme l k} (h : RealizationPullHom T U) :
    ObjectProperty.ι (PbcIsBoundedConstructibleComplete U.scheme (pbcIntegralDatum l E)) ⋙
      pbcActualDerivedPull h.left (pbcIntegralDatum l E) ≅
    ObjectProperty.ι (PbcIsBoundedConstructibleComplete U.scheme (pbcIntegralDatum l E)) ⋙
      pbcActualStrictCompletedPull (pbcIntegralDatum l E) h.left := by
  let γ := Functor.whiskerLeft
    (ObjectProperty.ι (PbcIsBoundedConstructibleComplete U.scheme (pbcIntegralDatum l E)))
    (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) h.left)
  have : ∀ K, IsIso (γ.app K) := (s.arrow h).unit_isIso
  have : IsIso γ := NatIso.isIso_of_isIso_app γ
  exact asIso γ

private def iteratedUnit (s : RealizationPullOrdinarySystem scalar)
    {T U V : RealizationPullScheme l k}
    (h : RealizationPullHom T U) (j : RealizationPullHom U V) :
    ((ObjectProperty.ι (PbcIsBoundedConstructibleComplete V.scheme (pbcIntegralDatum l E)) ⋙
      pbcActualDerivedPull j.left (pbcIntegralDatum l E)) ⋙
      pbcActualDerivedPull h.left (pbcIntegralDatum l E)) ≅
    ((ObjectProperty.ι (PbcIsBoundedConstructibleComplete V.scheme (pbcIntegralDatum l E)) ⋙
      pbcActualStrictCompletedPull (pbcIntegralDatum l E) j.left) ⋙
      pbcActualStrictCompletedPull (pbcIntegralDatum l E) h.left) :=
  Functor.isoWhiskerRight (unitIso s j) (pbcActualDerivedPull h.left (pbcIntegralDatum l E)) ≪≫
    Functor.isoWhiskerLeft (s.arrow j).integralCompleted (unitIso s h)

private def completedComp (s : RealizationPullOrdinarySystem scalar)
    {T U V : RealizationPullScheme l k}
    (h : RealizationPullHom T U) (j : RealizationPullHom U V) :
    ((ObjectProperty.ι (PbcIsBoundedConstructibleComplete V.scheme (pbcIntegralDatum l E)) ⋙
      pbcActualStrictCompletedPull (pbcIntegralDatum l E) j.left) ⋙
      pbcActualStrictCompletedPull (pbcIntegralDatum l E) h.left) ≅
    ObjectProperty.ι (PbcIsBoundedConstructibleComplete V.scheme (pbcIntegralDatum l E)) ⋙
      pbcActualStrictCompletedPull (pbcIntegralDatum l E) (h ≫ j).left :=
  (iteratedUnit s h j).symm ≪≫
    Functor.isoWhiskerLeft
      (ObjectProperty.ι (PbcIsBoundedConstructibleComplete V.scheme (pbcIntegralDatum l E)))
      (pbcActualDerivedPullCompIso h.left j.left (pbcIntegralDatum l E)).symm ≪≫
    unitIso s (h ≫ j)

private theorem completedComp_normalization (s : RealizationPullOrdinarySystem scalar) :
    realizationPullLawCompletedCompNormalization (completedComp s) := by
  intro T U V h j K
  rw [← Category.assoc]
  change (iteratedUnit s h j).hom.app K ≫ (completedComp s h j).hom.app K = _
  simp only [completedComp, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Iso.hom_inv_id_app_assoc, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  rfl

private theorem completedComp_unique (s : RealizationPullOrdinarySystem scalar) :
    realizationPullLawCompletedCompUnique (completedComp s) := by
  intro T U V h j K q hq
  apply Iso.ext
  apply (cancel_epi ((iteratedUnit s h j).hom.app K)).mp
  have he := hq.trans (completedComp_normalization s h j K).symm
  rw [← Category.assoc, ← Category.assoc] at he
  exact he

private theorem alpha_comp (s : RealizationPullOrdinarySystem scalar) :
    realizationPullLawAlphaComp scalar s.arrow s.rationalComp (completedComp s) := by
  intro T U V h j K
  let F := pbcDerivedExtend (realizationPullScalarMap l E (scalar T))
  let P := pbcActualDerivedPull h.left (pbcIntegralDatum l E)
  let γj := (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) j.left).app K.obj
  let γh := (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) h.left).app
    ((pbcActualStrictCompletedPull (pbcIntegralDatum l E) j.left).obj K.obj)
  let N := (iteratedUnit s h j).hom.app K
  apply (cancel_epi (F.map N)).mp
  have hn := completedComp_normalization s h j K
  rw [← Category.assoc] at hn
  change N ≫ (completedComp s h j).hom.app K = _ at hn
  erw [← Category.assoc, ← F.map_comp, hn,
    F.map_comp, Category.assoc, (s.arrow (h ≫ j)).alpha_normalization]
  change _ = F.map N ≫ _
  change _ = F.map (P.map γj ≫ γh) ≫ _
  erw [F.map_comp, Category.assoc, ← Category.assoc (F.map γh),
    (s.arrow h).alpha_normalization ((s.arrow j).integralCompleted.obj K)]
  have natural := (s.arrow h).ordinaryComparison.hom.naturality γj
  change F.map (P.map γj) ≫ _ = _ at natural
  erw [← Category.assoc (F.map (P.map γj)), natural]
  simp only [Functor.comp_map, Category.assoc]
  change _ = _ ≫ (s.arrow h).continuousPull.map
    ((pbcDerivedExtend (realizationPullScalarMap l E (scalar U))).map γj) ≫ _
  rw [← Category.assoc ((s.arrow h).continuousPull.map _), ← Functor.map_comp]
  erw [(s.arrow j).alpha_normalization K]
  exact s.ordinary_comp h j K.obj

private theorem alpha_id (s : RealizationPullOrdinarySystem scalar) :
    realizationPullLawAlphaId scalar s.arrow s.continuousId := by
  intro T K
  erw [← Category.assoc,
    (s.arrow (𝟙 (Over.mk (T.scheme ↘ Spec (CommRingCat.of k))))).alpha_normalization K]
  exact s.ordinary_id T K.obj

end CompletionCoherence

/-- Completion-unit-normalized scalar comparison for every morphism over k.
Source: Bhatt--Scholze, Proposition 6.6.11, Lemma 6.8.2 and Remark 6.8.15.
(blueprint: lem-weil-pbc-realization-completed-pull)

Proof:
1. Apply lem-weil-pbc-profinite-coefficient-inverse-image to the finite quotient tower.
Its finite-projection equations identify its map with completedCoefficientMap. Under
continuous integral coordinates, reduction commutes with precomposition, so the map
is precomposition. Continuous coefficient pullback composition supplies coherence.
2. Apply lem-weil-pbc-integral-stratified-perfect-characterization. Pull back each finite
stratum by a fiber product and each trivializing cover by base change. The same perfect
finite-projective complex supplies the local model. Weakly etale and fpqc base-change
stability and the canonical tensor and composition comparisons give every integral
condition, including the uniform reduction bounds and compatible etale origins.
3. Lem-weil-pbc-reduction-pullback-derived-tower identifies the pulled strict quotient
augmentation with that of ordinary pullback. Naturality of the constant-tower adjunction
unit identifies the actual strict completion units, not just their projections. Apply
lem-weil-pbc-intrinsic-to-tower-complete to the ordinary integral pullback from step 2.
4. Use lem-weil-pbc-localization-inverse-image-coherence, with the actual coefficient
map. It identifies continuous rational coefficients with localization, preserves units
and sends each sheaf-local fraction to its pulled numerator with the same denominator.
The normalized module comparison descends on unbounded complexes; its representative
equation is derived_normalization. This gives ordinaryComparison for the scalar functor.
5. Define alpha by ordinaryComparison after F of the inverse strict completion unit.
Its normalization equation is the same formula multiplied by F of that unit. The
module-unit equation gives the localization-unit normalization and fraction formula.
6. Define completedComp by the normalization displayed in the node. Its precomposed
factors are invertible by step 3, giving existence and uniqueness. Their naturality
makes the comparison natural. The identity is the inverse unit followed by the ordinary
identity comparison; it is retained by the equivalent alpha_id equation.
7. Precompose the alpha composition equation with F of the two invertible units.
Naturality moves the inner unit across ordinaryComparison; inverse factors cancel.
The remaining equation is the ordinary localization composition equation. Cancel the
precomposition. The identity calculation is identical with one unit.
8. Prop-weil-pbc-rational-transport extends the actual A-linear restrictions and their
natural transformations to raw rationalizations. Tensoring a Hom with E preserves its
numerator and denominator. Scalar-functor fractions give the displayed rationalAlpha
normalization; identity, composition and unit equations persist by functoriality and
uniqueness of the extension. Objects are unchanged; no idempotent completion is taken. -/
theorem realization_completed_pull (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)] :
    RealizationCompletedPullData l E k := by
  classical
  let scalar : ∀ T : RealizationPullScheme l k, RealizationScalarFunctorData l E T.scheme :=
    fun T ↦ Classical.choice (realization_scalar_functor l E T.scheme k)
  obtain ⟨s⟩ := realizationPullOrdinarySystem scalar
  obtain ⟨a, ha, hf, u, hu, c, hc, i, hi, hac, hai⟩ :=
    realizationPullRationalDescent s.arrow (completedComp s) s.rationalComp s.continuousId
      (alpha_comp s) (alpha_id s)
  exact ⟨scalar, s.arrow, a, ha, s.coefficient_comp, s.rationalComp,
    s.rationalComp_canonical, completedComp s, completedComp_normalization s,
    completedComp_unique s, alpha_comp s, s.moduleId, s.moduleId_unit,
    s.continuousId, s.continuousId_normalization, alpha_id s, hf,
    u, hu, c, hc, i, hi, hac, hai⟩

end WeilConjectures
