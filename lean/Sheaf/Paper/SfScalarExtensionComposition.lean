/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic
public import Sheaf.Paper.ScalarExtensionComposition


/-! # Composition of intrinsic rational scalar extensions

Source: Weil conjectures blueprint, sec-smooth-purity/sk-def-sf-operations,
order 1469; current main snapshot sec-proper-base-change/sk-thm-properbasechange,
order 1828 (blueprint: lem-weil-scalar-extension-composition).

The ordinary balanced tensor associator and unit are reused from the legacy module.
Their quotient-completion normalization is transported to the current intrinsic integral
subcategory and then to its raw Hom scalar localization. No identification with the legacy
integral constructibility predicate is assumed.

## Main statements

- `sfRationalScalarComp`: canonical composition on the currently recorded rational stages.
- `sfRationalScalarUnit`: the normalized identity-extension comparison.
- `sfRationalScalar_coherence`: both unit equations and the pentagon.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory

namespace WeilConjectures

private theorem map_heq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X X' Y Y' : C} (hX : X = X') (hY : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hX
  cases hY
  cases h
  rfl

private theorem localizedIso
    {R : Type*} [CommRing R] {S : Type*} [CommRing S]
    {C : Type*} [Category C] [Preadditive C] [Linear R C]
    {D : Type*} [Category D] [Preadditive D] [Linear S D]
    (t : R) (v : S) (ψ : Localization.Away t → Localization.Away v)
    (F₀ G₀ : C ⥤ D) (e : F₀ ≅ G₀)
    (F G : ScalarLocalization R C t ⥤ ScalarLocalization S D v)
    [F.Additive] [G.Additive]
    (hF : ∀ K, F.obj K = ⟨F₀.obj K.obj⟩)
    (hG : ∀ K, G.obj K = ⟨G₀.obj K.obj⟩)
    (mF : ∀ (K K' : C) (f : K ⟶ K') (a : Localization.Away t),
      HEq (F.map (a ⊗ₜ[R] f : ScalarLocalization.mk (R := R) (p := t) K ⟶ ⟨K'⟩))
        (ψ a ⊗ₜ[S] F₀.map f : ScalarLocalization.mk (R := S) (p := v) (F₀.obj K) ⟶
          ⟨F₀.obj K'⟩))
    (mG : ∀ (K K' : C) (f : K ⟶ K') (a : Localization.Away t),
      HEq (G.map (a ⊗ₜ[R] f : ScalarLocalization.mk (R := R) (p := t) K ⟶ ⟨K'⟩))
        (ψ a ⊗ₜ[S] G₀.map f : ScalarLocalization.mk (R := S) (p := v) (G₀.obj K) ⟶
          ⟨G₀.obj K'⟩)) :
    ∃! a : F ≅ G, ∀ K, HEq (a.hom.app K)
      ((ScalarLocalization.localization S D v).map (e.hom.app K.obj)) := by
  let c (K : ScalarLocalization R C t) : F.obj K ≅ G.obj K :=
    eqToIso (hF K) ≪≫ (ScalarLocalization.localization S D v).mapIso (e.app K.obj) ≪≫
      (eqToIso (hG K)).symm
  have hc (K) : HEq (c K).hom
      ((ScalarLocalization.localization S D v).map (e.hom.app K.obj)) := by
    simp [c]
  have hn {K K' : ScalarLocalization R C t} (f : K ⟶ K') :
      F.map f ≫ (c K').hom = (c K).hom ≫ G.map f := by
    obtain ⟨K⟩ := K
    obtain ⟨K'⟩ := K'
    induction f using TensorProduct.induction_on with
    | zero => simp
    | add f g hf hg =>
      rw [F.map_add, G.map_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
    | tmul a f =>
      rw [(conj_eqToHom_iff_heq _ _ (hF ⟨K⟩) (hF ⟨K'⟩)).mpr (mF K K' f a),
        (conj_eqToHom_iff_heq _ _ (hG ⟨K⟩) (hG ⟨K'⟩)).mpr (mG K K' f a)]
      dsimp [c]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      have he : ScalarLocalization.composition S D v _ _ _
            ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K') (ψ a ⊗ₜ[S] F₀.map f) =
          ScalarLocalization.composition S D v _ _ _
            (ψ a ⊗ₜ[S] G₀.map f) ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K) := by
        simp only [ScalarLocalization.composition_tmul, one_mul, mul_one]
        rw [e.hom.naturality f]
      have he' :
          @CategoryStruct.comp (ScalarLocalization S D v) _
            ⟨F₀.obj K⟩ ⟨F₀.obj K'⟩ ⟨G₀.obj K'⟩
            (ψ a ⊗ₜ[S] F₀.map f) ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K') =
          @CategoryStruct.comp (ScalarLocalization S D v) _
            ⟨F₀.obj K⟩ ⟨G₀.obj K⟩ ⟨G₀.obj K'⟩
            ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K) (ψ a ⊗ₜ[S] G₀.map f) := he
      simpa only [ScalarLocalization.localization, Category.assoc] using
        congrArg (fun z :
          (⟨F₀.obj K⟩ : ScalarLocalization S D v) ⟶ ⟨G₀.obj K'⟩ ↦
            eqToHom (hF ⟨K⟩) ≫ z ≫ eqToHom (hG ⟨K'⟩).symm) he'
  let a : F ≅ G := NatIso.ofComponents c (fun f ↦ hn f)
  refine ⟨a, hc, ?_⟩
  intro a' ha'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact eq_of_heq ((ha' K).trans (hc K).symm)

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})

/-- The normalized ordinary-to-completed comparison on intrinsic integral objects.
Source: blueprint order 1828, proof, first paragraph
(blueprint: lem-weil-scalar-extension-composition).
Proof: the finite-free completed-scalar comparison in the DAG identifies ordinary derived
extension and completed extension on every derived-complete input. On a K-flat complex
with flat terms, its map is the quotient-completion chain map: its unshifted cone
coordinates are the finite quotient tensor maps, and its shifted coordinate is zero.
Finite freeness commutes with the products in the Roos complex; completeness and cofinality
of the two uniformizer filtrations show this very map is invertible. The intrinsic predicate
includes derived completeness, so this applies without a finite-field structure on Y.
Naturality for good complexes descends through roofs. Every object has a good resolution,
so the displayed representative characterization determines the comparison uniquely. -/
theorem sfIntegralOrdinaryComparison_existsUnique :
    ∃! c : (sfIntegralConstructible l E Y).ι ⋙ integralOrdinaryDerivedScalar l E L ι Y ≅
        (sfIntegralConstructible l E Y).ι ⋙ integralScalarExtension l E L ι Y,
      ∀ (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (hP : sfIntegralConstructible l E Y (DerivedCategory.Q.obj P.obj)),
        c.hom.app ⟨DerivedCategory.Q.obj P.obj, hP⟩ ≫
            (integralScalarExtensionComparison l E L ι Y).hom.app P =
          (integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.hom.app P.obj ≫
            DerivedCategory.Q.map ((integralScalarCompletionChain l E L ι Y).app P.obj) := by
  sorry

/-- The uniquely normalized comparison; its data is fixed by quotient maps on good complexes.
Source: blueprint order 1828 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def sfIntegralOrdinaryComparison :=
  (sfIntegralOrdinaryComparison_existsUnique l E L ι Y).exists.choose

variable (p : ℕ) (hl : l ≠ p)
  (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
  (j : L →ₐ[Padic l] M)

/-- Completed integral associativity, uniquely fixed by ordinary balanced tensor and the
normalized quotient-completion comparisons.
Source: blueprint order 1828, proof, first paragraph
(blueprint: lem-weil-scalar-extension-composition).
Proof: on a K-flat resolution, ordinary associativity sends c tensor (b tensor x) to
c*j(b) tensor x, with inverse c tensor x to c tensor (1 tensor x). These maps commute
with restrictions, differentials and chain maps, hence descend through roofs. Conjugate
this fixed ordinary associator by the three normalized ordinary-to-completed comparisons.
Completed extension preserves the intrinsic subcategories, so full faithfulness of their
inclusions lifts this isomorphism and its inverse uniquely. The displayed equation specifies
that lift, rather than choosing an unnormalized natural isomorphism. -/
theorem sfIntegralScalarComp_existsUnique :
    ∃! a : sfConstructibleIntegralScalarExtension p l hl E L ι Y ⋙
        sfConstructibleIntegralScalarExtension p l hl L M j Y ≅
        sfConstructibleIntegralScalarExtension p l hl E M (j.comp ι) Y,
      ∀ K : sfIntegralConstructibleCategory l E Y,
        (a.hom.app K).hom =
          (sfIntegralOrdinaryComparison l L M j Y).inv.app
              ((sfConstructibleIntegralScalarExtension p l hl E L ι Y).obj K) ≫
            (integralOrdinaryDerivedScalar l L M j Y).map
              ((sfIntegralOrdinaryComparison l E L ι Y).inv.app K) ≫
            (integralOrdinaryDerivedScalarComp l E L ι Y M j).hom.app K.obj ≫
            (sfIntegralOrdinaryComparison l E M (j.comp ι) Y).hom.app K := by
  let c := sfIntegralOrdinaryComparison l E L ι Y
  let d := sfIntegralOrdinaryComparison l L M j Y
  let e := sfIntegralOrdinaryComparison l E M (j.comp ι) Y
  let F := sfConstructibleIntegralScalarExtension p l hl E L ι Y
  let G := sfConstructibleIntegralScalarExtension p l hl L M j Y
  let H := sfConstructibleIntegralScalarExtension p l hl E M (j.comp ι) Y
  let A := integralOrdinaryDerivedScalar l L M j Y
  let b : (F ⋙ G) ⋙ (sfIntegralConstructible l M Y).ι ≅
      H ⋙ (sfIntegralConstructible l M Y).ι :=
    Functor.isoWhiskerLeft F d.symm ≪≫
      (Functor.associator F (sfIntegralConstructible l L Y).ι A).symm ≪≫
      Functor.isoWhiskerRight c.symm A ≪≫
      Functor.associator (sfIntegralConstructible l E Y).ι
        (integralOrdinaryDerivedScalar l E L ι Y) A ≪≫
      Functor.isoWhiskerLeft (sfIntegralConstructible l E Y).ι
        (integralOrdinaryDerivedScalarComp l E L ι Y M j) ≪≫ e
  let a : F ⋙ G ≅ H := NatIso.ofComponents
    (fun K ↦ { hom := ⟨b.hom.app K⟩, inv := ⟨b.inv.app K⟩,
               hom_inv_id := by ext; exact b.hom_inv_id_app K
               inv_hom_id := by ext; exact b.inv_hom_id_app K })
    (by intro K K' f; ext; exact b.hom.naturality f)
  refine ⟨a, ?_, ?_⟩
  · intro K
    dsimp [a, b, c, d, e, F, A]
    simp only [Category.id_comp]
  · intro a' ha'
    apply Iso.ext
    apply NatTrans.ext
    funext K
    ext
    exact (ha' K).trans (by
      dsimp [a, b, c, d, e, F, A]
      simp only [Category.id_comp])

/-- The intrinsic completed integral associator with its fixed tensor normalization.
Source: blueprint order 1828 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def sfIntegralScalarComp :=
  (sfIntegralScalarComp_existsUnique l E L ι Y p hl M j).exists.choose

/-- The completed integral identity comparison, uniquely normalized by multiplication.
Source: blueprint order 1828, proof, identity-extension clause
(blueprint: lem-weil-scalar-extension-composition).
Proof: the ordinary unit sends s tensor x to s*x, with inverse x to 1 tensor x.
Conjugating it by the identity ordinary-to-completed comparison gives the actual
completeness-unit normalization. Full faithfulness lifts it uniquely to the intrinsic
subcategory; the inverse is the lift of the inverse ambient map. -/
theorem sfIntegralScalarUnit_existsUnique :
    ∃! a : sfConstructibleIntegralScalarExtension p l hl E E (AlgHom.id (Padic l) E) Y ≅
        𝟭 (sfIntegralConstructibleCategory l E Y),
      ∀ K : sfIntegralConstructibleCategory l E Y,
        (a.hom.app K).hom =
          (sfIntegralOrdinaryComparison l E E (AlgHom.id (Padic l) E) Y).inv.app K ≫
            (integralOrdinaryDerivedScalarUnit l E Y).hom.app K.obj := by
  let b := (sfIntegralOrdinaryComparison l E E (AlgHom.id (Padic l) E) Y).symm ≪≫
    Functor.isoWhiskerLeft (sfIntegralConstructible l E Y).ι
      (integralOrdinaryDerivedScalarUnit l E Y) ≪≫
    Functor.rightUnitor (sfIntegralConstructible l E Y).ι
  let a : sfConstructibleIntegralScalarExtension p l hl E E (AlgHom.id (Padic l) E) Y ≅
      𝟭 (sfIntegralConstructibleCategory l E Y) := NatIso.ofComponents
    (fun K ↦ { hom := ⟨b.hom.app K⟩, inv := ⟨b.inv.app K⟩,
               hom_inv_id := by ext; exact b.hom_inv_id_app K
               inv_hom_id := by ext; exact b.inv_hom_id_app K })
    (by intro K K' f; ext; exact b.hom.naturality f)
  refine ⟨a, ?_, ?_⟩
  · intro K
    simp [a, b]
  · intro a' ha'
    apply Iso.ext
    apply NatTrans.ext
    funext K
    ext
    exact (ha' K).trans (by simp [a, b])

/-- The normalized intrinsic integral unit.
Source: blueprint order 1828 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def sfIntegralScalarUnit :=
  (sfIntegralScalarUnit_existsUnique l E Y p hl).exists.choose

/-- The rational associator is uniquely specified as the image of the normalized
completed integral associator on every unchanged integral object.
Source: blueprint order 1828, proof, second paragraph
(blueprint: lem-weil-scalar-extension-composition).
Proof: rationalization has the same objects, and its morphisms are generated by pure
tensors f tensor a. Tensor each component of the integral associator and its inverse
with one. Integral naturality is linear over the source integers, so multiplying it
by a and adding proves naturality for every rational morphism. The inverse equations
survive localization. The published scalar functor has precisely the prescribed integral
object map; transport along that equality gives the displayed HEq. Every object is an
integral representative, so the component condition uniquely determines the isomorphism. -/
theorem sfRationalScalarComp_existsUnique :
    ∃! a : sfRationalScalarExtension l E Y p hl L ι ⋙
        sfRationalScalarExtension l L Y p hl M j ≅
        sfRationalScalarExtension l E Y p hl M (j.comp ι),
      ∀ K : sfRationalConstructibleCategory l E Y,
        HEq (a.hom.app K)
          ((sfRationalConstructibleLocalization l M Y).map
            ((sfIntegralScalarComp l E L ι Y p hl M j).hom.app K.obj)) := by
  let F₀ := sfConstructibleIntegralScalarExtension p l hl E L ι Y
  let G₀ := sfConstructibleIntegralScalarExtension p l hl L M j Y
  let H₀ := sfConstructibleIntegralScalarExtension p l hl E M (j.comp ι) Y
  let F := sfRationalScalarExtension l E Y p hl L ι
  let G := sfRationalScalarExtension l L Y p hl M j
  let H := sfRationalScalarExtension l E Y p hl M (j.comp ι)
  have hF := (sfRationalScalarExtension_existsUnique l E Y p hl L ι).exists.choose_spec
  have hG := (sfRationalScalarExtension_existsUnique l L Y p hl M j).exists.choose_spec
  have hH := (sfRationalScalarExtension_existsUnique l E Y p hl M
    (j.comp ι)).exists.choose_spec
  let ψ a := (sfRationalCoefficientEquiv l M).symm
    ((j.comp ι) (sfRationalCoefficientEquiv l E a))
  apply localizedIso
    (Padic.coefficientExtensionUniformizer l E) (Padic.coefficientExtensionUniformizer l M)
    ψ (F₀ ⋙ G₀) H₀ (sfIntegralScalarComp l E L ι Y p hl M j) (F ⋙ G) H
  · intro K
    exact (hG.2.1 (F.obj K)).trans
      (congrArg (fun X : sfRationalConstructibleCategory l L Y ↦
        (⟨G₀.obj X.obj⟩ : sfRationalConstructibleCategory l M Y)) (hF.2.1 K))
  · exact hH.2.1
  · intro K K' f a
    have hm := map_heq G (hF.2.1 ⟨K⟩) (hF.2.1 ⟨K'⟩) (hF.2.2 K K' f a)
    have hn := hG.2.2 (F₀.obj K) (F₀.obj K') (F₀.map f)
      ((sfRationalCoefficientEquiv l L).symm (ι (sfRationalCoefficientEquiv l E a)))
    exact hm.trans (by
      simpa only [ψ, AlgEquiv.apply_symm_apply, AlgHom.comp_apply,
        sfRationalConstructibleLocalization, ScalarLocalization.localization,
        sfRationalScalarExtension, F₀, G₀, G, Functor.comp_obj, Functor.comp_map] using hn)
  · exact hH.2.2

/-- Canonical composition for the currently recorded rational scalar extensions.
Source: blueprint order 1828 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def sfRationalScalarComp :
    sfRationalScalarExtension l E Y p hl L ι ⋙ sfRationalScalarExtension l L Y p hl M j ≅
      sfRationalScalarExtension l E Y p hl M (j.comp ι) :=
  (sfRationalScalarComp_existsUnique l E L ι Y p hl M j).exists.choose

/-- The rational unit is the localized normalized integral unit on every object.
Source: blueprint order 1828, proof, identity-extension clause
(blueprint: lem-weil-scalar-extension-composition).
Proof: localize the integral unit and inverse. Integral naturality multiplied by each
coefficient proves rational naturality on pure tensors and hence on every morphism.
The scalar functor's specified object equalities identify the endpoints, giving HEq.
All objects are integral representatives, so this condition proves uniqueness. -/
theorem sfRationalScalarUnit_existsUnique :
    ∃! a : sfRationalScalarExtension l E Y p hl E (AlgHom.id (Padic l) E) ≅
        𝟭 (sfRationalConstructibleCategory l E Y),
      ∀ K : sfRationalConstructibleCategory l E Y,
        HEq (a.hom.app K)
          ((sfRationalConstructibleLocalization l E Y).map
            ((sfIntegralScalarUnit l E Y p hl).hom.app K.obj)) := by
  let F := sfRationalScalarExtension l E Y p hl E (AlgHom.id (Padic l) E)
  let F₀ := sfConstructibleIntegralScalarExtension p l hl E E
    (AlgHom.id (Padic l) E) Y
  have hobj := (sfRationalScalarExtension_existsUnique l E Y p hl E
    (AlgHom.id (Padic l) E)).exists.choose_spec.2.1
  have hmap := (sfRationalScalarExtension_existsUnique l E Y p hl E
    (AlgHom.id (Padic l) E)).exists.choose_spec.2.2
  apply localizedIso
    (Padic.coefficientExtensionUniformizer l E) (Padic.coefficientExtensionUniformizer l E)
    id F₀ (𝟭 _) (sfIntegralScalarUnit l E Y p hl) F (𝟭 _)
    hobj (fun _ ↦ rfl)
  · intro K K' f a
    simpa only [F, F₀, id_eq, AlgHom.id_apply, AlgEquiv.symm_apply_apply,
      sfRationalConstructibleLocalization, ScalarLocalization.localization,
      sfRationalScalarExtension]
      using hmap K K' f a
  · intro K K' f a
    rfl

/-- The rational identity comparison, retaining the completeness-unit normalization.
Source: blueprint order 1828 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def sfRationalScalarUnit :
    sfRationalScalarExtension l E Y p hl E (AlgHom.id (Padic l) E) ≅
      𝟭 (sfRationalConstructibleCategory l E Y) :=
  (sfRationalScalarUnit_existsUnique l E Y p hl).exists.choose

/-- Both identity-extension laws and the pentagon for the canonical intrinsic comparisons.
Source: blueprint order 1828, proof, unit and pentagon clauses
(blueprint: lem-weil-scalar-extension-composition).
Proof: check ordinary sheaf tensor generators. For a source identity, the associator
sends c tensor (b tensor x) to cb tensor x, which equals c tensor (b*x). For a target
identity, it is the multiplication unit at the extended object. Both paths for three
extensions send d tensor (c tensor (b tensor x)) to d*k(c)*k(j(b)) tensor x.
Associativity in the final completed coefficient ring proves equality, and local tensor
generation extends it to sheaves. Derived localization preserves these equations.
Expand the completed comparisons as conjugates by the normalized quotient-completion
maps; naturality moves intermediate comparisons past tensor maps and cancels adjacent
inverse factors, leaving the ordinary equations. Full-subcategory faithfulness and
rationalization preserve them. These arguments also cover identity embeddings and
E=L=M, the zero object, and the empty scheme. -/
theorem sfRationalScalar_coherence :
    (∀ K : sfRationalConstructibleCategory l E Y,
      (sfRationalScalarComp l E E (AlgHom.id (Padic l) E) Y p hl L ι).hom.app K =
        (sfRationalScalarExtension l E Y p hl L ι).map
          ((sfRationalScalarUnit l E Y p hl).hom.app K)) ∧
    (∀ K : sfRationalConstructibleCategory l E Y,
      (sfRationalScalarComp l E L ι Y p hl L (AlgHom.id (Padic l) L)).hom.app K =
        (sfRationalScalarUnit l L Y p hl).hom.app
          ((sfRationalScalarExtension l E Y p hl L ι).obj K)) ∧
    (∀ (N : Type u) [Field N] [Algebra (Padic l) N] [FiniteDimensional (Padic l) N]
      (k : M →ₐ[Padic l] N) (K : sfRationalConstructibleCategory l E Y),
      (sfRationalScalarExtension l M Y p hl N k).map
          ((sfRationalScalarComp l E L ι Y p hl M j).hom.app K) ≫
        (sfRationalScalarComp l E M (j.comp ι) Y p hl N k).hom.app K =
      (sfRationalScalarComp l L M j Y p hl N k).hom.app
          ((sfRationalScalarExtension l E Y p hl L ι).obj K) ≫
        (sfRationalScalarComp l E L ι Y p hl N (k.comp j)).hom.app K) := by
  sorry

end WeilConjectures
