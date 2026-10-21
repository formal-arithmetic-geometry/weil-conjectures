/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q89
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.FieldTheory.Finite.Basic
import WeilConjectures.AlgebraicGeometry.AbsoluteFrobeniusNatural

/-!
# Unrestricted finite-field Frobenius factorization

Source: main-20261015 blueprint, `def-pur-scheme-geometric-frobenius`, absolute-Frobenius
factorization paragraph and second commuting square; Stacks Tags 03SM, 0CC7 and 01JP
(blueprint: lem-pur-unrestricted-frobenius-factorization).

All models are arbitrary objects of `Over (Spec D.k₀)`. The scalar extension, model
Frobenius, absolute Frobenius, and coefficient actions are the existing constructions,
written explicitly to avoid the finite-type restrictions on `D.geometricFiber` and
`D.relativeFrobenius`. No coefficient datum or finiteness hypothesis is needed.

## Main statements

- `unrestricted_frobenius_projections`: descent of model Frobenius and six projections.
- `unrestricted_frobenius_factorization`: both arithmetic and geometric factorizations
  and both inverse identities.
- `unrestricted_frobenius_naturality`: naturality of model and absolute Frobenius.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.FiniteFieldDatum

/-- The model's absolute q-power Frobenius is over the finite field, and the six
projection identities hold on its unrestricted scalar extension.
Source: Stacks Tags 03SM, 0CC7 and 01JP; main-20261015 blueprint,
`def-pur-scheme-geometric-frobenius`, factorization paragraph
(blueprint: lem-pur-unrestricted-frobenius-factorization).

Proof (node steps 1--4):
1. The structure morphism induces a unital ring map from k₀ to global sections.
The finite-field cardinality p^a implies characteristic p, so p vanishes there;
restriction gives vanishing on every open, including for the empty scheme.
2. For any morphism h between these schemes, its section maps preserve qth powers:
h-sharp(s^q) = h-sharp(s)^q. The underlying maps of absolute Frobenius are identities,
so this proves naturality of absolute q-power Frobenius (Stacks 0CC7).
3. The identity c^q = c in k₀ (lem-weil-finite-field-pow-card) gives identity Frobenius
on Spec k₀. Naturality for T₀ → Spec k₀ proves that model Frobenius is over k₀.
On Spec k its section map is sigma(z) = z^q (def-weil-frobenius-substitution).
Naturality for the two projections gives the two absolute-Frobenius equations.
4. Apply the projection equations of the base-change functor to model Frobenius,
and those of `galoisMap` to sigma. These are the remaining four projection equations.
The pullback exists without finite-type or separatedness assumptions. -/
theorem unrestricted_frobenius_projections (D : WeilConjectures.FiniteFieldDatum.{u})
    (T₀ : Over (Spec (CommRingCat.of D.k₀))) :
    T₀.left.iterateFrobenius D.prime (D.model_characteristic T₀.hom) D.a ≫ T₀.hom = T₀.hom ∧
    (pullback T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).iterateFrobenius
    D.prime (D.model_characteristic (pullback.fst T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap
    D.k₀ D.k))) ≫ T₀.hom)) D.a ≫ pullback.fst T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀
    D.k))) = pullback.fst T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫
    T₀.left.iterateFrobenius D.prime (D.model_characteristic T₀.hom) D.a ∧ (pullback T₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).iterateFrobenius D.prime
    (D.model_characteristic (pullback.fst T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀
    D.k))) ≫ T₀.hom)) D.a ≫ pullback.snd T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀
    D.k))) = pullback.snd T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫ Spec.map
    (CommRingCat.ofHom (@FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ _ (Fintype.ofFinite D.k₀)
    D.k _ _ _).toRingHom) ∧ ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀
    D.k)))).map (Over.homMk (T₀.left.iterateFrobenius D.prime (D.model_characteristic T₀.hom) D.a)
    (D.model_frobenius_over T₀.hom))).left ≫ pullback.fst T₀.hom (Spec.map (CommRingCat.ofHom
    (algebraMap D.k₀ D.k))) = pullback.fst T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀
    D.k))) ≫ T₀.left.iterateFrobenius D.prime (D.model_characteristic T₀.hom) D.a ∧
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map (Over.homMk
    (T₀.left.iterateFrobenius D.prime (D.model_characteristic T₀.hom) D.a) (D.model_frobenius_over
    T₀.hom))).left ≫ pullback.snd T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
    pullback.snd T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ∧ D.galoisMap T₀.hom
    (@FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ _ (Fintype.ofFinite D.k₀) D.k _ _ _) ≫
    pullback.fst T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) = pullback.fst T₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ∧ D.galoisMap T₀.hom
    (@FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ _ (Fintype.ofFinite D.k₀) D.k _ _ _) ≫
    pullback.snd T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) = pullback.snd T₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫ Spec.map (CommRingCat.ofHom
    (@FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ _ (Fintype.ofFinite D.k₀) D.k _ _
    _).toRingHom) := by
  classical
  let := Fintype.ofFinite D.k₀
  let b := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  let π := pullback.fst T₀.hom b
  let ρ := pullback.snd T₀.hom b
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ D.k
  have hFₖ : (Spec (CommRingCat.of D.k)).iterateFrobenius D.prime
      (D.model_characteristic b) D.a = Spec.map (CommRingCat.ofHom σ.toRingHom) := by
    apply AlgebraicGeometry.ext_to_Spec
    change (Scheme.ΓSpecIso (CommRingCat.of D.k)).inv ≫
        ((Spec (CommRingCat.of D.k)).iterateFrobenius D.prime
          (D.model_characteristic b) D.a).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of D.k)).inv ≫
        (Spec.map (CommRingCat.ofHom σ.toRingHom)).appTop
    rw [← Scheme.ΓSpecIso_inv_naturality]
    ext x
    change ((Scheme.ΓSpecIso (CommRingCat.of D.k)).inv x) ^ D.p ^ D.a =
      (Scheme.ΓSpecIso (CommRingCat.of D.k)).inv (σ x)
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ← map_pow,
      ← Nat.card_eq_fintype_card, D.card_base, D.cardinality_eq]
  refine ⟨D.model_frobenius_over T₀.hom, ?_, ?_, ?_, ?_,
    (D.galoisMap_projections T₀.hom σ).1,
    (D.galoisMap_projections T₀.hom σ).2⟩
  · exact (Scheme.comp_iterateFrobenius D.prime π (D.model_characteristic T₀.hom)
      (D.model_characteristic (π ≫ T₀.hom)) D.a).symm
  · change _ ≫ ρ = ρ ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)
    rw [← hFₖ]
    exact (Scheme.comp_iterateFrobenius D.prime ρ (D.model_characteristic b)
      (D.model_characteristic (π ≫ T₀.hom)) D.a).symm
  · simp [Over.pullback_map_left]
  · exact ((Over.pullback b).map (Over.homMk
      (T₀.left.iterateFrobenius D.prime (D.model_characteristic T₀.hom) D.a)
      (D.model_frobenius_over T₀.hom))).w

/-- Absolute q-power Frobenius is the commuting composite of model Frobenius
and arithmetic coefficient Frobenius. Geometric coefficient Frobenius cancels it
on either side, and the arithmetic and geometric coefficient maps are mutual inverses.
Source: main-20261015 blueprint, `def-pur-scheme-geometric-frobenius`,
absolute-Frobenius factorization paragraph; Stacks Tags 03SM, 0CC7 and 01JP
(blueprint: lem-pur-unrestricted-frobenius-factorization).

Proof (node steps 1--7): inherit characteristic p and compute the six projections
as in `unrestricted_frobenius_projections` (steps 1--4). Both orders of the composite
of model and arithmetic coefficient Frobenius have first projection F₀ after pi
and second projection Spec(sigma) after rho. Those are also the projections of
absolute Frobenius. Pullback uniqueness gives both arithmetic factorizations
(step 5, def-pc-fibre-product). The coefficient actions at sigma and gamma have
inverse composites: their first projections are pi, and their second projections
are rho since gamma = sigma inverse and Spec is contravariant. Pullback uniqueness
therefore gives both inverse identities (step 6, def-weil-affine-spectrum and
def-weil-frobenius-substitution). Compose the two arithmetic factorizations with
the appropriate inverse coefficient map; associativity and cancellation give
both geometric factorizations (step 7). -/
theorem unrestricted_frobenius_factorization (D : WeilConjectures.FiniteFieldDatum.{u})
    (T₀ : Over (Spec (CommRingCat.of D.k₀))) :
    (pullback T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).iterateFrobenius
    D.prime (D.model_characteristic (pullback.fst T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap
    D.k₀ D.k))) ≫ T₀.hom)) D.a = ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀
    D.k)))).map (Over.homMk (T₀.left.iterateFrobenius D.prime (D.model_characteristic T₀.hom) D.a)
    (D.model_frobenius_over T₀.hom))).left ≫ D.galoisMap T₀.hom
    (@FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ _ (Fintype.ofFinite D.k₀) D.k _ _ _) ∧
    (pullback T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).iterateFrobenius
    D.prime (D.model_characteristic (pullback.fst T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap
    D.k₀ D.k))) ≫ T₀.hom)) D.a = D.galoisMap T₀.hom (@FiniteField.frobeniusAlgEquivOfAlgebraic
    D.k₀ _ (Fintype.ofFinite D.k₀) D.k _ _ _) ≫ ((Over.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap D.k₀ D.k)))).map (Over.homMk (T₀.left.iterateFrobenius D.prime
    (D.model_characteristic T₀.hom) D.a) (D.model_frobenius_over T₀.hom))).left ∧ ((Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map (Over.homMk
    (T₀.left.iterateFrobenius D.prime (D.model_characteristic T₀.hom) D.a) (D.model_frobenius_over
    T₀.hom))).left = (pullback T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀
    D.k)))).iterateFrobenius D.prime (D.model_characteristic (pullback.fst T₀.hom (Spec.map
    (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫ T₀.hom)) D.a ≫ D.galoisMap T₀.hom
    (@FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ _ (Fintype.ofFinite D.k₀) D.k _ _ _).symm ∧
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map (Over.homMk
    (T₀.left.iterateFrobenius D.prime (D.model_characteristic T₀.hom) D.a) (D.model_frobenius_over
    T₀.hom))).left = D.galoisMap T₀.hom (@FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ _
    (Fintype.ofFinite D.k₀) D.k _ _ _).symm ≫ (pullback T₀.hom (Spec.map (CommRingCat.ofHom
    (algebraMap D.k₀ D.k)))).iterateFrobenius D.prime (D.model_characteristic (pullback.fst T₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫ T₀.hom)) D.a ∧ D.galoisMap T₀.hom
    (@FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ _ (Fintype.ofFinite D.k₀) D.k _ _ _).symm ≫
    D.galoisMap T₀.hom (@FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ _ (Fintype.ofFinite D.k₀)
    D.k _ _ _) = 𝟙 (pullback T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) ∧
    D.galoisMap T₀.hom (@FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ _ (Fintype.ofFinite D.k₀)
    D.k _ _ _) ≫ D.galoisMap T₀.hom (@FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ _
    (Fintype.ofFinite D.k₀) D.k _ _ _).symm = 𝟙 (pullback T₀.hom (Spec.map (CommRingCat.ofHom
    (algebraMap D.k₀ D.k)))) := by
  classical
  let := Fintype.ofFinite D.k₀
  let b := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  let T := pullback T₀.hom b
  let π := pullback.fst T₀.hom b
  let ρ := pullback.snd T₀.hom b
  let F := T.iterateFrobenius D.prime (D.model_characteristic (π ≫ T₀.hom)) D.a
  let P : T ⟶ T := ((Over.pullback b).map (Over.homMk
    (T₀.left.iterateFrobenius D.prime (D.model_characteristic T₀.hom) D.a)
    (D.model_frobenius_over T₀.hom))).left
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ D.k
  let S := D.galoisMap T₀.hom σ
  let G := D.galoisMap T₀.hom σ.symm
  obtain ⟨_, hF₁, hF₂, hP₁, hP₂, hS₁, hS₂⟩ :=
    D.unrestricted_frobenius_projections T₀
  have hPS : F = P ≫ S := by
    apply pullback.hom_ext
    · rw [Category.assoc, hS₁, hP₁, hF₁]
    · rw [Category.assoc, hS₂, ← Category.assoc, hP₂, hF₂]
  have hSP : F = S ≫ P := by
    apply pullback.hom_ext
    · rw [Category.assoc, hP₁, ← Category.assoc, hS₁, hF₁]
    · rw [Category.assoc, hP₂, hS₂, hF₂]
  have hSG : S ≫ G = 𝟙 T := (D.galoisMap_inverse T₀.hom σ).1
  have hGS : G ≫ S = 𝟙 T := (D.galoisMap_inverse T₀.hom σ).2
  change F = P ≫ S ∧ F = S ≫ P ∧ P = F ≫ G ∧ P = G ≫ F ∧
    G ≫ S = 𝟙 T ∧ S ≫ G = 𝟙 T
  refine ⟨hPS, hSP, ?_, ?_, hGS, hSG⟩
  · rw [hPS, Category.assoc, hSG, Category.comp_id]
  · rw [hSP, ← Category.assoc, hGS, Category.id_comp]

/-- For every morphism of arbitrary finite-field models, its scalar extension
commutes with the base-changed model Frobenius and with absolute q-power Frobenius.
Source: main-20261015 blueprint, `def-pur-scheme-geometric-frobenius`,
second commuting square; Stacks Tags 0CC7 and 01JP
(blueprint: lem-pur-unrestricted-frobenius-factorization).

Proof (node steps 1, 2 and 8): all schemes have characteristic p by their structure
maps (step 1). Section maps preserve qth powers, proving absolute-Frobenius
naturality for f₀ and for its scalar extension (step 2). For model Frobenius,
compose the two proposed maps with the model projection: the base-change projection
identity and naturality for f₀ make them equal. Their coefficient projections are
both the coefficient projection of X. Pullback uniqueness gives the first equality
(step 8, def-pc-base-change and def-pc-fibre-product). Apply absolute-Frobenius
naturality directly to the scalar extension for the second equality. -/
theorem unrestricted_frobenius_naturality (D : WeilConjectures.FiniteFieldDatum.{u})
    {X₀ Y₀ : Over (Spec (CommRingCat.of D.k₀))} (f₀ : X₀ ⟶ Y₀) :
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map (Over.homMk
    (X₀.left.iterateFrobenius D.prime (D.model_characteristic X₀.hom) D.a) (D.model_frobenius_over
    X₀.hom))).left ≫ ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map
    f₀).left = ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left
    ≫ ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map (Over.homMk
    (Y₀.left.iterateFrobenius D.prime (D.model_characteristic Y₀.hom) D.a) (D.model_frobenius_over
    Y₀.hom))).left ∧ (pullback X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀
    D.k)))).iterateFrobenius D.prime (D.model_characteristic (pullback.fst X₀.hom (Spec.map
    (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫ X₀.hom)) D.a ≫ ((Over.pullback (Spec.map
    (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left = ((Over.pullback (Spec.map
    (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left ≫ (pullback Y₀.hom (Spec.map
    (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).iterateFrobenius D.prime (D.model_characteristic
    (pullback.fst Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫ Y₀.hom)) D.a := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  let F₀ (T₀ : Over (Spec (CommRingCat.of D.k₀))) : T₀ ⟶ T₀ :=
    Over.homMk (T₀.left.iterateFrobenius D.prime (D.model_characteristic T₀.hom) D.a)
      (D.model_frobenius_over T₀.hom)
  have hnat : F₀ X₀ ≫ f₀ = f₀ ≫ F₀ Y₀ := by
    apply Over.OverMorphism.ext
    exact (Scheme.comp_iterateFrobenius D.prime f₀.left
      (D.model_characteristic Y₀.hom) (D.model_characteristic X₀.hom) D.a).symm
  constructor
  · have hmap : (Over.pullback b).map (F₀ X₀) ≫ (Over.pullback b).map f₀ =
        (Over.pullback b).map f₀ ≫ (Over.pullback b).map (F₀ Y₀) := by
      simpa only [Functor.map_comp] using congrArg ((Over.pullback b).map) hnat
    exact congrArg (fun f : (Over.pullback b).obj X₀ ⟶
      (Over.pullback b).obj Y₀ ↦ f.left) hmap
  · exact (Scheme.comp_iterateFrobenius D.prime ((Over.pullback b).map f₀).left
      (D.model_characteristic (pullback.fst Y₀.hom b ≫ Y₀.hom))
      (D.model_characteristic (pullback.fst X₀.hom b ≫ X₀.hom)) D.a).symm

end WeilConjectures.FiniteFieldDatum
