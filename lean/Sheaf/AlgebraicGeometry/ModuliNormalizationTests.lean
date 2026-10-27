/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.AlgebraicGeometry.ModuliChartNormalization
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Scheme tests for open substacks and normality

Source: Stacks, Morphisms of Stacks, representable open immersions and normality;
Tags 0ABP and 038O (blueprint: def-sfb-moduli-normalization-tests).

Density is tested on étale charts, rather than on arbitrary scheme base changes.
Normality is likewise étale local. Scalar extension is expressed by the canonical
integral-closure models on charts, retaining the map from the entire cover.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A dense open substack, with open scheme base changes and density on every étale
scheme chart. Source: Stacks, Morphisms of Stacks, open immersions and dense opens
(blueprint: def-sfb-moduli-normalization-tests). -/
def IsDenseOpenModuliMap {S : Scheme.{u}}
    {U : BasedCategory.{v₁, w₁} (Over S)} {X : BasedCategory.{v₂, w₂} (Over S)}
    (j : BasedFunctor U X) : Prop :=
  ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) X),
    ∃ (W : Over S) (p : W ⟶ T)
        (c : BasedFunctor (discreteModuli (yoneda.obj W)) (moduliTwoFiberProduct t j)),
      IsSchemeModuliBaseChange c p ∧ IsOpenImmersion p.left ∧
        (IsEtaleModuliMap t → DenseRange p.left)

/-- Normality of a DM stack is tested on its étale scheme charts.
Source: Stacks, Properties of Stacks, normality, and Tag 033H
(blueprint: def-sfb-moduli-normalization-tests). -/
def IsNormalModuliStack {S : Scheme.{u}}
    (X : BasedCategory.{v₁, w₁} (Over S)) : Prop :=
  ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) X),
    IsEtaleModuliMap t → ∀ x : T.left,
      IsDomain (T.left.presheaf.stalk x) ∧ IsIntegrallyClosed (T.left.presheaf.stalk x)

/-- Scalar extension of each chart normalization, with both the structural map and
its dominant map from the original cover. The base change is arbitrary, not assumed
étale. Over a field this is the chartwise meaning of formation commuting with scalar
extension. Source: Stacks 038O and 0ABP
(blueprint: def-sfb-moduli-normalization-tests). -/
def ModuliNormalizationScalarCharts {k : Type u} [Field k]
    {V : BasedCategory.{v₁, w₁} (Over (Spec (.of k)))}
    {X : BasedCategory.{v₂, w₂} (Over (Spec (.of k)))}
    (v : BasedFunctor V X) : Prop :=
  ∀ (T : Over (Spec (.of k)))
      (t : BasedFunctor (discreteModuli (yoneda.obj T)) X),
    (∀ x : T.left, IsDomain (T.left.presheaf.stalk x) ∧
      IsIntegrallyClosed (T.left.presheaf.stalk x)) →
    LocallyOfFiniteType T.hom → QuasiCompact T.hom → IsEtaleModuliMap t →
    ∀ (E : Over (Spec (.of k))) (p : E ⟶ T) [QuasiCompact p.left]
      [QuasiSeparated p.left]
      (c : BasedFunctor (discreteModuli (yoneda.obj E)) (moduliTwoFiberProduct t v)),
    IsSchemeModuliBaseChange c p →
    ∀ (k' : Type u) [Field k'] (a : k →+* k'),
    ∀ (T' : Scheme.{u}) (q : T' ⟶ T.left) (r : T' ⟶ Spec (.of k')),
    IsPullback q r T.hom (Spec.map (CommRingCat.ofHom a)) →
    ∃ e : (pullback.snd p.left q).normalization ≅ pullback p.left.fromNormalization q,
      e.hom ≫ pullback.snd p.left.fromNormalization q =
        (pullback.snd p.left q).fromNormalization ∧
      (pullback.snd p.left q).toNormalization ≫ e.hom ≫
          pullback.fst p.left.fromNormalization q =
        pullback.fst p.left q ≫ p.left.toNormalization

end CategoryTheory
