/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Sheaf.RingTheory.IndPrincipalZariski

import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Étale, affine pro-étale and weakly étale morphisms

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-def-pe-morphisms/
`det-pe-morphisms-etale-comparison.md` (blueprint: det-pe-morphisms-etale-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The four comparisons of blueprint node det-pe-morphisms-etale-comparison.
Source: `det-pe-morphisms-etale-comparison.md`, clauses 1--4; Stacks Tags 094X,
097N, 025G, 0818, and 01U5 (blueprint: det-pe-morphisms-etale-comparison).

Proof:
1. Mathlib's instance for étale morphisms gives clause 1: the morphism is flat,
   and its open-immersion diagonal is flat.
2. The source library's `Algebra.IndEtale.weaklyEtale` gives both ring flatness
   conditions for an ind-étale algebra. The recorded affine-spectrum comparison
   `weaklyEtale_SpecMap_algebraMap_iff` gives clause 2.
3. For clause 3, `locallyOfFinitePresentation_diagonal` supplies local finite
   presentation of the diagonal. It is a monomorphism and is flat by weak
   étaleness, so `IsOpenImmersion.of_flat_of_mono` makes it an open immersion.
   The open diagonal gives formal unramifiedness. Together with flatness and
   the assumed local finite presentation, `Etale.of_formallyUnramified_of_flat`
   proves étaleness.
4. The source library's `WeaklyEtale.hasRingHomProperty` identifies weak
   étaleness with the affine-local ring property. On each chart, use exactly
   the algebra structure induced by `appLE`. Expanding `Algebra.WeaklyEtale`
   gives module flatness and flatness of tensor multiplication; the equivalence
   `RingHom.flat_algebraMap_iff` changes module flatness to ring-map flatness.
   These conversions in both directions prove clause 4.
-/
theorem etale_indEtale_weaklyEtale_comparison :
    (∀ {U X : Scheme.{u}} (u : U ⟶ X),
      Etale u → WeaklyEtale u) ∧
    (∀ (R B : Type u) [CommRing R] [CommRing B] [Algebra R B],
      Algebra.IndEtale R B →
        WeaklyEtale
          (Spec.map (CommRingCat.ofHom (algebraMap R B)))) ∧
    (∀ {U X : Scheme.{u}} (u : U ⟶ X),
      WeaklyEtale u → LocallyOfFinitePresentation u → Etale u) ∧
    (∀ {U X : Scheme.{u}} (u : U ⟶ X),
      WeaklyEtale u ↔
        ∀ (T : X.Opens) (_hT : IsAffineOpen T) (V : U.Opens) (_hV : IsAffineOpen V)
          (e : V ≤ u ⁻¹ᵁ T),
          (u.appLE T V e).hom.Flat ∧
            (fun (_a : Algebra Γ(X, T) Γ(U, V)) ↦
              RingHom.Flat (Algebra.TensorProduct.lmul' Γ(X, T) (S := Γ(U, V))).toRingHom)
              (u.appLE T V e).hom.toAlgebra) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro U X f hf
    let := hf
    infer_instance
  · intro R B _ _ _ h
    let := h
    exact weaklyEtale_SpecMap_algebraMap_iff.mpr inferInstance
  · intro U X f hf hfp
    let := hf
    let := hfp
    have : IsOpenImmersion (pullback.diagonal f) :=
      IsOpenImmersion.of_flat_of_mono (pullback.diagonal f)
    exact Etale.of_formallyUnramified_of_flat f
  · intro U X f
    rw [HasRingHomProperty.eq_affineLocally @WeaklyEtale,
      affineLocally_iff_forall_isAffineOpen]
    constructor
    · intro h T hT V hV e
      let := (f.appLE T V e).hom.toAlgebra
      have h' := h hT hV e
      change Algebra.WeaklyEtale Γ(X, T) Γ(U, V) at h'
      exact ⟨(RingHom.flat_algebraMap_iff).mpr h'.flat, h'.flat_lmul'⟩
    · intro h T hT V hV e
      let := (f.appLE T V e).hom.toAlgebra
      obtain ⟨hflat, hmul⟩ := h T hT V hV e
      change Algebra.WeaklyEtale Γ(X, T) Γ(U, V)
      exact ⟨(RingHom.flat_algebraMap_iff).mp hflat, hmul⟩

end AlgebraicGeometry
