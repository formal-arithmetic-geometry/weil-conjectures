/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.FieldTheory.Separable

/-!
# Etale coproducts of spectra of finite separable field extensions

Source: Stacks Project, Morphisms, Lemma 02GL (blueprint: lem-exc-etale-coproduct-etale).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For a field `K` and any family of finite separable field extensions `L i / K`, the
canonical map from their coproduct of spectra to `Spec K` is etale. The coproduct and its
open, disjoint, covering inclusions are given by Schemes, Lemma 01JB. Each component map is
etale by the finite separable case of Morphisms, Lemma 02GL. Etaleness is local on the source
by Morphisms, Lemma 02GJ, so the coproduct map is etale. This includes an empty or singleton
index type (blueprint: lem-exc-etale-coproduct-etale). -/
theorem etale_sigmaDesc_spec_of_finite_separable
    (K : Type u) [Field K] (I : Type u) (L : I → Type u)
    [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
    [∀ i, Module.Finite K (L i)] [∀ i, Algebra.IsSeparable K (L i)] :
    Etale (Sigma.desc (fun i : I =>
      Spec.map (CommRingCat.ofHom (algebraMap K (L i))))) := by
  sorry

end AlgebraicGeometry
