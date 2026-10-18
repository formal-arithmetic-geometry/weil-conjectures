/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Étale-acyclic affine schemes

Source: Hübner–Schmidt, Definition 7.8 and Proposition 7.9, étale case
(blueprint: def-trf-etale-acyclic-scheme).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

/-- A scheme is étale-acyclic when every jointly-surjective family in its small étale site
admits a section of the induced coproduct cover.
Source: Hübner–Schmidt, Definition 7.8 and Proposition 7.9, étale case
(blueprint: def-trf-etale-acyclic-scheme). -/
def AlgebraicGeometry.Scheme.IsEtaleAcyclic (T : Scheme.{u}) : Prop :=
  ∀ (ι : Type u) (U : ι → T.Etale),
    ((⋃ i : ι, Set.range (U i).hom.base) : Set T) = Set.univ →
      ∃ (s : T ⟶ ∐ fun i => (U i).left),
        s ≫ Sigma.desc (fun i => (U i).hom) = 𝟙 T
