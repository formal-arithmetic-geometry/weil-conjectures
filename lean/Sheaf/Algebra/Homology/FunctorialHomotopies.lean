/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Functorial quasi-isomorphisms killing maps from a set of acyclic complexes

Source: Stacks Project, `injectives.tex`, Lemma `lemma-functorial-homotopies`
(blueprint: lem-pur-kinjective-functorial-homotopies).
-/

@[expose] public section

universe v u

open CategoryTheory

namespace CochainComplex

/-- In a Grothendieck abelian category, a set of acyclic complexes admits a functorial
termwise monomorphic quasi-isomorphism killing all maps from those complexes up to homotopy.
Source: Stacks Project, `injectives.tex`, Lemma `lemma-functorial-homotopies`
(blueprint: lem-pur-kinjective-functorial-homotopies).

Proof:
1. For each `K i`, use its inclusion into the cone on its identity. The inclusion is
termwise monic, and the cone is contractible by `lem-pur-kinjective-cone-contractible`.
Its identity and zero map induce the same cohomology map by
`lem-weil-pbc-homotopic-maps-equal-cohomology`, so the cone is acyclic, and the inclusion
is homotopic to zero.
2. For each complex `M`, take the coproduct over pairs `(i, w)` with `w : K i ⟶ M`, and
push out the coproduct of the cone inclusions along the coproduct of the maps `w`.
Small colimits exist by `def-sp-grothendieck-abelian`. The universal property sends the
summand for `w` to that for its composite with any map `M ⟶ M'`, giving the endofunctor
and its natural transformation from the identity.
3. Degreewise, the pushout is the cokernel of the signed map from the coproduct of the
`K i` to the coproduct of their cones and `M`. The cone inclusions are monic, so the map
from `M` is monic. Its cokernel is the coproduct of the cokernels of the cone inclusions.
Each such cokernel is acyclic by `lem-weil-pbc-complex-ses-homology-long-exact`.
Coproducts are exact: they are filtered colimits of finite coproducts, and filtered
colimits are exact in a Grothendieck abelian category. Thus the cokernel of the map from
`M` is acyclic. The same long exact cohomology sequence shows that this map is a
quasi-isomorphism, as defined in `def-pc-quasi-iso-modules`. The pushout relation factors
its composite with every `w` through the corresponding cone inclusion; compose that
inclusion's null-homotopy with the map from the cone to the pushout. -/
theorem exists_functorial_homotopies {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{v} A] {I : Type v} (K : I → CochainComplex A ℤ)
    (hK : ∀ i : I, (K i).Acyclic) :
    ∃ (F : CochainComplex A ℤ ⥤ CochainComplex A ℤ)
      (j : 𝟭 (CochainComplex A ℤ) ⟶ F),
      (∀ M : CochainComplex A ℤ,
        (∀ n : ℤ, Mono ((j.app M).f n)) ∧ QuasiIso (j.app M)) ∧
      (∀ (M : CochainComplex A ℤ) (i : I) (w : K i ⟶ M),
        Nonempty (Homotopy (w ≫ j.app M) 0)) := by
  sorry

end CochainComplex
