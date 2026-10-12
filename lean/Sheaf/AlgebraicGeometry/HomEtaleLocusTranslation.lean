/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.EtaleAtFieldExtension

/-!
# Translation invariance of the étale locus of a group homomorphism

Source: literature/stacks-project/groupoids.tex, Groupoid Schemes, lemma on etaleness of
multiplication by d, proof using translations (blueprint: lem-sc-hom-etale-locus-translation)
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- For a homomorphism from a nonzero abelian variety, translation by every rational point
preserves the étale locus; hence étaleness is equivalent to étaleness at the identity.
Source: Stacks Project, `groupoids.tex`, proof of
`lemma-abelian-variety-multiplication-by-d-etale` (translation argument).

Proof steps: (1) By `lem-sc-translation-automorphism`, translations by `a` on A and by
`f(a)` on H are isomorphisms, with inverses the translations by their inverses. The
homomorphism identity intertwines these translations. Composing with these étale
isomorphisms in both directions transports étaleness between `x` and `a * x`.
(2) For each point `x`, extend its residue field to an algebraic closure K and lift `x`
to a K-point of the base change. By `lem-sc-etale-base-change-geometric`, étaleness at
`x` is equivalent to étaleness at that lift. Translation by the inverse of the lift
carries it to the identity, so step (1) reduces étaleness there to étaleness at the
identity over K. The same base-change equivalence at the identity returns to k.
Thus every point is étale exactly when the identity is: the locus is empty or all of A,
and locality of étaleness on the source gives the global criterion.
(blueprint: lem-sc-hom-etale-locus-translation) -/
theorem hom_etaleLocus_translation
    (A H : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A] [GrpObj H]
    (f : A ⟶ H) [IsMonHom f]
    (hA : ¬ Nonempty (A ≅ 𝟙_ (Over (Spec (.of k)))))
    (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    Set.image (GrpObj.mulLeft A a).left.base
        {x : A.left | ∃ U : A.left.Opens, x ∈ U ∧ Etale (U.ι ≫ f.left)} =
      {x : A.left | ∃ U : A.left.Opens, x ∈ U ∧ Etale (U.ι ≫ f.left)} ∧
    ({x : A.left | ∃ U : A.left.Opens, x ∈ U ∧ Etale (U.ι ≫ f.left)} = ∅ ∨
      {x : A.left | ∃ U : A.left.Opens, x ∈ U ∧ Etale (U.ι ≫ f.left)} = Set.univ) ∧
    (Etale f.left ↔
      ∃ U : A.left.Opens, GrpObj.onePoint A ∈ U ∧ Etale (U.ι ≫ f.left)) := by
  sorry

end AlgebraicGeometry
