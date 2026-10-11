/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints
import Sheaf.AlgebraicGeometry.InvertibleGeneratingSectionsFibre

/-!
# Morphisms into projective space from generating sections

Source: Stacks Project, Constructions, Lemma 01NE, Definition 01NF and its following paragraph
(blueprint: def-weil-pbc-morphism-to-projective-space-by-sections).

The integral projective space used by the functor-of-points declaration is the base change
of the raw integral Proj to `Spec ℤ`. Its second projection identifies it with that Proj.
Thus the second component of the defining pairing below is `ψ ≫ toProjInt`.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.ProjectiveSpace

variable (I : Type u) [Finite I] {Y S : Scheme.{u}}

/-- The integral morphism attached to an invertible module and generating sections exists
uniquely, including for an arbitrary finite coordinate set.

Source: Stacks Project, Constructions, Lemma 01NE
(blueprint: def-weil-pbc-morphism-to-projective-space-by-sections).

Proof: For `I = ULift (Fin (n+1))`, use
`Scheme.Modules.invertible_generating_sections_fibre_criterion` to turn the epimorphism
hypothesis into nonvanishing at every point. Apply the second clause of
`AlgebraicGeometry.projectiveSpace_functor_of_points` to the sections evaluated at the top
open. For a nonempty finite `I`, enumerate its elements by `Fin (card I)` and reindex the
polynomial variables, the twisting sheaf, and its coordinate sections along that bijection;
this transports the same unique classification. If `I` is empty, generation forces every
stalk to be zero; invertibility then forces `Y` to be empty. Both integral projective space
and `Y` are empty, so the unique morphism and the unique module isomorphism give the claim.
The identification of the base-changed integral model with raw Proj is the second
projection of the pullback over the terminal scheme. -/
theorem generatingSections_integralHom_exists (L : Y.Modules) [L.IsInvertible]
    (s : I → L.sections) (hs : Epi (L.freeHomEquiv.symm s)) :
    ∃! ψ : Y ⟶ ℙ(I; Spec (CommRingCat.of (ULift.{u} ℤ))),
      ∃ e : (Scheme.Modules.tensorPullback ψ).obj
          (twist I (Spec (CommRingCat.of (ULift.{u} ℤ))) 1) ≅ L,
        ∀ i : I, e.hom.app ⊤ (((Classical.choose
          (Scheme.Modules.exists_tensorPullbackAdjunction ψ)).unit.app
            (twist I (Spec (CommRingCat.of (ULift.{u} ℤ))) 1)).val.app (Opposite.op ⊤)
              (twistOneSection I (Spec (CommRingCat.of (ULift.{u} ℤ))) i)) =
          (s i).val (Opposite.op ⊤) := by
  sorry

/-- The morphism `ψ` into integral projective space classified by the given pair.
Source: Stacks Project, Constructions, Lemma 01NE
(blueprint: def-weil-pbc-morphism-to-projective-space-by-sections). -/
noncomputable def integralHomOfGeneratingSections (L : Y.Modules) [L.IsInvertible]
    (s : I → L.sections) (hs : Epi (L.freeHomEquiv.symm s)) :
    Y ⟶ ℙ(I; Spec (CommRingCat.of (ULift.{u} ℤ))) :=
  Classical.choose (generatingSections_integralHom_exists I L s hs)

/-- Pair `g` with the integral morphism classified by `(L,s)` using the universal property
of the fibre product. No trivialization of `L` is an additional input.
Source: Stacks Project, Constructions, Definition 01NF, paragraph following it
(blueprint: def-weil-pbc-morphism-to-projective-space-by-sections). -/
noncomputable def homOfGeneratingSections (g : Y ⟶ S) (L : Y.Modules) [L.IsInvertible]
    (s : I → L.sections) (hs : Epi (L.freeHomEquiv.symm s)) : Y ⟶ ℙ(I; S) :=
  pullback.lift g
    (integralHomOfGeneratingSections I L s hs ≫
      toProjInt I (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (terminal.hom_ext _ _)

/-- The selected integral morphism pulls the universal pair back to `(L,s)`.
Source: Stacks Project, Constructions, Lemma 01NE
(blueprint: def-weil-pbc-morphism-to-projective-space-by-sections).
Proof: The existence part of `Classical.choose_spec` for
`generatingSections_integralHom_exists` is exactly the required section-preserving
isomorphism. -/
theorem integralHomOfGeneratingSections_spec (L : Y.Modules) [L.IsInvertible]
    (s : I → L.sections) (hs : Epi (L.freeHomEquiv.symm s)) :
    ∃ e : (Scheme.Modules.tensorPullback (integralHomOfGeneratingSections I L s hs)).obj
        (twist I (Spec (CommRingCat.of (ULift.{u} ℤ))) 1) ≅ L,
      ∀ i : I, e.hom.app ⊤ (((Classical.choose
          (Scheme.Modules.exists_tensorPullbackAdjunction
            (integralHomOfGeneratingSections I L s hs))).unit.app
              (twist I (Spec (CommRingCat.of (ULift.{u} ℤ))) 1)).val.app (Opposite.op ⊤)
                (twistOneSection I (Spec (CommRingCat.of (ULift.{u} ℤ))) i)) =
        (s i).val (Opposite.op ⊤) := by
  sorry

/-- The two projection identities and uniqueness characterize the coordinate morphism;
the first identity says precisely that it is a morphism over `S`.
Source: Stacks Project, Constructions, Definition 01NF, paragraph following it
(blueprint: def-weil-pbc-morphism-to-projective-space-by-sections).
Proof: Unfold the defining pairing and apply `pullback.lift_fst` and
`pullback.lift_snd`. For any other `χ` with those projection identities,
`pullback.hom_ext` gives its equality with the pairing. Equality of the composites into
the terminal scheme, needed for the lift, is `terminal.hom_ext` (Spec ℤ is terminal). -/
theorem homOfGeneratingSections_spec (g : Y ⟶ S) (L : Y.Modules) [L.IsInvertible]
    (s : I → L.sections) (hs : Epi (L.freeHomEquiv.symm s)) :
    homOfGeneratingSections I g L s hs ≫ ℙ(I; S) ↘ S = g ∧
    homOfGeneratingSections I g L s hs ≫ toProjInt I S =
      integralHomOfGeneratingSections I L s hs ≫
        toProjInt I (Spec (CommRingCat.of (ULift.{u} ℤ))) ∧
    ∀ χ : Y ⟶ ℙ(I; S), χ ≫ ℙ(I; S) ↘ S = g →
      χ ≫ toProjInt I S = integralHomOfGeneratingSections I L s hs ≫
        toProjInt I (Spec (CommRingCat.of (ULift.{u} ℤ))) →
      χ = homOfGeneratingSections I g L s hs := by
  sorry

end AlgebraicGeometry.ProjectiveSpace
