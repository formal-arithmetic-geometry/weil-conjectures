/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.AlgebraicGeometry.EtaleKFlatSupportRows

/-!
# K-flat comparison of actual ordinary etale support sequences

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Locality, expanded by the agent-written
support diagram; Stacks Tags 03DB, 03ER, 06YU, 07A4, 0FPI, 0152 and 014A
(blueprint: lem-pur-etale-kflat-support-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] HomologicalComplex.monoidalCategoryStruct CategoryTheory.catToReflQuiver
universe u uC vC uD vD w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.KFlatSupportComparison


attribute [local instance 20000] sheafBraidedCategory
attribute [local irreducible] Sheaf.monoidalCategory

variable {A B : Type (u + 1)} [CommRing A] [CommRing B]
  {Z P U : Scheme.{u}}


/-- The unique natural tensor/support diagram and its invertible localized middle map.
Source: Stacks Tags 093X, 012Z, 0152, 014A; the strict diagram argument of
lem-pur-etale-kflat-support-comparison
(blueprint: lem-pur-etale-kflat-support-strict).

Proof: the injective support-sequence theorem supplies the two actual short exact rows
and K-injectivity after open pullback. Identify each actual support row with the kernel
sequence of its restriction map. The flat-support chain diagram gives the right square,
the summand formula for its right map, and degreewise exactness of the tensor kernel
sequence. Transport along the kernel identifications to get the actual tensor row.
Lift its left arrow followed by eta through the bottom kernel. The right square gives
its vanishing composite. Cancellation of the bottom monomorphism proves uniqueness.
Naturality of eta and of the chain diagram gives equality of the middle and right
components; cancel the same monomorphism for the first component. The middle component becomes
invertible after localization because eta is a quasi-isomorphism. Empty open or closed
strata, zero complexes, and unbounded flat Q require
no separate assumptions: kernel exactness and the degreewise direct sums still apply. -/
theorem support_comparison_strict [Finite A]
    (i : Z ⟶ P) [IsClosedImmersion i]
    (j : U ⟶ P) [IsOpenImmersion j] (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (I : Complex A P) [I.IsKInjective] [∀ n : ℤ, Injective (I.X n)]
    (Q : Complex A P) (_hQf : ∀ n : ℤ, ObjectProperty.flat (Q.X n))
    (F : Complex A P ⥤ Complex A P) (η : 𝟭 _ ⟶ F)
    [∀ K : Complex A P, (F.obj K).IsKInjective]
    [∀ (K : Complex A P) (n : ℤ), Injective ((F.obj K).X n)]
    [∀ K : Complex A P, QuasiIso (η.app K)] :
    let S := (topSequenceFamily A i j hij Q).obj I
    let N := Q ⊗ I
    let J := F.obj N
    let a := η.app N
    let S' := (bottomSequenceFamily A i j hij Q F).obj I
    let v := OpenSupport.rightMap
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j)
      Q I (F.obj (Q ⊗ I)) (η.app (Q ⊗ I))
    ∃ (hI : CochainComplex.IsKInjective ((pullComplex A j).obj I))
      (hJ : CochainComplex.IsKInjective ((pullComplex A j).obj (F.obj (Q ⊗ I))))
      (hTop : S.ShortExact) (hBottom : S'.ShortExact) (m : S ⟶ S'),
      HEq m.τ₂ a ∧ HEq m.τ₃ v ∧
      (∀ m' : S ⟶ S', HEq m'.τ₂ a → HEq m'.τ₃ v → m' = m) ∧
      IsIso ((localize A P).map m.τ₂) ∧
      DiagramNatural (topSequenceFamily A i j hij Q)
        (bottomSequenceFamily A i j hij Q F) (IsComparison A i j hij Q F η) I m := by
  sorry


end AlgebraicGeometry.Etale.KFlatSupportComparison
